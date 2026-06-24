module

public import Validator.StateSetFormalism.Formula

namespace Validator.Formula.Clause

public def IsHorn {n} (γ : Clause n) : Prop :=
  γ.countP Literal.isPos ≤ 1
  deriving Decidable

-- M.models ∩ γ.models = M.models ∩ γ'.models
def propagate_assignment {n} (M : PartialModel n) : Clause n → Option (Clause n)
  | [] => some []
  | l :: γ =>
    if l ∈ M then
      none
    else if l.negate ∈ M then
      propagate_assignment M γ
    else do
      let γ' ← propagate_assignment M γ
      return l :: γ'

lemma propagate_assignment_eq_none {n M} {γ : Clause n} :
    γ.propagate_assignment M = none → M.models ⊆ γ.models  := by
  fun_induction propagate_assignment
  case _ =>
    simp only [reduceCtorEq, models_nil, Set.subset_empty_iff, IsEmpty.forall_iff]
  case _ l γ h1 =>
    simp_all [Set.subset_def, mem_models, PartialModel.mem_models]
  case _ l γ h1 h2 h3 =>
    simp_all [Set.subset_def, mem_models]
  case _ l γ h1 h2 h3 =>
    simp_all only [Set.subset_def, mem_models, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_none_iff, reduceCtorEq, imp_false, List.mem_cons, exists_eq_or_imp]
    cases h4 : propagate_assignment M γ
    · grind
    · simp

lemma IsHorn_propagate_assignment {n} {γ γ' : Clause n} {M} :
    γ.propagate_assignment M = some γ' → γ.IsHorn → γ'.IsHorn := by
  intro h1
  suffices h : γ'.countP Literal.isPos ≤ γ.countP Literal.isPos by
    grind only [Clause.IsHorn]
  fun_induction propagate_assignment generalizing γ'
  case _ => grind only
  case _ l γ h1 => simp only [reduceCtorEq] at h1
  case _ l γ h1 h2 h3 => grind only [= List.countP_cons]
  case _ l γ h1 h2 h3 =>
    cases h4 : propagate_assignment M γ
    · grind
    · grind

lemma mem_propagate_assignment {n} {γ γ' : Clause n} {M} :
    γ.propagate_assignment M = some γ' → ∀ l, l ∈ γ' ↔ l ∈ γ ∧ l.negate ∉ M := by
  fun_induction propagate_assignment generalizing γ'
  case _ => grind
  case _ l γ h1 => simp only [reduceCtorEq, IsEmpty.forall_iff]
  case _ l' γ h1 h2 h3 => grind only [= List.mem_cons]
  case _ l γ h1 h2 h3 =>
    cases h4 : propagate_assignment M γ
    · grind
    · grind

-- TODO : write in terms of mem_propagate_assignment?
lemma mem_propagate_assignment' {n} {γ γ' : Clause n} {M} :
    γ.propagate_assignment M = some γ' → ∀ l, l ∈ γ' ↔ l ∈ γ ∧ l ∉ M ∧ l.negate ∉ M := by
  fun_induction propagate_assignment generalizing γ'
  case _ => grind
  case _ l γ h1 => simp only [reduceCtorEq, IsEmpty.forall_iff]
  case _ l' γ h1 h2 h3 => grind only [= List.mem_cons]
  case _ l γ h1 h2 h3 =>
    cases h4 : propagate_assignment M γ
    · grind
    · grind

@[simp]
lemma mem_vars_propagate_assignment {n} {γ γ' : Clause n} {M} :
    γ.propagate_assignment M = some γ' → ∀ i, i ∈ γ'.vars ↔ i ∈ γ.vars ∧ ∀ l ∈ M, ¬l.1 = i := by
  intro h1 i
  simp only [mem_vars, mem_propagate_assignment' h1]
  constructor
  · rintro ⟨l, h2, rfl⟩
    grind only [Literal.eq_or_eq_negate_iff_var_eq]
  · rintro ⟨⟨l, h2, rfl⟩, h3⟩
    grind only [Literal.eq_or_eq_negate_iff_var_eq]

lemma mem_models_propagate_assignment {n} {γ γ' : Clause n} {M} :
    γ.propagate_assignment M = some γ' → ∀ M' ∈ M.models, M' ∈ γ'.models ↔ M' ∈ γ.models := by
  intro h1 M' hM'
  simp only [mem_models, mem_propagate_assignment h1]
  constructor
  · grind
  · rintro ⟨l, hl, h2⟩
    use l
    simp_all only [true_and, and_true]
    intro h3
    apply PartialModel.subset_models_of_mem at h3
    specialize h3 hM'
    simp_all only [Literal.models_negate, Set.mem_compl_iff, not_true_eq_false]

end Clause

namespace CNF

-- write in terms of filterMap?
def propagate_literal {n} (φ : CNF n) (l : Literal n) : CNF n :=
  (φ.filter fun γ ↦ not (γ.contains l)).map (List.filter (· ≠ l.negate))

lemma length_propagate_literal {n} {φ : CNF n} {l} : (φ.propagate_literal l).length ≤ φ.length := by
  simp only [propagate_literal, List.length_map]
  apply List.length_filter_le

lemma IsHorn_propagate_literal {n} {φ : CNF n} {l} :
    (∀ γ ∈ φ, γ.IsHorn) → ∀ γ ∈ φ.propagate_literal l, γ.IsHorn := by
  simp only [Clause.IsHorn, List.countP_eq_length_filter, propagate_literal, List.mem_map,
    List.mem_filter, forall_exists_index, and_imp]
  intro h1 γ' γ hγ h3 rfl
  rw [List.filter_comm]
  grind only [List.length_filter_le]

@[simp]
lemma mem_propagate_literal {n} {φ : CNF n} {l γ} :
    γ ∈ (φ.propagate_literal l) ↔ ∃ γ' ∈ φ, l ∉ γ' ∧ γ = γ'.filter (· ≠ l.negate) := by
  simp [propagate_literal]
  grind

lemma mem_models_propagate_literal {n} {φ : CNF n} {l} :
    ∀ M ∈ l.models, M ∈ (φ.propagate_literal l).models ↔ M ∈ φ.models := by
  intro M hM
  simp only [propagate_literal, ne_eq, decide_not, List.contains_eq_mem, mem_models, List.mem_map,
    List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    forall_exists_index, and_imp, Clause.mem_models]
  constructor
  · grind
  · intro h1 γ' γ hγ hl rfl
    simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    specialize h1 γ hγ
    rcases h1 with ⟨l', hl', h2⟩
    have : l' ≠ l.negate := by
      rintro rfl
      simp_all
    grind

end Formula.CNF
open Formula

-- Enforce that unit_literals does not contain a literal and its negation?
public structure Horn n where

  private vars : VarSet n

  private empty : Bool

  private unit_literals : PartialModel n

  private clauses : CNF n

  private horn_prop : ∀ γ ∈ clauses, γ.IsHorn

  private clauses_prop : ∀ γ ∈ clauses, 2 ≤ γ.length

  private subset_vars : ∀ i ∈ unit_literals.vars ∪ clauses.vars, i ∈ vars

  private vars_prop : unit_literals.vars ∩ clauses.vars = ∅

  deriving DecidableEq, Repr

namespace Horn

def toCNF {n} (φ : Horn n) : CNF n :=
  if φ.empty then
    [[]]
  else
    φ.unit_literals.toCNF ++ φ.clauses

def models {n} (φ : Horn n) : Models n := φ.toCNF.models

lemma models_eq {n} {φ : Horn n} :
    φ.models = if φ.empty then ∅ else φ.unit_literals.models ∩ φ.clauses.models := by
  simp only [models, toCNF]
  split
  · simp
  · simp only [CNF.models_append, PartialModel.models_toCNF]

@[simps]
def top {n} : Horn n where
  vars := ∅
  empty := false
  unit_literals := PartialModel.empty
  clauses := []
  horn_prop := by simp
  clauses_prop := by simp
  subset_vars := by simp [CNF.mem_vars]
  vars_prop := by simp only [PartialModel.vars_empty, VarSet.empty_inter]

@[simp]
lemma models_top {n} : (@top n).models = Set.univ := by
  simp [top, models_eq]

@[simps]
def bot {n} : Horn n where
  vars := ∅
  empty := true
  unit_literals := PartialModel.empty
  clauses := []
  horn_prop := by simp
  clauses_prop := by simp
  subset_vars := by simp [CNF.mem_vars]
  vars_prop := by simp only [PartialModel.vars_empty, VarSet.empty_inter]

@[simp]
lemma models_bot {n} : (@bot n).models = ∅ := by
  simp [bot, models_eq]

def unit_propagate {n} (φ : Horn n) (δ : Cube n) : Horn n :=
  match δ with
  | [] => φ
  | l :: todo =>
    match h : φ.unit_literals.insert l with
    | none => bot
    | some M =>
      let res := (φ.clauses.propagate_literal l).partition fun γ ↦ γ.length < 2
      let δ' := res.1.flatten ++ todo
      let φ' := {
        vars := φ.vars.insert l.1
        empty := φ.empty ∨ res.1.contains []
        unit_literals := M
        clauses := res.snd
        horn_prop := by
          have h := φ.clauses.IsHorn_propagate_literal (l := l) φ.horn_prop
          grind
        clauses_prop := by
          simp [res]
        subset_vars := by
          have h1 := φ.subset_vars
          simp only [PartialModel.vars_insert h, VarSet.mem_union, VarSet.mem_insert, CNF.mem_vars,
            Clause.mem_vars]
          simp_all only [PartialModel.insert_eq_some_iff, VarSet.mem_union, CNF.mem_vars,
            Clause.mem_vars, List.partition_eq_filter_filter, List.mem_filter,
            CNF.mem_propagate_literal, ne_eq, decide_not, Function.comp_apply,
            Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt, ↓existsAndEq,
            and_true, res]
          grind only
        vars_prop := by
          suffices h1 : l.1 ∉ CNF.vars res.2 by
            simp only [VarSet.inter_eq_empty_iff, CNF.mem_vars, Clause.mem_vars,
              PartialModel.vars_insert h, VarSet.mem_insert]
            simp only [List.partition_eq_filter_filter, List.mem_filter, CNF.mem_propagate_literal,
              ne_eq, decide_not, Function.comp_apply, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_false_iff_not, not_lt, ↓existsAndEq, and_true, not_exists, not_and, and_imp,
              res]
            intro i h2 γ hγ hl h3 l' hl' h4 rfl
            simp only [Literal.eq_or_eq_negate_iff_var_eq, ne_of_mem_of_not_mem hl' hl, h4, or_self,
              or_false] at h2
            have h5 := VarSet.inter_eq_empty_iff.1 φ.vars_prop l'.1 h2
            grind only [CNF.mem_vars, Clause.mem_vars]
          simp [res, Literal.eq_or_eq_negate_iff_var_eq]
          grind
      }
      unit_propagate φ' δ'
termination_by φ.clauses.length + δ.length
decreasing_by
  simp only [List.partition_eq_filter_filter, List.length_append,
    List.length_cons, Function.comp_def]
  rw [← Nat.add_assoc _ _ 1, Nat.lt_add_one_iff, ← add_assoc, Nat.add_le_add_iff_right, add_comm]
  apply Lean.Grind.Nat.le_lo
  · apply List.length_flatten_short
    grind only [= List.mem_filter]
  · simp [← List.length_eq_length_filter_add, φ.clauses.length_propagate_literal]

lemma vars_unit_propagate {n} {φ : Horn n} {δ} : (φ.unit_propagate δ).vars ⊆ φ.vars ∪ δ.vars := by
  simp only [VarSet.Subset_def, VarSet.mem_union]
  fun_induction unit_propagate with
  | case1 φ => grind only
  | case2 φ l todo h => grind only [!bot_vars, VarSet.mem_empty]
  | case3 φ l todo M hM res δ' φ' ih =>
    intro i hi
    specialize ih i hi
    simp only [VarSet.mem_insert, List.partition_eq_filter_filter, Cube.mem_vars, List.mem_append,
      List.mem_flatten, List.mem_filter, CNF.mem_propagate_literal, ne_eq, decide_not,
      decide_eq_true_eq, existsAndEq, and_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, δ', res, φ'] at ih
    simp only [Cube.vars_cons, VarSet.mem_insert, Cube.mem_vars]
    grind only [VarSet.mem_union, CNF.mem_vars, Clause.mem_vars, φ.subset_vars]

lemma models_unit_propagate {n} {φ : Horn n} {δ} :
    (φ.unit_propagate δ).models = φ.models ∩ δ.models := by
  fun_induction unit_propagate with
  | case1 φ => simp [Cube.models_nil]
  | case2 φ l todo h =>
    simp only [PartialModel.insert_eq_none_iff] at h
    ext M
    simp only [bot, models_eq, ↓reduceIte, Set.mem_empty_iff_false, Set.mem_inter_iff,
      Set.mem_ite_empty_left, Bool.not_eq_true, PartialModel.mem_models, CNF.mem_models,
      Clause.mem_models, Cube.mem_models, List.mem_cons, forall_eq_or_imp, false_iff, not_and,
      not_forall, and_imp]
    intro h1 h2 h3 h4
    specialize h2 l.negate h
    simp [h4] at h2
  | case3 φ l todo M hM res δ' φ' ih =>
    calc
    (φ'.unit_propagate δ').models
    _ = φ'.models ∩ Cube.models δ' := by
      rw [ih]
    _ = φ'.models ∩ Cube.models res.1.flatten ∩ Cube.models todo := by
      simp [δ']
      grind
    _ = if φ.empty = true ∨ [] ∈ res.1 then
          ∅
        else
          M.models ∩ CNF.models res.2 ∩
          Cube.models res.1.flatten ∩ Cube.models todo := by
      simp [models_eq, φ']
      grind
    _ = if φ.empty = true then
          ∅
        else
          φ.unit_literals.models ∩ (CNF.models res.1 ∩ CNF.models res.2) ∩
          l.models ∩ Cube.models todo := by
      split
      case isTrue h1 => grind [CNF.models_mem_empty res.1]
      case isFalse h1 =>
        have h : Cube.models res.1.flatten = CNF.models res.1 := by
          ext M
          simp only [Cube.mem_models, List.mem_flatten, forall_exists_index, and_imp,
            CNF.mem_models, Clause.mem_models]
          constructor
          · intro h2 γ hγ
            rcases γ with ⟨⟩ | ⟨l', ⟨⟩ | γ'⟩
            · simp [hγ] at h1
            · use l'
              grind
            · grind
          · intro h2 l' γ h3 hl'
            rcases γ with ⟨⟩ | ⟨l', ⟨⟩ | _⟩
            all_goals grind
        apply PartialModel.models_insert at hM
        grind
    _ = φ.models ∩ Cube.models (l :: todo) := by
      have h : CNF.models res.1 ∩ CNF.models res.2 = (φ.clauses.propagate_literal l).models := by
        ext M
        simp only [Set.mem_inter_iff, CNF.mem_models, ← List.forall_mem_union, List.mem_union_iff,
          ← List.mem_partition, res]
      simp only [h, models_eq, Cube.models_cons]
      grind only [Set.mem_inter_iff, Set.mem_empty_iff_false, CNF.mem_models_propagate_literal]

/-- Returns the conjunction of the given Horn-clause with the given Horn-formula. -/
def insert {n} (φ : Horn n) (γ : Clause n) (h : γ.IsHorn) : Horn n :=
  if φ.empty then
    bot
  else
    match h1 : γ.propagate_assignment φ.unit_literals with
    | none => φ
    | some [] => bot
    | some [l] => φ.unit_propagate [l]
    | some (l1 :: l2 :: γ') => {
      vars := φ.vars ∪ Clause.vars (l1 :: l2 :: γ')
      empty := φ.empty
      unit_literals := φ.unit_literals
      clauses := (l1 :: l2 :: γ') :: φ.clauses
      horn_prop := by
        have h2 := φ.horn_prop
        simp_all only [List.mem_cons, forall_eq_or_imp,
          Clause.IsHorn_propagate_assignment h1, implies_true, and_self]
      clauses_prop := by
        have h2 := φ.clauses_prop
        simp_all only [List.mem_cons, forall_eq_or_imp, List.length_cons,
          Nat.le_add_left, implies_true, and_self]
      subset_vars := by
        have := φ.subset_vars
        simp_all only [VarSet.mem_union, CNF.mem_vars, Clause.mem_vars, List.mem_cons,
          exists_eq_or_imp]
        grind only
      vars_prop := by
        suffices  ∀ i ∈ Clause.vars (l1 :: l2 :: γ'), i ∉ φ.unit_literals.vars by
          have := φ.vars_prop
          grind only [VarSet.inter_eq_empty_iff, CNF.mem_vars, Clause.mem_vars, List.mem_cons]
        grind only [PartialModel.mem_vars, Clause.mem_vars_propagate_assignment h1]
    }

lemma vars_insert {n} {φ : Horn n} {γ h1} : (φ.insert γ h1).vars ⊆ φ.vars ∪ γ.vars := by
  unfold insert
  simp only [VarSet.Subset_def, VarSet.mem_union, Clause.mem_vars]
  split
  · simp only [bot_vars, VarSet.mem_empty, IsEmpty.forall_iff, implies_true]
  · split
    next h2 h3 => grind only
    next h2 h3 => grind only [bot_vars, VarSet.mem_empty]
    next h2 l h3 =>
      intro i hi
      apply vars_unit_propagate at hi
      simp only [VarSet.mem_union, Cube.mem_vars] at hi
      apply Clause.mem_propagate_assignment at h3
      rcases hi with hi | ⟨l', hl', rfl⟩
      · exact Or.inl hi
      · specialize h3 l'
        grind only
    next h2 l1 l2 γ' h3 =>
      have := Clause.mem_propagate_assignment h3
      grind only [VarSet.mem_union, Clause.mem_vars]

lemma models_insert {n} {φ : Horn n} {γ h1} : (φ.insert γ h1).models = φ.models ∩ γ.models := by
  unfold insert
  split
  · simp_all only [bot, models_eq, ↓reduceIte, Set.empty_inter]
  · split
    case _ h2 h3 =>
      grind only [models_eq, = Set.subset_def, = Set.mem_inter_iff,
        Clause.propagate_assignment_eq_none h3]
    case _ h2 h3 =>
      have := Clause.mem_models_propagate_assignment h3
      ext M
      simp only [models_bot, Set.mem_empty_iff_false, Set.mem_inter_iff, false_iff, not_and]
      grind only [models_eq, Clause.mem_models, = Set.mem_inter_iff, ← List.not_mem_nil]
    case _ h2 l h3 =>
      ext M
      have := Clause.mem_models_propagate_assignment h3 M
      simp only [models_unit_propagate]
      grind only [models_eq, Clause.mem_models, Cube.models_cons, = Set.mem_inter_iff,
        Cube.mem_models, = List.mem_cons, ← List.not_mem_nil]
    case _ h2 l1 l2 γ' h3 =>
      have := Clause.mem_models_propagate_assignment h3
      ext M
      simp only [models_eq, Set.mem_ite_empty_left, Bool.not_eq_true, Set.mem_inter_iff,
        CNF.mem_models, List.mem_cons, forall_eq_or_imp]
      grind only [models_eq, Clause.mem_models, = List.mem_cons, usr List.eq_or_mem_of_mem_cons]

def insert' {n} (γ : Clause n) (φ : Horn n) : Option (Horn n) :=
  if h : γ.IsHorn then φ.insert γ h else none

@[no_expose]
public instance {n} : Formula n (Horn n) where

  vars φ := φ.vars

  models := models

  models_equiv_right φ M M' h1 := by
    simp only [models, CNF.mem_models, Clause.mem_models]
    intro h2 γ hγ
    specialize h2 γ hγ
    rcases h2 with ⟨l, h2, hM⟩
    have h3 : l.1 ∈ φ.vars := by
      apply φ.subset_vars
      simp [toCNF] at hγ
      split at hγ
      · grind
      · simp_all only [eq_iff_iff, Bool.not_eq_true, List.mem_append, PartialModel.mem_toCNF,
          PartialModel.mem_def, VarSet.mem_union,
          PartialModel.vars_eq, CNF.mem_vars, Clause.mem_vars]
        grind only [= List.mem_cons, ← List.not_mem_nil]
    specialize h1 l.1 h3
    simp_all only [Literal.mem_models, eq_iff_iff]
    use l, h2

@[no_expose]
public instance {n} : Top n (Horn n) where

  top := top

  models_top := by
    simp [Formula.models, models_top]

@[no_expose]
public instance {n} : Bot n (Horn n) where

  bot := bot

  vars_bot := by simp only [Formula.vars, bot_vars]

  models_bot := by simp only [Formula.models, bot, models_eq, ↓reduceIte]

-- Only if this makes ClausalEntailment easier
@[no_expose]
public instance {n} : Consistency n (Horn n) where

  consistent φ := ¬φ.empty

  consistent_iff φ := by
    simp only [Bool.not_eq_true, Bool.decide_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true,
      Formula.models, models_eq, Set.nonempty_def, Set.mem_ite_empty_left, Set.mem_inter_iff,
      CNF.mem_models, exists_and_left, iff_self_and]
    intro h1
    use fun i ↦ ⟨i, true⟩ ∈ φ.unit_literals
    constructor
    · simp only [PartialModel.mem_models, Literal.mem_models]
      intro l hl
      rcases l with ⟨i, true | false⟩
      · have h := φ.unit_literals.disjoint
        simp_all [VarSet.inter_eq_empty_iff, PartialModel.mem_def]
        grind
      · grind
    · intro γ hγ
      obtain ⟨i, h2⟩ : ∃ i, ⟨i, false⟩ ∈ γ := by
        rcases γ with ⟨⟩ | ⟨l1, ⟨⟩ | ⟨l2, γ'⟩⟩
        · have h := φ.clauses_prop [] hγ
          simp at h
        · have h := φ.clauses_prop [l1] hγ
          simp at h
        · have h := φ.horn_prop (l1 :: l2 :: γ') hγ
          rcases l1 with ⟨v, true | false⟩
          · use v
            simp
          · simp [Clause.IsHorn] at h
            use l2.1
            simp [← h.1]
      simp only [PartialModel.mem_def, Clause.mem_models]
      use ⟨i, false⟩
      simp only [h2, Literal.mem_models, Bool.false_eq_true, iff_false, true_and]
      intro h3
      have h4 := VarSet.inter_eq_empty_iff.1 φ.vars_prop i
      simp only [PartialModel.vars_eq, VarSet.mem_union, h3, true_or, CNF.mem_vars,
        Clause.mem_vars, not_exists, not_and, forall_const] at h4
      exact h4 γ hγ ⟨i, false⟩ h2 rfl

@[no_expose]
public instance {n} : ClausalEntailment n (Horn n) where

  entails φ γ := not (Consistency.consistent n (φ.unit_propagate γ.neg))

  entails_iff φ γ := by
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, ← Bool.bool_iff_false,
      Consistency.consistent_iff, Formula.models, models_unit_propagate, Clause.models_neg,
      Set.nonempty_def, Set.mem_inter_iff, Set.mem_compl_iff, Clause.mem_models, Set.subset_def]
    grind only

@[no_expose]
public instance {n} : SententialEntailment n (Horn n) where

  entails φ ψ := ψ.toCNF.all fun γ ↦ ClausalEntailment.entails φ γ

  entails_iff φ ψ := by
    simp [ClausalEntailment.entails_iff, Formula.models, Horn.models]

-- TODO : check whether this can be done more efficiently by only propagating
-- ψ.unit_literals in φ.clauses and vice versa
@[no_expose]
public instance {n} : BoundedConjuction n (Horn n) where
  and φ ψ :=
    let χ : Horn n := {
      vars := φ.vars ∪ ψ.vars
      empty := φ.empty ∨ ψ.empty
      unit_literals := PartialModel.empty
      clauses := φ.clauses ++ ψ.clauses
      horn_prop := by
        rw [List.forall_mem_append]
        exact And.intro φ.horn_prop ψ.horn_prop
      clauses_prop := by
        rw [List.forall_mem_append]
        exact And.intro φ.clauses_prop ψ.clauses_prop
      subset_vars := by
        intro i
        have := φ.subset_vars
        have := ψ.subset_vars
        grind only [VarSet.mem_union, CNF.mem_vars, Clause.mem_vars, PartialModel.vars_empty,
          VarSet.mem_empty, List.mem_append]
      vars_prop := by
        simp }
    χ.unit_propagate (φ.unit_literals.toCube ++ ψ.unit_literals.toCube)

  models_and φ ψ := by
    ext M
    simp [Formula.models, models_unit_propagate]
    simp [models_eq]
    grind

@[no_expose]
public instance {n} : OfPartialModel n (Horn n) where

  ofPartialModel M := {
      vars := M.vars
      empty := false
      unit_literals := M
      clauses := []
      horn_prop := by simp
      clauses_prop := by simp
      subset_vars := by
        grind only [VarSet.mem_union, CNF.mem_vars, List.not_mem_nil, Clause.mem_vars]
      vars_prop := by simp }

  vars_ofPartialModel := by simp only [implies_true, Formula.vars]

  models_ofPartialModel := by simp [models_eq, Formula.models]

-- TODO : can this be done more directly?
@[no_expose]
public instance {n} : Implicant n (Horn n) where

  entails δ φ :=
    match δ.toPartialModel with
    | none => true
    | some M => SententialEntailment.entails n (instOfPartialModel.ofPartialModel M) φ

  entails_iff δ φ := by
    split
    case _ h1 =>
      simp_all only [Cube.toPartialModel_eq_none_iff, Set.empty_subset]
    case _ M h1 =>
      simp only [SententialEntailment.entails_iff, OfPartialModel.models_ofPartialModel,
        Cube.models_toPartialModel h1]

@[no_expose]
public instance {n} : Rename n (Horn n) where

  rename φ V r h1 := {
      vars := VarSet.rename r φ.vars
      empty := φ.empty
      unit_literals :=
        have h2 : φ.unit_literals.vars ⊆ V := by
          intro i hi
          apply h1
          apply φ.subset_vars
          simp only [VarSet.mem_union, hi, true_or]
        φ.unit_literals.rename r h2
      clauses := φ.clauses.rename r
      horn_prop := by
        have h : ∀ γ : Clause n, (γ.rename r).IsHorn ↔ γ.IsHorn := by
            intro γ
            simp only [Clause.IsHorn, Clause.rename, List.countP_map]
            rfl
        simp only [CNF.rename, List.mem_map, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, h]
        exact φ.horn_prop
      clauses_prop := by
        simp only [CNF.rename, List.mem_map, Clause.rename, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, List.length_map]
        exact φ.clauses_prop
      subset_vars := by
        simp only [VarSet.mem_union, PartialModel.mem_vars_rename, CNF.mem_vars, Clause.mem_vars,
          VarSet.mem_rename]
        simp only [CNF.rename, List.mem_map, Clause.rename, exists_exists_and_eq_and,
          Literal.rename]
        have h2 := φ.subset_vars
        simp only [VarSet.mem_union, CNF.mem_vars, Clause.mem_vars] at h2
        grind only
      vars_prop := by
        have h2 := φ.vars_prop
        have h3 := φ.subset_vars
        simp only [VarSet.inter_eq_empty_iff, VarSet.mem_union, PartialModel.mem_vars_rename,
          CNF.mem_vars_rename, not_exists, not_and, forall_exists_index, and_imp] at *
        intro i' i hi rfl j hj
        apply Renaming.ne
        · apply h1
          simp only [Formula.vars]
          grind
        · apply h1
          simp only [Formula.vars]
          grind
        grind }

  vars_rename φ V r h1 := by
    simp only [Formula.vars, VarSet.mem_rename, Set.mem_image, SetLike.mem_coe]
    grind only

  models_rename φ V r h1 := by
    ext M
    simp only [Formula.models, models_eq, PartialModel.models_rename, CNF.models_rename,
      Set.mem_ite_empty_left, Bool.not_eq_true, Set.mem_inter_iff, Set.mem_preimage]

@[no_expose]
public instance {n} : ToCNF n (Horn n) where

  toCNF := toCNF

  models_toCNF φ := by simp only [Formula.models, models]

/--
Translate the given CNF formula to a Horn-formula.
Returns `none` if the CNF-formula is not a Horn-formula.
-/
public def fromCNF {n} (φ : CNF n) : Option (Horn n) :=
  φ.foldrM insert' top

public lemma vars_fromCNF {n} {φ : CNF n} {ψ} :
    Horn.fromCNF φ = some ψ → Formula.vars ψ ⊆ φ.vars := by
  simp only [fromCNF, Formula.vars]
  induction φ generalizing ψ with
  | nil =>
    simp
    grind only [!top_vars, VarSet.mem_empty]
  | cons γ φ ih =>
    intro h1
    simp_all only [List.foldrM_cons, Option.bind_eq_bind, insert', CNF.vars_cons]
    split at h1
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h1
      rcases h1 with ⟨φ', h2, rfl⟩
      intro i hi
      apply vars_insert at hi
      simp only [VarSet.mem_union, VarSet.Subset_def] at *
      grind only
    · grind only [Option.bind_eq_none_iff]

public lemma models_fromCNF {n} {φ : CNF n} {ψ} :
    Horn.fromCNF φ = some ψ → Formula.models ψ = φ.models := by
  simp only [fromCNF, Formula.models]
  induction φ generalizing ψ with
  | nil =>
    simp
    grind [models_top]
  | cons γ φ ih =>
    simp only [List.foldrM_cons, Option.bind_eq_bind, insert', CNF.models_cons]
    split
    · grind only [Option.bind_eq_some_iff, !models_insert]
    · grind only [Option.bind_eq_none_iff]


end Validator.Horn
