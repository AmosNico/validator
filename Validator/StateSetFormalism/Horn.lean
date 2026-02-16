import Validator.StateSetFormalism.Formula

namespace Validator.Formula.Clause

abbrev IsHorn {n} (γ : Clause n) : Prop :=
  γ.countP Prod.snd ≤ 1

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
  γ.propagate_assignment M = none → M.models ⊆ γ.models  :=
  by
    fun_induction propagate_assignment
    case _ =>
      simp only [reduceCtorEq, models, List.not_mem_nil, false_and, exists_false, Set.setOf_false,
        Set.subset_empty_iff, IsEmpty.forall_iff]
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
  γ.propagate_assignment M = some γ' → γ.IsHorn → γ'.IsHorn :=
  by
    intro h1
    suffices h: γ'.countP Prod.snd ≤ γ.countP Prod.snd by grind only
    fun_induction propagate_assignment generalizing γ'
    case _ => grind only
    case _ l γ h1 => simp only [reduceCtorEq] at h1
    case _ l γ h1 h2 h3 => grind only [= List.countP_cons]
    case _ l γ h1 h2 h3 =>
      cases h4 : propagate_assignment M γ
      · grind
      · grind

lemma mem_propagate_assignment {n} {γ γ' : Clause n} {M} :
  γ.propagate_assignment M = some γ' → ∀ l, l ∈ γ' ↔ l ∈ γ ∧ l.negate ∉ M :=
  by
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
  γ.propagate_assignment M = some γ' → ∀ l, l ∈ γ' ↔ l ∈ γ ∧ l ∉ M ∧ l.negate ∉ M :=
  by
    fun_induction propagate_assignment generalizing γ'
    case _ => grind
    case _ l γ h1 => simp only [reduceCtorEq, IsEmpty.forall_iff]
    case _ l' γ h1 h2 h3 => grind only [= List.mem_cons]
    case _ l γ h1 h2 h3 =>
      cases h4 : propagate_assignment M γ
      · grind
      · grind

@[simp]
lemma mem_vars'_propagate_assignment {n} {γ γ' : Clause n} {M} :
  γ.propagate_assignment M = some γ' → ∀ i, i ∈ γ'.vars' ↔ i ∈ γ.vars' ∧ ∀ l ∈ M, ¬l.1 = i :=
  by
    intro h1 i
    simp only [mem_vars', mem_propagate_assignment' h1]
    constructor
    · rintro ⟨l, h2, rfl⟩
      grind only [Literal.eq_or_eq_negate_iff_var_eq]
    · rintro ⟨⟨l, h2, rfl⟩, h3⟩
      grind only [Literal.eq_or_eq_negate_iff_var_eq]

lemma mem_models_propagate_assignment {n} {γ γ' : Clause n} {M} :
  γ.propagate_assignment M = some γ' → ∀ M' ∈ M.models, M' ∈ γ'.models ↔ M' ∈ γ.models :=
  by
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

lemma length_propagate_literal {n} {φ : CNF n} {l} : (φ.propagate_literal l).length ≤ φ.length :=
  by
    simp only [propagate_literal, List.length_map]
    apply List.length_filter_le

lemma IsHorn_propagate_literal {n} {φ : CNF n} {l} :
  (∀ γ ∈ φ, γ.IsHorn) → ∀ γ ∈ φ.propagate_literal l, γ.IsHorn :=
  by
    simp only [Clause.IsHorn, List.countP_eq_length_filter, propagate_literal, List.mem_map,
      List.mem_filter, forall_exists_index, and_imp]
    intro h1 γ' γ hγ h3 rfl
    rw [List.filter_comm]
    grind only [List.length_filter_le]

lemma vars_propagate_literal {n} {φ : CNF n} {l} : (φ.propagate_literal l).vars ⊆ φ.vars \ {l.1} :=
  by
    intro v hv
    simp [vars, propagate_literal, Literal, Literal.negate] at hv
    simp [vars, Literal]
    grind

@[simp]
lemma mem_propagate_literal {n} {φ : CNF n} {l γ} :
  γ ∈ (φ.propagate_literal l) ↔ ∃ γ' ∈ φ, l ∉ γ' ∧ γ = γ'.filter (· ≠ l.negate) :=
  by
    simp [propagate_literal]
    grind

lemma mem_models_propagate_literal {n} {φ : CNF n} {l} :
  ∀ M ∈ l.models, M ∈ (φ.propagate_literal l).models ↔ M ∈ φ.models :=
  by
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
structure Horn n where

  vars : VarSet' n

  empty : Bool

  unit_literals : PartialModel n

  clauses : CNF n

  horn_prop : ∀ γ ∈ clauses, γ.IsHorn

  clauses_prop : ∀ γ ∈ clauses, 2 ≤ γ.length

  subset_vars : ∀ i ∈ unit_literals.vars ∪ clauses.vars, i ∈ vars

  vars_prop : unit_literals.vars ∩ clauses.vars = ∅

  deriving DecidableEq, Repr

namespace Horn

def toCNF {n} (φ : Horn n) : CNF n :=
    if φ.empty then
      [[]]
    else
      φ.unit_literals.toCNF ++ φ.clauses

def models {n} (φ : Horn n) : Models n := φ.toCNF.models

lemma models_eq {n} {φ : Horn n} :
  φ.models = if φ.empty then ∅ else φ.unit_literals.models ∩ φ.clauses.models :=
  by
    simp only [models, toCNF]
    split
    · simp [CNF.models]
    · simp only [CNF.models_append, PartialModel.models_toCNF]

def top {n} : Horn n where
    vars := VarSet'.empty
    empty := false
    unit_literals := PartialModel.empty
    clauses := []
    horn_prop := by simp
    clauses_prop := by simp
    subset_vars := by simp [CNF.vars]
    vars_prop := by simp

@[simp]
lemma models_top {n} : (@top n).models = Set.univ :=
  by
    simp [Set.ext_iff, top, models_eq]

def bot {n} : Horn n where
    vars := VarSet'.empty
    empty := true
    unit_literals := PartialModel.empty
    clauses := []
    horn_prop := by simp
    clauses_prop := by simp
    subset_vars := by simp [CNF.vars]
    vars_prop := by simp

@[simp]
lemma models_bot {n} : (@bot n).models = ∅ :=
  by simp [bot, models_eq]

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
          simp [PartialModel.vars_insert h]
          have h1 := φ.subset_vars
          simp_all only [Set.mem_union, CNF.mem_vars, List.partition_eq_filter_filter,
            List.mem_filter, CNF.mem_propagate_literal, ne_eq, decide_not, Function.comp_apply,
            Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt, ↓existsAndEq,
            and_true, res]
          grind
        vars_prop := by
          suffices h1 : l.1 ∉ CNF.vars res.2 by
            ext i
            simp only [PartialModel.vars_insert h, Set.union_singleton,
              List.partition_eq_filter_filter, Set.mem_inter_iff, Set.mem_insert_iff, CNF.mem_vars,
              List.mem_filter, CNF.mem_propagate_literal, ne_eq, decide_not, Function.comp_apply,
              Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt, ↓existsAndEq,
              and_true, Set.mem_empty_iff_false, iff_false, not_and, not_exists, and_imp, res]
            intro h2 γ hγ hl h3 l' hl' h4 rfl
            simp [Literal.eq_or_eq_negate_iff_var_eq, h4, ne_of_mem_of_not_mem hl' hl] at h2
            have h5 := Set.eq_empty_iff_forall_notMem.1 φ.vars_prop l'.1
            grind only [= Set.mem_inter_iff, CNF.mem_vars]
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

lemma models_unit_propagate {n} {φ : Horn n} {δ} :
  (φ.unit_propagate δ).models = φ.models ∩ δ.models :=
  by
    fun_induction unit_propagate with
    | case1 φ => simp [Cube.models]
    | case2 φ l todo h =>
      simp only [PartialModel.insert_eq_none_iff] at h
      ext M
      simp only [bot, models_eq, ↓reduceIte, Set.mem_empty_iff_false, Cube.models, List.mem_cons,
        forall_eq_or_imp, Set.mem_inter_iff, Set.mem_ite_empty_left, Bool.not_eq_true,
        PartialModel.mem_models, CNF.mem_models, Set.mem_setOf_eq, false_iff, not_and, not_forall,
        and_imp, Clause.mem_models]
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
      vars := φ.vars ∪ Clause.vars' (l1 :: l2 :: γ')
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
        simp_all only [Set.mem_union, List.mem_cons, exists_eq_or_imp,
          Clause.mem_vars', VarSet'.mem_union, CNF.mem_vars]
        grind only
      vars_prop := by
        suffices  ∀ i ∈ Clause.vars' (l1 :: l2 :: γ'), i ∉ φ.unit_literals.vars by
          have := φ.vars_prop
          grind only [Set.mem_inter_iff, CNF.mem_vars, Clause.mem_vars', List.mem_cons]
        grind only [PartialModel.mem_vars, Clause.mem_vars'_propagate_assignment h1]
    }

lemma models_insert {n} {φ : Horn n} {γ h1} : (φ.insert γ h1).models = φ.models ∩ γ.models :=
  by
    unfold insert
    split
    · simp_all [ge_iff_le, bot, models_eq, ↓reduceIte, Set.empty_inter]
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

def insert' {n} (φ : Horn n) (γ : Clause n) : Option (Horn n) :=
  if h : γ.IsHorn then φ.insert γ h else none

/--
Translate the given CNF formula to a Horn-formula.
Returns `none` if the CNF-formula is not a Horn-formula.
-/
def fromCNF {n} (φ : CNF n) : Option (Horn n) :=
  φ.foldlM insert' top

lemma models_formCNF {n} {φ : CNF n} {ψ} : Horn.fromCNF φ = some ψ → ψ.models = φ.models :=
  by
    suffices h1 : ∀ ψ', φ.foldlM insert' ψ' = some ψ → ψ.models = φ.models ∩ ψ'.models by
      specialize h1 top
      simp_all only [models_top, Set.inter_univ, fromCNF, implies_true]
    induction φ with
    | nil => simp [CNF.models]
    | cons γ φ ih =>
      intro φ' h2
      simp_all only [List.foldlM_cons, Option.bind_eq_bind, insert']
      split at h2
      case _ h3 =>
        specialize ih (φ'.insert γ h3) h2
        simp_all only [Option.bind_some, models_insert, CNF.models_cons]
        grind only
      case _ h2 => grind only [= Option.bind_none]

instance {n} : Formula n (Horn n) where

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
        PartialModel.instMembershipLiteral, Set.mem_union,
        PartialModel.mem_vars_iff_mem_pos_or_mem_neg, CNF.mem_vars]
        grind only [= List.mem_cons, ← List.not_mem_nil]
    specialize h1 l.1 h3
    simp_all only [Literal.mem_models, eq_iff_iff]
    use l, h2

instance {n} : Top n (Horn n) where

  top := top

  top_correct := by
    simp [Formula.models, models_top]

instance {n} : Bot n (Horn n) where

  bot := bot

  bot_correct := by
    simp [bot, models_eq, Formula.models, Formula.vars]

-- Only if this makes ClausalEntailment easier
instance {n} : Consistency n (Horn n) where

  consistent φ := ¬φ.empty

  consistent_correct φ := by
    simp only [Bool.not_eq_true, Bool.decide_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true,
      Formula.models, models_eq, Set.nonempty_def, Set.mem_ite_empty_left, Set.mem_inter_iff,
      CNF.mem_models, exists_and_left, iff_self_and]
    intro h1
    use fun i ↦ (i, true) ∈ φ.unit_literals
    constructor
    · simp only [PartialModel.mem_models, Literal.mem_models]
      intro l hl
      rcases l with ⟨i, true | false⟩
      · have h := φ.unit_literals.disjoint
        simp_all [VarSet'.Disjoint_iff, PartialModel.instMembershipLiteral]
        grind
      · grind
    · intro γ hγ
      obtain ⟨i, h2⟩ : ∃ i, (i, false) ∈ γ := by
        rcases γ with ⟨⟩ | ⟨l1, ⟨⟩ | ⟨l2, γ'⟩⟩
        · have h := φ.clauses_prop [] hγ
          simp at h
        · have h := φ.clauses_prop [l1] hγ
          simp at h
        · have h := φ.horn_prop (l1 :: l2 :: γ') hγ
          rcases l1 with ⟨v, true | false⟩
          · use v
            simp
          · simp at h
            use l2.1
            simp [← h.1]
      use (i, false)
      simp only [h2, PartialModel.instMembershipLiteral, Literal.mem_models, Bool.false_eq_true,
        iff_false, true_and]
      intro h3
      have h4 := Set.eq_empty_iff_forall_notMem.1 φ.vars_prop i
      simp only [Set.mem_inter_iff, PartialModel.mem_vars_iff_mem_pos_or_mem_neg, h3, true_or,
        CNF.mem_vars, true_and, not_exists, not_and] at h4
      exact h4 γ hγ (i, false) h2 rfl

instance {n} : ClausalEntailment n (Horn n) where

  entails φ γ := not (Consistency.consistent n (φ.unit_propagate γ.neg))

  entails_correct φ γ := by
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, ← Bool.bool_iff_false,
      Consistency.consistent_correct, Formula.models, models_unit_propagate, Clause.models_neg,
      Set.nonempty_def, Set.mem_inter_iff, Set.mem_compl_iff, Clause.mem_models, Set.subset_def]
    grind only

instance {n} : SententialEntailment n (Horn n) where

  entails φ ψ := ψ.toCNF.all fun γ ↦ ClausalEntailment.entails φ γ

  entails_correct φ ψ := by
    simp [ClausalEntailment.entails_correct, Formula.models, Horn.models]

-- TODO : check whether this can be done more efficiently by only propagating
-- ψ.unit_literals in φ.clauses and vice versa
instance {n} : BoundedConjuction n (Horn n) where
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
        simp_all only [Set.mem_union, CNF.mem_vars, PartialModel.vars_empty, Set.empty_union,
          List.mem_append, VarSet'.mem_union, forall_exists_index, and_imp]
        grind
      vars_prop := by
        simp }
    χ.unit_propagate (φ.unit_literals.toCube ++ ψ.unit_literals.toCube)

  and_correct φ ψ := by
    ext M
    simp [Formula.models, models_unit_propagate]
    simp [models_eq]
    grind

instance {n} : OfPartialModel n (Horn n) where

  ofPartialModel M := {
      vars := M.vars'
      empty := false
      unit_literals := M
      clauses := []
      horn_prop := by simp
      clauses_prop := by simp
      subset_vars := by
        grind only [PartialModel.mem_vars', = Set.mem_union, CNF.mem_vars, ← List.not_mem_nil]
      vars_prop := by
        simp [CNF.vars] }

  ofPartialModel_correct := by
    simp [instFormula, models_eq, CNF.models]

-- TODO : can this be done more directly?
instance {n} : Implicant n (Horn n) where

  entails δ φ :=
    match δ.toPartialModel with
    | none => true
    | some M => SententialEntailment.entails n (instOfPartialModel.ofPartialModel M) φ

  entails_correct δ φ := by
    split
    case _ h1 =>
      simp_all only [Cube.toPartialModel_eq_none_iff, Set.empty_subset]
    case _ M h1 =>
      simp only [SententialEntailment.entails_correct, OfPartialModel.ofPartialModel_correct,
        Cube.models_toPartialModel h1]

instance {n} : Rename n (Horn n) where

  rename φ V r h1 := {
      vars := VarSet'.rename r φ.vars
      empty := φ.empty
      unit_literals :=
        have h2 : φ.unit_literals.vars' ⊆ V := by
          intro i hi
          apply h1
          apply φ.subset_vars
          simp only [PartialModel.vars, VarSet'.toVarSet, Set.mem_union, Set.mem_setOf_eq, hi,
            true_or]
        φ.unit_literals.rename r h2
      clauses := φ.clauses.rename r
      horn_prop := by
        have h : ∀ γ : Clause n, (γ.rename r).IsHorn ↔ γ.IsHorn := by
            intro γ
            unfold Clause.rename Literal.rename
            simp
            rfl
        simp only [CNF.rename, List.mem_map, ge_iff_le, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, h]
        exact φ.horn_prop
      clauses_prop := by
        simp only [CNF.rename, List.mem_map, Clause.rename, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, List.length_map]
        exact φ.clauses_prop
      subset_vars := by
        simp only [PartialModel.vars_rename, CNF.rename, Set.mem_union, Set.mem_image, CNF.mem_vars,
          List.mem_map, Clause.rename, exists_exists_and_eq_and, Literal.rename, VarSet'.mem_rename]
        have h2 := φ.subset_vars
        grind only [= Set.mem_union, CNF.mem_vars]
      vars_prop := by
        have h2 := φ.vars_prop
        have h3 := φ.subset_vars
        simp only [PartialModel.vars_rename, CNF.vars_rename, Set.eq_empty_iff_forall_notMem,
          Set.mem_inter_iff, Set.mem_image, not_and, not_exists, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂] at *
        intro i hi j hj
        apply Renaming.ne
        · apply h1
          simp [Formula.vars]
          grind
        · apply h1
          simp [Formula.vars]
          grind
        grind }

  rename_correct φ V r h1 := by
    simp only [Formula.vars, VarSet'.mem_rename, VarSet'.toVarSet, Set.mem_image, Set.mem_setOf_eq,
      Formula.models, models_eq]
    constructor
    · grind
    · ext M
      simp only [PartialModel.models_rename, Set.mem_ite_empty_left, Bool.not_eq_true,
        Set.mem_inter_iff, Set.mem_preimage, CNF.models_rename]

instance {n} : ToCNF n (Horn n) where

  toCNF := toCNF

  toCNF_correct φ := by
    simp only [Formula.models, models]

end Validator.Horn
