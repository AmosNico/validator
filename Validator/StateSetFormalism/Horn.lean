import Validator.StateSetFormalism.Formula

namespace Validator.Formula

abbrev Clause.IsHorn {n} (γ : Clause n) : Prop :=
  γ.countP Prod.snd ≤ 1

def Cube.ofPartialModel {n} (M : PartialModel n) : Cube n :=
  M.foldl (fun δ l ↦ l :: δ) []

@[simp]
lemma Cube.models_ofPartialModel {n} {M : PartialModel n} :
  models (ofPartialModel M) = M.models := by
    ext M'
    simp [ofPartialModel, PartialModel.foldl_cons, PartialModel.mem_models]

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
      forall_exists_index, and_imp]
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

def bot {n} : Horn n :=
  {
    vars := VarSet'.empty
    empty := true
    unit_literals := PartialModel.empty
    clauses := []
    horn_prop := by simp
    clauses_prop := by simp
    subset_vars := by simp [CNF.vars]
    vars_prop := by simp
  }

def unit_propagate {n} (φ : Horn n) (δ : Cube n) : Horn n :=
  match δ with
  | [] => φ
  | l :: todo =>
    match h : φ.unit_literals.insert l with
    | none => bot
    | some M =>
      let res := (φ.clauses.propagate_literal l).partition fun γ ↦ γ.length < 2
      let δ' := todo ++ res.1.flatten
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
termination_by δ.length + φ.clauses.length
decreasing_by
  simp only [List.length_append, add_assoc, List.length_cons,
    Nat.add_lt_add_iff_left, Nat.lt_one_add_iff]
  apply Lean.Grind.Nat.le_lo _ _ _ _ (List.length_flatten_short _ (by simp))
  simp only [List.partition_eq_filter_filter, Function.comp_def, ← List.length_eq_length_filter_add]
  apply φ.clauses.length_propagate_literal

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
        and_imp]
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
              CNF.mem_models]
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

instance {n} : Formula n (Horn n) where

  vars φ := φ.vars

  models := models

  models_equiv_right φ M M' h1 := by
    simp only [models, CNF.mem_models]
    intro h2 γ hγ
    specialize h2 γ hγ
    rcases h2 with ⟨l, h2, hM⟩
    have h3 : l.1 ∈ φ.vars := by
      apply φ.subset_vars
      simp [toCNF] at hγ
      split at hγ
      · grind
      · simp_all only [eq_iff_iff, Bool.not_eq_true, List.mem_append, PartialModel.mem_toCNF,
          PartialModel.instMembershipLiteral, Set.mem_union, PartialModel.mem_vars, CNF.mem_vars]
        grind
    specialize h1 l.1 h3
    simp_all only [Literal.mem_models, eq_iff_iff]
    use l, h2

instance {n} : Top n (Horn n) where

  top := {
    vars := VarSet'.empty
    empty := false
    unit_literals := PartialModel.empty
    clauses := []
    horn_prop := by simp
    clauses_prop := by simp
    subset_vars := by simp [CNF.vars]
    vars_prop := by simp
  }

  top_correct := by
    ext M
    simp [Formula.models, models_eq]

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
      simp only [Set.mem_inter_iff, PartialModel.mem_vars, h3, true_or, CNF.mem_vars, true_and,
        not_exists, not_and] at h4
      exact h4 γ hγ (i, false) h2 rfl

instance {n} : ClausalEntailment n (Horn n) where

  entails φ γ := not (Consistency.consistent n (φ.unit_propagate γ.neg))

  entails_correct φ γ := by
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, ← Bool.bool_iff_false,
      Consistency.consistent_correct, Formula.models, models_unit_propagate, Clause.models_neg,
      Set.nonempty_def, Set.mem_inter_iff, Set.mem_compl_iff, Clause.mem_models, Set.subset_def]
    grind only

instance {n} : Implicant n (Horn n) where

  entails δ φ := sorry

  entails_correct δ φ := sorry

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
    χ.unit_propagate (Cube.ofPartialModel φ.unit_literals ++ Cube.ofPartialModel ψ.unit_literals)

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
        simp [PartialModel.vars, VarSet'.toVarSet]
      vars_prop := by
        simp [CNF.vars] }

  ofPartialModel_correct := by
    simp [instFormula, models_eq, CNF.models]

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
