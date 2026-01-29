import Validator.StateSetFormalism.Formula

namespace Validator.Formula

abbrev Clause.IsHorn {n} (γ : Clause n) : Prop :=
  γ.countP Prod.snd ≤ 1

def Cube.ofPartialModel {n} {V : VarSet' n} (M : PartialModel V) : Cube n :=
  V.val.mapFinIdx fun i var h ↦ (var, M[i])

@[simp]
lemma Cube.models_ofPartialModel {n} {V : VarSet' n} {M : PartialModel V} :
  models (ofPartialModel M) = M.models := by
    ext M'
    simp only [ofPartialModel, mem_models, List.mem_mapFinIdx, Literal.mem_models,
      forall_exists_index, PartialModel.models, Fin.getElem_fin, Fin.eta, Set.mem_setOf_eq]
    constructor
    · grind
    · intro h γ i hi rfl
      specialize h ⟨i, hi⟩
      simp_all

namespace CNF

-- write in terms of filterMap?
def propagate_literal {n} (φ : CNF n) (l : Literal n) : CNF n :=
  (φ.filter fun γ ↦ not (γ.contains l)).map (List.filter (· ≠ l.negate))

lemma length_propagate_literal {n} {φ : CNF n} {l} : (φ.propagate_literal l).length ≤ φ.length :=
  by
    simp only [propagate_literal, List.length_map]
    apply List.length_filter_le

lemma IsHorn_propagate_literal {n} {φ : CNF n} {l} :
  φ.Forall Clause.IsHorn → (φ.propagate_literal l).Forall Clause.IsHorn :=
  by
    simp only [List.forall_iff_forall_mem, Clause.IsHorn, List.countP_eq_length_filter,
      propagate_literal, List.mem_map, List.mem_filter, forall_exists_index, and_imp]
    intro h1 γ' γ hγ h3 rfl
    rw [List.filter_comm]
    grind only [List.length_filter_le]

lemma vars_propagate_literal {n} {φ : CNF n} {l} : (φ.propagate_literal l).vars ⊆ φ.vars \ {l.1} :=
  by
    intro v hv
    simp [vars, propagate_literal, Literal.negate] at hv
    simp [vars]
    grind

def rename {n} (φ : CNF n) (vars vars' : VarSet' n)
  (h1 : vars.val.length = vars'.val.length) : CNF n :=
  sorry

end Formula.CNF
open Formula

structure Horn n where

  vars : VarSet' n

  empty : Bool

  unit_literals : Cube n

  clauses : CNF n

  horn_prop : clauses.Forall Clause.IsHorn

  clauses_prop : clauses.Forall fun γ ↦ 2 ≤ γ.length

  subset_vars : ∀ i ∈ unit_literals.vars ∪ clauses.vars, i ∈ vars.val

  deriving DecidableEq, Repr

namespace Horn

def toCNF {n} (φ : Horn n) : CNF n :=
    if φ.empty then
      [[]]
    else
      φ.unit_literals.map (fun l ↦ [l]) ++ φ.clauses

abbrev models {n} (φ : Horn n) : Models n := φ.toCNF.models

lemma models_eq {n} {φ : Horn n} :
  φ.models = if φ.empty then ∅ else φ.unit_literals.models ∩ φ.clauses.models :=
  by
    simp only [models, toCNF]
    split
    · simp [CNF.models]
    · ext M
      simp only [CNF.mem_models, List.mem_append, List.mem_map,
        Set.mem_inter_iff, Cube.mem_models]
      constructor
      · intro h1
        constructor
        · intro l hl
          specialize h1 [l] (by grind)
          grind
        · grind
      · grind

instance {n} : Formula n (Horn n) where

  vars φ := φ.vars

  models := models

  models_equiv_right φ M M' h1 := by
    simp only [models, CNF.mem_models]
    intro h2 γ hγ
    specialize h2 γ hγ
    rcases h2 with ⟨l, h2, hM⟩
    have h3 : l.1 ∈ φ.vars.val := by
      apply φ.subset_vars
      rw [toCNF] at hγ
      simp only [Set.mem_union, CNF.mem_vars, Cube.vars]
      grind
    specialize h1 l.1 h3
    simp_all only [Literal.mem_models, eq_iff_iff]
    use l, h2

def unit_propagate_aux {n} (φ : Horn n) (todo : Cube n) : Horn n :=
  match todo with
  | [] => φ
  | l :: todo =>
    let res := (φ.clauses.propagate_literal l).partition fun γ ↦ γ.length < 2
    let empty := res.fst.contains []
    let todo' := todo ++ res.fst.flatten
    let φ' := {
      vars := φ.vars
      empty := empty
      unit_literals := l :: φ.unit_literals
      clauses := res.snd
      horn_prop := by
        have h := φ.clauses.IsHorn_propagate_literal (l := l) φ.horn_prop
        simp only [List.forall_iff_forall_mem] at ⊢ h
        grind
      clauses_prop := by
        simp [res, List.forall_iff_forall_mem]
      subset_vars := by
        simp only [Cube.vars, List.mem_cons, exists_eq_or_imp,
          Set.mem_union, Set.mem_setOf_eq, CNF.mem_vars]
        intro i hi
        rcases hi with ⟨rfl | h⟩ | h
        · sorry
        · sorry
        sorry
    }
    unit_propagate_aux φ' todo'
termination_by todo.length + φ.clauses.length
decreasing_by
  simp only [List.length_append, add_assoc, List.length_cons,
    Nat.add_lt_add_iff_left, Nat.lt_one_add_iff]
  apply Lean.Grind.Nat.le_lo _ _ _ _ (List.length_flatten_short _ (by simp))
  simp only [List.partition_eq_filter_filter, Function.comp_def, ← List.length_eq_length_filter_add]
  apply φ.clauses.length_propagate_literal

def unit_propagate {n} (φ : Horn n) :
  { ψ : Horn n // ψ.unit_literals.vars ∩ ψ.clauses.vars = ∅ } where
    val := sorry
    property := sorry

instance {n} : Top n (Horn n) where

  top := Horn.mk VarSet'.empty false [] [] (by simp) (by simp) (by simp [Cube.vars])

  top_correct := by
    ext M
    simp [Formula.models, models_eq]

instance {n} : Bot n (Horn n) where

  bot := Horn.mk VarSet'.empty true [] [] (by simp) (by simp) (by simp [Cube.vars])

  bot_correct := by
    simp [Formula.models, models_eq, Formula.vars]

-- Only if this makes ClausalEntailment easier
instance {n} : Consistency n (Horn n) where

  consistent := sorry

  consistent_correct := sorry

instance {n} : ClausalEntailment n (Horn n) where

  entails φ γ := not (Consistency.consistent n (sorry : Horn n))

  entails_correct := sorry

instance {n} : Implicant n (Horn n) where

  entails δ φ := sorry

  entails_correct := sorry

instance {n} : SententialEntailment n (Horn n) where

  entails φ ψ := sorry

  entails_correct := sorry

instance {n} : BoundedConjuction n (Horn n) where

  and φ ψ :=
    { vars := VarSet'.union φ.vars ψ.vars
      empty := φ.empty ∨ ψ.empty
      unit_literals := φ.unit_literals ++ ψ.unit_literals
      clauses := φ.clauses ++ ψ.clauses
      horn_prop := by
        rw [List.forall_append]
        exact And.intro φ.horn_prop ψ.horn_prop
      clauses_prop := by
        rw [List.forall_append]
        exact And.intro φ.clauses_prop ψ.clauses_prop
      subset_vars := by
        intro i
        have := φ.subset_vars i
        have := ψ.subset_vars i
        simp_all only [Cube.vars, Set.mem_union, CNF.mem_vars, List.mem_append, VarSet'.mem_union]
        grind }

  and_correct := by
    intro φ ψ
    ext M
    simp [Formula.models, models_eq]
    grind

instance {n} : OfPartialModel n (Horn n) where

  ofPartialModel V M :=
    { vars := V
      empty := false
      unit_literals := Cube.ofPartialModel M
      clauses := []
      horn_prop := by simp
      clauses_prop := by simp
      subset_vars := by
        simp [Cube.vars, Cube.ofPartialModel]
        grind }

  ofPartialModel_correct := by
    simp [instFormula, models_eq, CNF.models]

instance {n} : Renaming n (Horn n) where

  rename φ vars' h := sorry

  rename_correct := sorry

instance {n} : ToCNF n (Horn n) where

  toCNF := toCNF

  toCNF_correct φ := by
    simp only [Formula.models, models]

end Validator.Horn
