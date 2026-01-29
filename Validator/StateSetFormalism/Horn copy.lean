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

  clauses_prop : clauses.Forall fun γ ↦ γ.length ≥ 2

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
    apply CNF.models_equiv_right
    intro i hi
    exact h1 i sorry

instance {n} : Top n (Horn n) where

  top := Horn.mk VarSet'.empty false [] [] (by simp) (by simp) (by simp [Cube.vars])

  top_correct := by
    ext M
    simp [Formula.models, toCNF]

instance {n} : Bot n (Horn n) where

  bot := Horn.mk VarSet'.empty true [] [] (by simp) (by simp) (by simp [Cube.vars])

  bot_correct := by
    simp [Formula.models, toCNF, CNF.models, Formula.vars]

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
    ⟨
      VarSet'.union φ.vars ψ.vars,
      φ.empty ∨ ψ.empty,
      φ.unit_literals ++ ψ.unit_literals,
      φ.clauses ++ ψ.clauses,
      by
        rw [List.forall_append]
        exact And.intro φ.horn_prop ψ.horn_prop,
      by
        rw [List.forall_append]
        exact And.intro φ.clauses_prop ψ.clauses_prop,
      by
        intro i
        have := φ.subset_vars i
        have := ψ.subset_vars i
        simp_all only [Cube.vars, Set.mem_union, CNF.mem_vars, List.mem_append, VarSet'.mem_union]
        grind
    ⟩

  and_correct := by
    intro φ ψ
    ext M
    simp only [Formula.models, Horn.models, toCNF]
    split
    all_goals split
    all_goals simp_all only [Bool.false_eq_true, false_or, Bool.decide_eq_true, Bool.not_eq_true,
      CNF.mem_models, List.mem_cons, List.not_mem_nil, or_false, false_and, exists_false, imp_false,
      forall_eq, ↓reduceIte, Set.mem_inter_iff, List.mem_append, List.mem_map, and_false, true_or,
      decide_true, not_true_eq_false]
    sorry

instance {n} : OfPartialModel n (Horn n) where

  ofPartialModel V M :=
    ⟨
      V,
      false,
      Cube.ofPartialModel M,
      [],
      by simp,
      by simp,
      by simp [Cube.vars, Cube.ofPartialModel]; grind
    ⟩

  ofPartialModel_correct := by
    simp [instFormula, models, CNF.models]
    sorry

instance {n} : Renaming n (Horn n) where

  rename φ vars' h := sorry

  rename_correct := sorry

instance {n} : ToCNF n (Horn n) where

  toCNF := toCNF

  toCNF_correct φ := by
    simp only [Formula.models, models]

end Validator.Horn
