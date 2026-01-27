import Validator.StateSetFormalism.Formula

namespace Validator
open Formula

abbrev Clause.IsHorn {n} (γ : Clause n) : Prop :=
  γ.countP Prod.snd ≤ 1

namespace Formula.CNF

def ofPartialModel {n} {V : VarSet' n} (M : PartialModel V) : CNF n :=
  V.val.mapFinIdx fun i var h ↦ [(var, M[i])]

@[simp]
lemma models_ofPartialModel {n} {V : VarSet' n} {M : PartialModel V} :
  models (ofPartialModel M) = M.models := by
    ext M'
    simp only [ofPartialModel, mem_models, List.mem_mapFinIdx, Literal.mem_models,
      forall_exists_index, PartialModel.models, Fin.getElem_fin, Fin.eta, Set.mem_setOf_eq]
    constructor
    · grind
    · intro h γ i hi rfl
      specialize h ⟨i, hi⟩
      simp_all

def rename {n} (φ : CNF n) (vars vars' : VarSet' n)
  (h1 : vars.val.length = vars'.val.length) : CNF n :=
  sorry

end Formula.CNF

structure Horn n where

  vars : VarSet' n

  formula : CNF n

  prop : formula.Forall Clause.IsHorn

  subset_vars : ∀ i ∈ formula.vars, i ∈ vars.val

  deriving DecidableEq, Repr

namespace Horn

abbrev models {n} (φ : Horn n) : Models n := φ.formula.models

instance {n} : Formula n (Horn n) where

  vars φ := φ.vars

  models := models

  models_equiv_right φ M M' h1 := by
    apply CNF.models_equiv_right
    intro i hi
    exact h1 i (φ.subset_vars i hi)

instance {n} : Top n (Horn n) where

  top := Horn.mk VarSet'.empty [] (by simp) (by simp)

  top_correct := by
    ext M
    simp [Formula.models]

instance {n} : Bot n (Horn n) where

  bot := Horn.mk VarSet'.empty [[]] (by simp) (by simp)

  bot_correct := by
    simp [Formula.models, models, Formula.vars, Set.ext_iff]

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
    let formula := φ.formula ++ ψ.formula
    have h1 : List.Forall Clause.IsHorn formula := by
      rw [List.forall_append]
      exact And.intro φ.prop ψ.prop
    have h2 : ∀ i ∈ formula.vars , i ∈ (φ.vars.union ψ.vars).val := by
      intro i
      have := φ.subset_vars i
      have := ψ.subset_vars i
      simp_all only [CNF.mem_vars, Prod.exists, VarSet'.mem_union, formula]
      grind
    Horn.mk (VarSet'.union φ.vars ψ.vars) formula h1 h2

  and_correct := by
    intro φ ψ
    ext M
    simp [Formula.models, Horn.models]
    grind

instance {n} : OfPartialModel n (Horn n) where

  ofPartialModel V M := by
    apply Horn.mk V (CNF.ofPartialModel M)
    · simp only [List.forall_iff_forall_mem, CNF.ofPartialModel]
      grind
    · simp [CNF.ofPartialModel]
      grind

  ofPartialModel_correct := by
    simp [instFormula, models]

instance {n} : Renaming n (Horn n) where

  rename φ vars' h := sorry

  rename_correct := sorry

instance {n} : ToCNF n (Horn n) where

  toCNF := formula

  toCNF_correct := by
    simp [Formula.models]

end Validator.Horn
