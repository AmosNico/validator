import Validator.StateSetFormalism.Formula

namespace Validator
open Formula

structure Horn n where

  vars : VarSet' n

  -- TODO : this is 2CNF, not Horn
  formula : { φ : CNF n // ∀ c ∈ φ, c.length ≤ 2 }

  subset_vars : ∀ i ∈ formula.val.vars, i ∈ vars.val

  deriving DecidableEq, Repr

namespace Horn

def models {n} (φ : Horn n) : Models n :=
  φ.formula.val.models

instance {n} : Formula n (Horn n) where

  vars φ := φ.vars

  models := models

  models_equiv_right φ M M' h1 :=
    by
      apply CNF.models_equiv_right
      intro i hi
      exact h1 i (φ.subset_vars i hi)

instance {n} : Top n (Horn n) where

  top := Horn.mk  VarSet'.empty ⟨[], by simp⟩ (by simp)

  top_correct := by
    ext M
    simp [Formula.models, models]

instance {n} : Bot n (Horn n) where

  bot := Horn.mk VarSet'.empty ⟨[[]], by simp⟩ (by simp)

  bot_correct := by
    simp [Formula.models, models, Formula.vars, Set.ext_iff]

instance {n} : ClausalEntailment n (Horn n) where

  entails := sorry

  entails_correct := sorry

instance {n} : BoundedConjuction n (Horn n) where

  and φ ψ :=
    let formula : { φ : CNF n // _ } := ⟨φ.formula.val ++ ψ.formula.val, by grind⟩
    have h : ∀ i ∈ formula.val.vars , i ∈ (φ.vars.union ψ.vars).val := by
      intro i
      have := φ.subset_vars i
      have := ψ.subset_vars i
      simp_all only [CNF.mem_vars, Prod.exists, VarSet'.mem_union, formula]
      grind
    Horn.mk (VarSet'.union φ.vars ψ.vars) formula h

  and_correct := by
    intro φ ψ
    ext M
    simp [Formula.models, Horn.models]
    grind

instance {n} : OfPartialModel n (Horn n) where

  ofPartialModel := sorry

  ofPartialModel_correct := sorry

instance {n} : Renaming n (Horn n) where

  rename := sorry

  rename_correct := sorry

instance {n} : ToCNF n (Horn n) where

  toCNF φ := φ.formula

  toCNF_correct := by
    simp [Formula.models, Horn.models]

end Validator.Horn
