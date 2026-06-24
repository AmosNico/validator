module

public import Validator.StateSetFormalism.Formula

namespace Validator
open Formula

public structure TwoCNF n where

  private vars : VarSet n

  private formula : { φ : CNF n // ∀ c ∈ φ, c.length ≤ 2 }

  private subset_vars : ∀ i ∈ formula.val.vars, i ∈ vars

  deriving DecidableEq, Repr

namespace TwoCNF

def models {n} (φ : TwoCNF n) : Models n :=
  φ.formula.val.models

@[no_expose]
public instance {n} : Formula n (TwoCNF n) where

  vars φ := φ.vars

  models := models

  models_equiv_right φ M M' h1 :=
    by
      apply CNF.models_equiv_right
      intro i hi
      exact h1 i (φ.subset_vars i hi)

@[no_expose]
public instance {n} : Top n (TwoCNF n) where

  top := TwoCNF.mk ∅ ⟨[], by simp⟩ (by simp)

  models_top := by
    ext M
    simp [Formula.models, models]

@[no_expose]
public instance {n} : Bot n (TwoCNF n) where

  bot := TwoCNF.mk ∅ ⟨[[]], by simp⟩ (by simp)

  vars_bot := by simp only [Formula.vars]

  models_bot := by
    simp only [Formula.models, models, CNF.models_cons, Set.ext_iff, Set.mem_inter_iff,
      Clause.mem_models, List.not_mem_nil, false_and, exists_false, Set.mem_empty_iff_false,
      implies_true]

@[no_expose]
public instance {n} : ClausalEntailment n (TwoCNF n) where

  entails := sorry

  entails_iff := sorry

@[no_expose]
public instance {n} : BoundedConjuction n (TwoCNF n) where

  and φ ψ :=
    let formula : { φ : CNF n // _ } := ⟨φ.formula.val ++ ψ.formula.val, by grind⟩
    have h : ∀ i ∈ formula.val.vars , i ∈ φ.vars ∪ ψ.vars := by
      intro i
      have := φ.subset_vars i
      have := ψ.subset_vars i
      simp_all only [CNF.mem_vars, VarSet.mem_union, formula]
      grind
    TwoCNF.mk (φ.vars ∪ ψ.vars) formula h

  models_and := by
    intro φ ψ
    ext M
    simp [Formula.models, TwoCNF.models]

@[no_expose]
public instance {n} : OfPartialModel n (TwoCNF n) where

  ofPartialModel := sorry

  vars_ofPartialModel := sorry

  models_ofPartialModel := sorry

@[no_expose]
public instance {n} : Rename n (TwoCNF n) where

  rename := sorry

  vars_rename := sorry

  models_rename := sorry

@[no_expose]
public instance {n} : ToCNF n (TwoCNF n) where

  toCNF φ := φ.formula

  models_toCNF := by simp [Formula.models, TwoCNF.models]

end Validator.TwoCNF
