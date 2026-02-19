import Validator.StateSetFormalism.Formula

import Bdd.BDD

namespace Validator
open Formula

structure BDD n where
  vars : VarSet n
  bdd : _root_.BDD
  nvars_prop : bdd.nvars = n

namespace Formula.Model

noncomputable def toVector {n} (M : Model n) : Vector Bool n :=
  have := Classical.decPred M
  Vector.ofFn fun i ↦ if M i then true else false

def ofVector {n} (V : Vector Bool n) : Model n :=
  fun i ↦ V[i]

@[simp]
lemma ofVector_toVector {n} (M : Model n) : ofVector M.toVector = M :=
  by simp [ofVector, toVector, funext_iff]

@[simp]
lemma toVector_ofVector {n} (V : Vector Bool n) : (ofVector V).toVector = V :=
  by simp [ofVector, toVector, Vector.ext_iff]

end Formula.Model
namespace BDD

private lemma nvars_prop_max {n} {φ ψ : BDD n} : max φ.bdd.nvars ψ.bdd.nvars = n :=
  by simp only [φ.nvars_prop, ψ.nvars_prop, max_self]
/-
def models_aux {n} (φ : BDD n) : Set (Vector Bool n) :=
  { V | φ.bdd.denotation (by simp [φ.nvars_prop]) V }

def models {n} (φ : BDD n) : Models n :=
  { fun i ↦ V[i] = true | V ∈ models_aux φ }
-/
def models {n} (φ : BDD n) : Models n :=
  { M | φ.bdd.denotation (by simp [φ.nvars_prop]) M.toVector }

private lemma models_subset_of_equiv {n} (φ φ' : BDD n) :
  φ.bdd.SemanticEquiv φ'.bdd  → φ.models = φ'.models :=
  by
    simp only [BDD.SemanticEquiv, funext_iff, models, Set.ext_iff, Set.mem_setOf_eq,
      Bool.coe_iff_coe]
    grind only [nvars_prop_max]

lemma models_eq_iff {n} {φ φ' : BDD n} : φ.models = φ'.models ↔ φ.bdd.SemanticEquiv φ'.bdd :=
  by
    constructor
    · simp only [models, Set.ext_iff, Set.mem_setOf_eq, Bool.coe_iff_coe, BDD.SemanticEquiv]
      intro h
      ext V
      specialize h (Model.ofVector (φ.nvars_prop_max ▸ V))
      grind only [Model.toVector_ofVector]
    · intro h1
      have := models_subset_of_equiv φ φ' h1
      have := models_subset_of_equiv φ' φ (by grind only [BDD.SemanticEquiv])
      grind only [= Set.subset_def]

instance {n} : Formula n (BDD n) where

  vars φ := φ.vars

  models := models

  models_equiv_right := sorry

instance {n} : Top n (BDD n) where

  top := {
    vars := ∅
    bdd := (BDD.const true).lift n.zero_le
    nvars_prop := by simp only [BDD.lift_nvars]
  }

  models_top := by
    simp only [Formula.models, models, BDD.lift_denotation, BDD.const_denotation,
      Function.const_apply, Set.setOf_true]

instance {n} : Bot n (BDD n) where

  bot := {
    vars := ∅
    bdd := (BDD.const false).lift n.zero_le
    nvars_prop := by simp only [BDD.lift_nvars]
  }

  vars_bot := by simp only [Formula.vars]

  models_bot := by
    simp only [Formula.models, models, BDD.lift_denotation, BDD.const_denotation,
      Function.const_apply, Bool.false_eq_true, Set.setOf_false]

instance {n} : Consistency n (BDD n) where

  consistent φ := ¬φ.bdd.SemanticEquiv (BDD.const false)

  consistent_iff φ := by
    simp only [BDD.SemanticEquiv, BDD.const_nvars, BDD.const_denotation, funext_iff,
      Function.const_apply, not_forall, Bool.not_eq_false, decide_eq_true_eq, Set.Nonempty,
      Formula.models, models, Set.mem_setOf_eq]
    have h1 : max φ.bdd.nvars 0 = n := by
        simp only [φ.nvars_prop, zero_le, sup_of_le_left]
    constructor
    · rintro ⟨V, h2⟩
      use Model.ofVector (h1 ▸ V)
      grind only [Model.toVector_ofVector]
    · rintro ⟨M, h2⟩
      use h1.symm ▸ M.toVector
      grind only [Model.toVector_ofVector]

instance {n} : ClausalEntailment n (BDD n) where

  entails := sorry

  entails_iff := sorry

instance {n} : Implicant n (BDD n) where

  entails δ φ := sorry

  entails_iff := sorry

instance {n} : SententialEntailment n (BDD n) where

  entails := sorry

  entails_iff := sorry

instance {n} : BoundedConjuction n (BDD n) where

  and φ ψ := {
    vars := φ.vars ∪ ψ.vars
    bdd := φ.bdd.and ψ.bdd
    nvars_prop := by
      simp only [BDD.and_nvars, φ.nvars_prop, ψ.nvars_prop, max_self]
  }

  models_and φ ψ := by
    simp only [Formula.models, models, BDD.and_denotation, Bool.and_eq_true, Set.ext_iff,
      Set.mem_setOf_eq, Set.mem_inter_iff, implies_true]

instance {n} : BoundedDisjunction n (BDD n) where

  or φ ψ := {
    vars := φ.vars ∪ ψ.vars
    bdd := φ.bdd.or ψ.bdd
    nvars_prop := by
      simp only [BDD.or_nvars, φ.nvars_prop, ψ.nvars_prop, max_self]
  }

  models_or φ ψ := by
    simp only [Formula.models, models, BDD.or_denotation, Bool.or_eq_true, Set.ext_iff,
      Set.mem_setOf_eq, Set.mem_union, implies_true]

instance {n} : OfPartialModel n (BDD n) where

  ofPartialModel := sorry

  vars_ofPartialModel := sorry

  models_ofPartialModel := sorry

instance {n} : Rename n (BDD n) where

  rename := sorry

  vars_rename := sorry

  models_rename := sorry

end Validator.BDD
