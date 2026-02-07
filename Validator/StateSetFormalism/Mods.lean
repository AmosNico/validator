import Validator.StateSetFormalism.Formula

namespace Validator
open Formula

structure MODS n where
  vars : VarSet' n
  mods : List (PartialModel n)
  prop : ∀ M ∈ mods, M.vars' = vars
  deriving DecidableEq, Repr

namespace Formula.PartialModel

/-
lemma disjoint {n} {V : VarSet' n} {M1 M2 : PartialModel V} {M} :
  M ∈ M1.models → M ∈ M2.models → M1 = M2 :=
  by
    simp only [models]
    intro hM1 hM2
    ext i hi
    specialize hM1 ⟨i, hi⟩
    specialize hM2 ⟨i, hi⟩
    simp_all
-/

end PartialModel

namespace Clause

private def isTrivial_aux {n} (acc : Vector (Bool × Bool) n) : Clause n → Vector (Bool × Bool) n
| [] => acc
| (x, true) :: ls => isTrivial_aux (acc.set x (true, acc[x].2)) ls
| (x, false) :: ls => isTrivial_aux (acc.set x (acc[x].1, true)) ls

def isTrivial {n} (γ : Clause n) : Bool :=
  (isTrivial_aux (Vector.replicate n (false, false)) γ).contains (true, true)

lemma isTrivial_iff {n} {γ : Clause n} : isTrivial γ ↔ ∃ x, (x, true) ∈ γ ∧ (x, false) ∈ γ :=
  by
    sorry

end Formula.Clause
namespace MODS

def models {n} (φ : MODS n) : Models n :=
  { M | ∃ M' ∈ φ.mods, M ∈ PartialModel.models M' }

@[simp]
lemma mem_models {n} {φ : MODS n} {M} : M ∈ φ.models ↔ ∃ M' ∈ φ.mods, M ∈ M'.models :=
  by
    simp [models]

instance {n} : Formula n (MODS n) where

  vars φ := φ.vars

  models := models

  models_equiv_right := by
    simp [models, PartialModel.models]
    sorry -- grind

instance {n} : Top n (MODS n) where

  top := sorry

  top_correct := sorry

instance {n} : Bot n (MODS n) where

  bot := sorry

  bot_correct := sorry

instance {n} : ClausalEntailment n (MODS n) where

  -- This only seems to work is all variables of γ are in φ.vars
  -- Otherwise, if p ∉ φ.vars, then γ := p ∨ ¬ p causes problems
  entails φ γ := φ.mods.all (fun M ↦ γ.any fun l ↦ l ∈ M) || γ.isTrivial

  entails_correct :=
    by
      intro φ γ
      simp only [Bool.or_eq_true, List.all_eq_true, List.any_eq_true, Literal, Prod.exists,
        Clause.isTrivial_iff, Formula.models, Set.subset_def, mem_models, Clause.mem_models,
        forall_exists_index, and_imp]
      constructor
      · intro h M M' hM' hM
        rcases h with h | ⟨x, h⟩
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hM'
          specialize h φ.mods[i] hM'
          rcases h with ⟨var, b, h1, h2⟩
          use var, b, h1
          simp_all only [List.getElem_mem, PartialModel.mem_models, decide_eq_true_eq]
        · if h : M x then
            use x, true
            simp_all [Literal.mem_models]
          else
            use x, false
            simp_all [Literal.mem_models]
      · intro h
        if h' : ∃ x, (x, true) ∈ γ ∧ (x, false) ∈ γ then
          exact Or.inr h'
        else
          apply Or.inl
          intro M' hM'
          obtain ⟨M, hM⟩ := M'.models_nonempty
          rcases h M M' hM' hM with ⟨var, b, h1, h2⟩
          use var, b, h1
          simp_all only [Literal.mem_models, Bool.exists_bool, Bool.false_eq_true, iff_false,
            iff_true, PartialModel.mem_models]
          by_contra h3
          obtain ⟨j, hj, h3⟩ := List.getElem_of_mem h1
          sorry

instance {n} : Implicant n (MODS n) where

  entails δ φ := sorry

  entails_correct := sorry

instance {n} : BoundedConjuction n (MODS n) where

  and φ ψ := sorry

  and_correct := sorry

instance {n} : SententialEntailment n (MODS n) where

  entails φ ψ := sorry

  entails_correct := sorry

instance {n} : OfPartialModel n (MODS n) where

  ofPartialModel M := ⟨M.vars', [M], by simp⟩

  ofPartialModel_correct := by
    simp [Formula.models, models, Formula.vars]

instance {n} : Rename n (MODS n) where

  rename := sorry

  rename_correct := sorry

instance {n} : ToCNF n (MODS n) where

  toCNF := sorry

  toCNF_correct := sorry

instance {n} : ToDNF n (MODS n) where

  toDNF := sorry

  toDNF_correct := sorry

end Validator.MODS
