import Mathlib.Data.Fin.Parity

import Validator.PlanningTask.Basic
import Validator.Basic

/-! # Formulas
This file provides typeclasses for formulas and different operations these formulas can support.
Note that this file does not implement any of these operations, but it formalizes what these
operations should do. More specifically the file contains
* some functions for working with `Validator.VarSet'`,
* definitions and methods for models, partial models,
  literals, clauses, cubes, CNF-formulas and DNF-formulas, and
* type classes for formulas and various operations on formulas.
-/

/-! ## VarSet' -/
namespace Validator.VarSet'

def empty {n} : VarSet' n := ⟨[], by simp⟩

def union {n} (V V' : VarSet' n) : VarSet' n :=
  ⟨List.mergeDedup V V', List.mergeDedup_sorted V.prop V'.prop⟩

@[simp]
lemma mem_union {n} {V V' : VarSet' n} {i} :
  i ∈ (V.union V').val ↔ i ∈ V.val ∨ i ∈ V'.val :=
  by
    simp [union, List.mem_mergeDedup]

end VarSet'

namespace Formula
/-! ## Model and PartialModel -/

/--
`Model` is usually in the in the context of a formula, where it represents a model of this formula,
i.e. an assignment of variables making the formula true.
It is used to show the correctness of operations.
-/
abbrev Model n := Fin n → Prop

/-- A set of models. -/
abbrev Models n := Set (Model n)

/-- Partial models are partial assignments. In contrast to `Model`, these are used at runtime. -/
abbrev PartialModel {n} (V : VarSet' n) := BitVec V.val.length

/-- All models corresponding to to partial model `M`. -/
def PartialModel.models {n} {V : VarSet' n} (M : PartialModel V) : Models n :=
  { M' | ∀ i : Fin V.val.length, M' ⟨V.val[i], by simp⟩ ↔ M[i] }

/-! ## Literal -/

/--
A Literal is a variable `i` (represented by `(i, true)`) or
its negation (represented by `(i, false)`).
-/
abbrev Literal n := Fin n × Bool

def Literal.models {n} : Literal n → Models n
| (i, true) => { M | M i }
| (i, false) => { M | ¬M i }

lemma Literal.mem_models {n} (l : Literal n) M : M ∈ l.models ↔ (M l.1 ↔ l.2) :=
  by
    simp [models]
    split
    all_goals simp

/-! ## Clause -/

/-- A clause is a disjuction of literals. -/
abbrev Clause n := List (Literal n)

namespace Clause

def models {n} (γ : Clause n) : Models n :=
  { M | ∃ l ∈ γ, M ∈ l.models }

@[simp]
lemma mem_models {n} (γ : Clause n) M :
  M ∈ γ.models ↔ ∃ l ∈ γ, M ∈ l.models :=
  by simp [Clause.models]

@[simp]
lemma models_append {n} (γ1 γ2 : Clause n) :
  models (γ1 ++ γ2) = γ1.models ∪ γ2.models :=
  by
    ext M
    simp [models, -Prod.forall]
    grind

end Clause

/-! ## Cube -/

/-- A cube is a conjunction of literals. -/
abbrev Cube n := List (Literal n)

namespace Cube

def models {n} (δ : Cube n) : Models n :=
  { M | ∀ l ∈ δ, M ∈ l.models }

@[simp]
lemma mem_models {n} (δ : Cube n) M :
  M ∈ δ.models ↔ ∀ l ∈ δ, M ∈ l.models :=
  by simp [models]

@[simp]
lemma models_append {n} (δ1 δ2 : Cube n) :
  models (δ1 ++ δ2) = δ1.models ∩ δ2.models :=
  by
    ext M
    simp [models, -Prod.forall]
    grind

end Cube

/-! ## CNF -/

/-- A CNF-formula is a conjunction of clauses. -/
abbrev CNF n := List (Clause n)

namespace CNF

def models {n} (φ : CNF n) : Models n :=
  { M | ∀ γ ∈ φ, ∃ l ∈ γ, M ∈ l.models }

@[simp]
lemma mem_models {n} (φ : CNF n) {M} : M ∈ φ.models ↔ ∀ γ ∈ φ, ∃ l ∈ γ, M ∈ l.models :=
  by
    simp [models]

def vars {n} (φ : CNF n) : VarSet n :=
  { i | ∃ γ ∈ φ, ∃ v ∈ γ, v.fst = i }

@[simp]
lemma mem_vars {n} (φ : CNF n) {i} : i ∈ φ.vars ↔ ∃ γ ∈ φ, ∃ v ∈ γ, v.fst = i :=
  by
    simp [vars]

@[simp]
lemma forall_iff_subset_models {n} {φ : CNF n} {Ms} :
  (∀ γ ∈ φ, Ms ⊆ γ.models) ↔ Ms ⊆ φ.models :=
  by
    simp [models, Set.subset_def, -Prod.exists]
    grind

lemma models_equiv_right {n} {φ : CNF n} {M M' : Formula.Model n} :
  (∀ i ∈ vars φ, M i = M' i) → M ∈ models φ → M' ∈ models φ :=
  by
    simp [Literal.mem_models]
    grind

end CNF

/-! ## DNF -/

/-- A DNF-formula is a conjunction of cubes. -/
abbrev DNF n := List (Cube n)

def DNF.models {n} (φ : DNF n) : Models n :=
  { M |  ∃ δ ∈ φ, ∀ l ∈ δ, M ∈ l.models }

@[simp]
lemma DNF.mem_models {n} (φ : DNF n) {M} : M ∈ φ.models ↔ ∃ δ ∈ φ, ∀ l ∈ δ, M ∈ l.models :=
  by
    simp [models]

@[simp]
lemma DNF.exists_iff_models_subset {n} {φ : DNF n} {Ms} :
  (∀ δ ∈ φ, δ.models ⊆ Ms) ↔ φ.models ⊆ Ms :=
  by
    simp [DNF.models, Set.subset_def, -Prod.forall]
    grind

end Formula

/-! ## Formula -/

/-- Type class for formulas with variables `Fin n`. The variables are ordered by ordering `<`. -/
class Formula n (R : Type) where
  /--
  The variables associated with the formula `φ`. Note that not all of these variables need
  to 'appear' in `φ`.
  -/
  vars : (φ : R) → VarSet' n

  /-- The models of the formula `φ` -/
  models : (φ : R) → Formula.Models n

  /--
  If two assignments coincide on the variables of `φ`, then the second is a model of `φ`
  if the first one is a model of `φ`.
  -/
  models_equiv_right (φ : R) (M M' : Formula.Model n) :
    (∀ i ∈ (vars φ).val, M i = M' i) → M ∈ models φ → M' ∈ models φ

namespace Formula

/--
If two assignments `M` and `M'` coincide on the variables of `φ`, then `M` is a model of
`φ` iff `M'` is a model of `φ`.
-/
lemma models_equiv {n} {R} [h : Formula n R] {φ : R} {M M' : Model n}
  (h1 : ∀ i ∈ (h.vars φ).val, M i = M' i) : M ∈ h.models φ ↔ M' ∈ h.models φ :=
  by
    constructor
    · apply models_equiv_right
      exact h1
    · apply models_equiv_right
      grind

/-! ## Operations on Formulas -/
-- TODO : documentation

class Top n R [F : Formula n R] where

  top : R

  top_correct : F.models top = Set.univ

class Bot n R [F : Formula n R] where

  bot : R

  bot_correct : F.models bot = ∅ ∧ F.vars bot = VarSet'.empty

/- TODO : remove
class ModelTesting n R [F : Formula n R] where

  isModel : (φ : R) → PartialModel (F.vars φ) → Bool

  isModel_correct {φ M} : isModel φ M ↔ M.models ⊆ models φ
-/

class ClausalEntailment n R [F : Formula n R] where

  entails : (φ : R) → (γ : Clause n) → Bool

  entails_correct {φ γ} : entails φ γ ↔ F.models φ ⊆ γ.models

class Implicant n R [F : Formula n R] where

  entails : (δ : Cube n) → (φ : R) → Bool

  entails_correct {δ φ} : entails δ φ ↔ δ.models  ⊆ F.models φ

class SententialEntailment n R [F : Formula n R] where

  entails : (φ ψ : R)  → Bool

  entails_correct {φ ψ} : entails φ ψ ↔ F.models φ ⊆ F.models ψ

class BoundedConjuction n R [F : Formula n R] where
  and : R → R → R

  and_correct {φ ψ} : F.models (and φ ψ) = F.models φ ∩ F.models ψ

namespace BoundedConjuction

/--
The time complexity of `andList` is generally bad, therefore it should only be used
if the number of conjuncts is bounded.
-/
def andList {n} {R} [Formula n R] [Top n R] [h : BoundedConjuction n R] : List R → R
| [] => Top.top n
| [φ] => φ
| φ :: ψ :: tail => h.and φ (h.andList (ψ :: tail))

lemma andList_correct {n} {R} [F : Formula n R] [Top n R] [h : BoundedConjuction n R] {l} :
  models (h.andList l) = { M | ∀ φ ∈ l, M ∈ F.models φ } :=
  by
    fun_induction andList
    · simp [Top.top_correct]
    · simp
    · simp_all [and_correct]
      grind

end BoundedConjuction

class BoundedDisjunction n R [F : Formula n R] where
  or : R → R → R

  or_correct {φ ψ} : F.models (or φ ψ) = F.models φ ∪ F.models ψ

namespace BoundedDisjunction

/--
The timecomplexity of `andList` is generally bad, therefore it should only be used
if the number of conjuncts is bounded.
-/
def orList {n} {R} [Formula n R] [Bot n R] [h : BoundedDisjunction n R] : List R → R
| [] => Bot.bot n
| [φ] => φ
| φ :: ψ :: tail => h.or φ (h.orList (ψ :: tail))

lemma orList_correct {n} {R} [F : Formula n R] [Bot n R] [h : BoundedDisjunction n R] {l} :
  models (h.orList l) = { M | ∃ φ ∈ l, M ∈ F.models φ } :=
  by
    fun_induction orList
    · simp [Bot.bot_correct]
    · simp
    · ext M
      simp_all [or_correct]

end BoundedDisjunction

/- Alternative to OfPartialModel, currently not used.
class OfCube n R [F : Formula n R] where
  ofCube : Cube n → R

  ofCube_correct {δ} :
    F.models (ofCube δ) = δ.models ∧ F.vars (ofCube δ) = sorry
-/

class OfPartialModel n R [F : Formula n R] where
  ofPartialModel : (V : VarSet' n) → PartialModel V → R

  ofPartialModel_correct {V M} :
    F.models (ofPartialModel V M) = M.models ∧ F.vars (ofPartialModel V M) = V

/-- Renaming consistent with order -/
class Renaming n R [F : Formula n R] where
  rename : (φ : R) → (vars' : VarSet' n) → vars'.val.length = (F.vars φ).val.length → R

  rename_correct {φ vars' h} :
    F.vars (rename φ vars' h) = vars' ∧ F.models (rename φ vars' h) =
      { M | ∃ M' ∈ F.models φ, ∀ i : Fin vars'.val.length, M vars'.val[i] ↔ M' (F.vars φ).val[i] }

def Renaming.renameModel {n}
  (V V' : VarSet' n) (h : V'.val.length = V.val.length) (M : Model n) : Model n :=
  fun i ↦
    match V.val.finIdxOf? i with
    | none => M i
    | some j => M (V'.val[j]'(by omega))

-- TODO : replace rename_correct by this?
lemma Renaming.mem_rename_models {n R} [F : Formula n R] [Renaming n R] {φ vars' h M} :
  M ∈ F.models (rename φ vars' h) ↔ renameModel (F.vars φ) vars' (by simp [h]) M ∈ F.models φ :=
  by
    simp [rename_correct]
    constructor
    · rintro ⟨M', h1, h2⟩
      unfold renameModel
      rw [Formula.models_equiv]
      · exact h1
      · simp
        intro i hi
        split
        · grind
        · rename_i j h
          simp_all
          grind
    · intro h1
      use renameModel (vars φ) vars' h M, h1
      simp [renameModel]
      intro i
      split
      · grind
      · rename_i j h
        simp_all
        rcases h with ⟨h1, h2⟩
        have h3 := List.Sorted.nodup (F.vars φ).prop
        apply (List.Nodup.getElem_inj_iff h3).1 at h1
        simp_all only

class ToCNF n R [F : Formula n R] where
  toCNF : R → CNF n

  toCNF_correct {φ} : (toCNF φ).models = F.models φ

namespace ToCNF

def disjunctionToCNF {n} {R} [Formula n R] [ToCNF n R] (l : List R) : CNF n :=
  (l.map toCNF).multiply

lemma disjunctionToCNF_correct {n} {R} [F : Formula n R] [h : ToCNF n R] {φs} :
  (disjunctionToCNF φs).models = { M | ∃ φ ∈ φs, M ∈ F.models φ } :=
  by
    ext M
    simp [disjunctionToCNF, -Prod.exists, ← toCNF_correct]
    constructor
    · induction φs with
      | nil => simp
      | cons φ φs ih =>
        simp [-Prod.exists]
        grind
    · induction φs with
      | nil => simp
      | cons φ φs ih =>
        simp [-Prod.exists] at ⊢ ih
        intro h1 _ γ1 hγ1 γ2 hγ2 rfl
        rcases h1 with h1 | ⟨φ', h1, h2⟩
        · grind
        · specialize ih φ' h1 h2 γ2 hγ2
          grind

end ToCNF

class ToDNF n R [F : Formula n R] where
  toDNF : R → DNF n

  toDNF_correct {φ} : (toDNF φ).models = F.models φ

namespace ToDNF

def conjunctionToDNF {n} {R} [Formula n R] [ToDNF n R] (l : List R) : DNF n :=
  (l.map toDNF).multiply

lemma conjunctionToDnF_correct {n} {R} [F : Formula n R] [h : ToDNF n R] {φs} :
  (conjunctionToDNF φs).models = { M | ∀ φ ∈ φs, M ∈ F.models φ } :=
  by
    ext M
    simp [conjunctionToDNF, ← toDNF_correct, -Prod.forall]
    induction φs with
      | nil => simp
      | cons φ φs ih =>
        simp [-Prod.forall]
        grind

end Validator.Formula.ToDNF
