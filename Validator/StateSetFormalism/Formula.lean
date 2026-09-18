module

public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Fin.Basic
public import Validator.StateSetFormalism.PartialModel

/-
Cannot compile inline/specializing declaration `disjunctionToCNF` as it uses `List.multiply` of
module `Validator.Basic` which must be imported publicly.
This limitation may be lifted in the future.
-/
public import Validator.Basic
public import Strips.PlanningTask

namespace Validator

open STRIPS (VarSet)

public section

/-! # Formulas
This file provides typeclasses for formulas and different operations these formulas can support.
Note that this file does not implement any of these operations, but it formalizes what these
operations should do.
-/

/-! ## Formula -/

/-- Type class for formulas with variables `Fin n`. The variables are ordered by ordering `<`. -/
class Formula n (R : Type) where
  /--
  The variables associated with the formula `φ`. Note that not all of these variables need
  to 'appear' in `φ`.
  -/
  vars : (φ : R) → VarSet n

  /-- The models of the formula `φ` -/
  models : (φ : R) → Models n

  /--
  If two assignments coincide on the variables of `φ`, then the second is a model of `φ`
  if the first one is a model of `φ`.
  -/
  models_equiv_right (φ : R) (M M' : Model n) :
    (∀ i ∈ vars φ, M i = M' i) → M ∈ models φ → M' ∈ models φ

/--
If two assignments `M` and `M'` coincide on the variables of `φ`, then `M` is a model of
`φ` iff `M'` is a model of `φ`.
-/
lemma Formula.models_equiv {n} {R} [h : Formula n R] {φ : R} {M M' : Model n}
    (h1 : ∀ i ∈ h.vars φ, M i = M' i) : M ∈ h.models φ ↔ M' ∈ h.models φ := by
  constructor
  · apply models_equiv_right
    exact h1
  · apply models_equiv_right
    grind

/-! ## Renaming -/

structure Renaming {n} (dom : VarSet n) where
  rename : Fin n → Fin n
  mono : StrictMonoOn rename dom
  --prop : ∀ i ∉ dom.toVarSet, rename i = i

lemma Renaming.ne {n} {dom : VarSet n} {r : Renaming dom} :
    ∀ i ∈ dom, ∀ j ∈ dom, i ≠ j → r.rename i ≠ r.rename j := by
  intro i hi j hj
  exact Set.InjOn.ne (StrictMonoOn.injOn r.mono) hi hj

-- TODO : the name is a bit misleading, since it does the inverse of the other rename functions
@[expose]
def Model.rename {n} {dom : VarSet n} (r : Renaming dom) (M : Model n) : Model n :=
  fun i ↦ M (r.rename i)

@[expose]
def Literal.rename {n} {dom : VarSet n} (r : Renaming dom) (l : Literal n) : Literal n :=
  ⟨r.rename l.var, l.isPos⟩

@[simp]
lemma Literal.models_rename {n dom} {r : Renaming dom} {l : Literal n} :
    (l.rename r).models = Model.rename r ⁻¹' l.models := by
  ext M
  simp only [rename, mem_models, Set.mem_preimage, Model.rename]

@[expose]
def Clause.rename {n} {dom : VarSet n} (r : Renaming dom) (γ : Clause n) : Clause n :=
  γ.map (Literal.rename r)

@[simp]
lemma Clause.models_rename {n dom} {r : Renaming dom} {γ : Clause n} :
    (γ.rename r).models = Model.rename r ⁻¹' γ.models := by
  ext M
  simp only [rename, mem_models, List.mem_map, exists_exists_and_eq_and, Literal.models_rename,
    Set.mem_preimage]

def Cube.rename {n} {dom : VarSet n} (r : Renaming dom) (δ : Cube n) : Cube n :=
  δ.map (Literal.rename r)

@[expose]
def CNF.rename {n} {dom : VarSet n} (r : Renaming dom) (φ : CNF n) : CNF n :=
  φ.map (Clause.rename r)

@[simp]
lemma CNF.mem_vars_rename {n} {dom : VarSet n} {r : Renaming dom} {φ : CNF n} {i} :
    i ∈ (φ.rename r).vars ↔ ∃ j ∈ φ.vars, i = r.rename j := by
  simp [rename, mem_vars, List.mem_map, Clause.rename, Clause.mem_vars,
    exists_exists_and_eq_and, Literal.rename, ↓existsAndEq, and_true]
  grind only

@[simp]
lemma CNF.models_rename {n} {dom : VarSet n} {r : Renaming dom} {φ : CNF n} :
    (φ.rename r).models = Model.rename r ⁻¹' φ.models := by
  ext M
  simp only [mem_models, Set.mem_preimage]
  simp only [rename, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp only [Clause.models_rename, Set.mem_preimage]

def VarSet.rename {n} {dom : VarSet n} (r : Renaming dom) (V : VarSet n) : VarSet n :=
  V.map r.rename

@[simp]
lemma VarSet.mem_rename {n} {dom : VarSet n} {r : Renaming dom} {V : VarSet n} {i} :
    i ∈ (VarSet.rename r V) ↔ ∃ j ∈ V, i = r.rename j := by
  simp [rename, VarSet.mem_map]

def PartialModel.rename {n} {dom : VarSet n} (r : Renaming dom) (M : PartialModel n)
    (h1 : M.vars ⊆ dom) : PartialModel n where
  pos := VarSet.rename r M.pos
  neg := VarSet.rename r M.neg
  disjoint := by
    have h3 := r.mono
    simp only [VarSet.inter_eq_empty_iff, VarSet.mem_rename, not_exists, not_and,
      forall_exists_index, and_imp]
    intro _ i hi rfl j hj
    apply Renaming.ne
    · apply h1
      simp [PartialModel.vars_eq, hi]
    · apply h1
      simp [PartialModel.vars_eq, hj]
    · have h2 := M.disjoint
      grind only [VarSet.inter_eq_empty_iff]

@[simp]
lemma PartialModel.mem_vars_rename {n dom} {r : Renaming dom} {M : PartialModel n} {h1 i} :
    i ∈ (M.rename r h1).vars ↔ ∃ j ∈ M.vars, i = r.rename j := by
  grind only [rename, vars_eq, VarSet.mem_union, VarSet.mem_rename]

@[simp]
lemma PartialModel.models_rename {n dom} {r : Renaming dom} {M : PartialModel n} {h1} :
    (M.rename r h1).models = M.models.preimage (Model.rename r) := by
  ext M'
  simp only [rename, mem_models', VarSet.mem_rename, forall_exists_index, and_imp, Set.mem_preimage,
    Model.rename]
  grind

namespace Formula

/-! ## Operations on Formulas -/
-- TODO : documentation

class Top n R [F : Formula n R] where

  top : R

  models_top : F.models top = Set.univ

class Bot n R [F : Formula n R] where

  bot : R

  vars_bot : F.vars bot = ∅

  models_bot : F.models bot = ∅

class Consistency n R [F : Formula n R] where

  consistent : (φ : R) → Bool

  consistent_iff φ : consistent φ ↔ (F.models φ).Nonempty

class ClausalEntailment n R [F : Formula n R] where

  entails : (φ : R) → (γ : Clause n) → Bool

  entails_iff φ γ : entails φ γ ↔ F.models φ ⊆ γ.models

class Implicant n R [F : Formula n R] where

  entails : (δ : Cube n) → (φ : R) → Bool

  entails_iff δ φ : entails δ φ ↔ δ.models  ⊆ F.models φ

class SententialEntailment n R [F : Formula n R] where

  entails : (φ ψ : R)  → Bool

  entails_iff φ ψ : entails φ ψ ↔ F.models φ ⊆ F.models ψ

class BoundedConjuction n R [F : Formula n R] where
  and : R → R → R

  models_and φ ψ : F.models (and φ ψ) = F.models φ ∩ F.models ψ

namespace BoundedConjuction

/--
The time complexity of `andList` is generally bad, therefore it should only be used
if the number of conjuncts is bounded.
-/
def andList {n} {R} [Formula n R] [Top n R] [h : BoundedConjuction n R] : List R → R
  | [] => Top.top n
  | [φ] => φ
  | φ :: ψ :: tail => h.and φ (h.andList (ψ :: tail))

lemma models_andList {n} {R} [F : Formula n R] [Top n R] [h : BoundedConjuction n R] {l} :
    models (h.andList l) = { M | ∀ φ ∈ l, M ∈ F.models φ } := by
  fun_induction andList
  · simp [Top.models_top]
  · simp
  · simp_all [models_and]
    grind

end BoundedConjuction

class BoundedDisjunction n R [F : Formula n R] where
  or : R → R → R

  models_or φ ψ : F.models (or φ ψ) = F.models φ ∪ F.models ψ

namespace BoundedDisjunction

/--
The timecomplexity of `andList` is generally bad, therefore it should only be used
if the number of conjuncts is bounded.
-/
def orList {n} {R} [Formula n R] [Bot n R] [h : BoundedDisjunction n R] : List R → R
  | [] => Bot.bot n
  | [φ] => φ
  | φ :: ψ :: tail => h.or φ (h.orList (ψ :: tail))

lemma models_orList {n} {R} [F : Formula n R] [Bot n R] [h : BoundedDisjunction n R] {l} :
    models (h.orList l) = { M | ∃ φ ∈ l, M ∈ F.models φ } := by
  fun_induction orList
  · simp [Bot.models_bot]
  · simp
  · ext M
    simp_all [models_or]

end BoundedDisjunction

/- Alternative to OfPartialModel, currently not used.
class OfCube n R [F : Formula n R] where
  ofCube : Cube n → R

  ofCube_correct {δ} :
    F.models (ofCube δ) = δ.models ∧ F.vars (ofCube δ) = _
-/

class OfPartialModel n R [F : Formula n R] where
  ofPartialModel : PartialModel n → R

  vars_ofPartialModel M : F.vars (ofPartialModel M) = M.vars

  models_ofPartialModel M : F.models (ofPartialModel M) = M.models

/-- Renaming consistent with order -/
class Rename n R [F : Formula n R] where
  --rename (φ : R) (r : { i : Fin n // i ∈ (F.vars φ).val } → Fin n) (h : StrictMono r) : R
  rename (φ : R) {V : VarSet n} (f : Renaming V) (h1 : F.vars φ ⊆ V) : R

  vars_rename φ V (r : Renaming V) h : ∀ i, i ∈ F.vars (rename φ r h) ↔ i ∈ r.rename '' F.vars φ

  models_rename φ V (r : Renaming V) h : F.models (rename φ r h) =  Model.rename r ⁻¹' F.models φ

namespace Rename

lemma mem_rename_models {n R} [F : Formula n R] [Rename n R] {φ V} {r : Renaming V} {h M} :
    M ∈ F.models (rename φ r h) ↔ M.rename r ∈ F.models φ := by
  simp only [models_rename, Set.mem_preimage]

end Rename

class ToCNF n R [F : Formula n R] where
  toCNF : R → CNF n

  models_toCNF φ : (toCNF φ).models = F.models φ

namespace ToCNF

def disjunctionToCNF {n} {R} [Formula n R] [ToCNF n R] (l : List R) : CNF n :=
  (l.map toCNF).multiply

lemma models_disjunctionToCNF {n} {R} [F : Formula n R] [h : ToCNF n R] {φs} :
    (disjunctionToCNF φs).models = { M | ∃ φ ∈ φs, M ∈ F.models φ } := by
  ext M
  simp only [disjunctionToCNF, CNF.mem_models, Clause.mem_models, ← models_toCNF,
    Set.mem_ofPred_eq]
  induction φs with
  | nil => simp
  | cons φ φs ih =>
    constructor
    · simp
      grind
    · simp only [forall_exists_index, and_imp, List.mem_cons, exists_eq_or_imp, List.map_cons,
        List.multiply_cons, List.mem_flatMap, List.mem_map] at ⊢ ih
      intro h1 _ γ1 hγ1 γ2 hγ2 rfl
      grind only [= List.mem_append]

/-- Transform ¬x to a DNF formula by translating x to a CNF-formula and applying De Morgans laws. -/
def negToDNF {n} {R} [Formula n R] [h : ToCNF n R] (φ : R) : DNF n :=
  (h.toCNF φ).map Clause.neg

lemma models_negToDNF {n} {R} [F : Formula n R] [h : ToCNF n R] {φ} :
    (negToDNF φ).models = (F.models φ)ᶜ := by
  ext M
  simp only [negToDNF, DNF.mem_models, List.mem_map, exists_exists_and_eq_and, ← models_toCNF,
    Set.mem_compl_iff]
  grind only [CNF.mem_models, !Clause.models_neg, Set.mem_compl_iff]

end ToCNF

class ToDNF n R [F : Formula n R] where
  toDNF : R → DNF n

  models_toDNF φ : (toDNF φ).models = F.models φ

namespace ToDNF

def conjunctionToDNF {n} {R} [Formula n R] [ToDNF n R] (l : List R) : DNF n :=
  (l.map toDNF).multiply

lemma models_conjunctionToDnF {n} {R} [F : Formula n R] [h : ToDNF n R] {φs} :
    (conjunctionToDNF φs).models = { M | ∀ φ ∈ φs, M ∈ F.models φ } := by
  ext M
  simp only [conjunctionToDNF, DNF.mem_models, Cube.mem_models, ← models_toDNF, Set.mem_ofPred_eq]
  induction φs with
    | nil => simp
    | cons φ φs ih =>
      simp
      grind only

/-- Transform ¬x to a CNF formula by translating x to a DNF-formula and applying De Morgans laws. -/
def negToCNF {n} {R} [Formula n R] [h : ToDNF n R] (φ : R) : CNF n :=
  (h.toDNF φ).map Cube.neg

lemma models_negToCNF {n} {R} [F : Formula n R] [h : ToDNF n R] {φ} :
    (negToCNF φ).models = (F.models φ)ᶜ := by
  ext M
  simp only [negToCNF, CNF.mem_models, List.mem_map, forall_exists_index, and_imp,
    ← models_toDNF]
  grind only [Set.mem_compl_iff, DNF.mem_models, !Cube.models_neg]
