module

public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Fin.Basic

/-
Cannot compile inline/specializing declaration `disjunctionToCNF` as it uses `List.multiply` of
module `Validator.Basic` which must be imported publicly.
This limitation may be lifted in the future.
-/
public import Validator.Basic
public import Strips.PlanningTask

/-! # Formulas
This file provides typeclasses for formulas and different operations these formulas can support.
Note that this file does not implement any of these operations, but it formalizes what these
operations should do. More specifically the file contains
* definitions and methods for models, partial models,
  literals, clauses, cubes, CNF-formulas and DNF-formulas, and
* type classes for formulas and various operations on formulas.
-/

public section

open STRIPS (VarSet)

namespace Validator.Formula

/-! ## Model -/

/--
`Model` is usually in the in the context of a formula, where it represents a model of this formula,
i.e. an assignment of variables making the formula true.
It is used to show the correctness of operations.
-/
abbrev Model n := Fin n → Prop

/-- A set of models. -/
abbrev Models n := Set (Model n)

/-! ## Literal -/

/--
A Literal is a variable `i` (represented by `(i, true)`) or
its negation (represented by `(i, false)`).
-/
@[unbox]
structure Literal (n : ℕ) where
  var : Fin n
  isPos : Bool
  deriving DecidableEq

namespace Literal

def models {n} : Literal n → Models n
  | ⟨i, true⟩ => { M | M i }
  | ⟨i, false⟩ => { M | ¬M i }

lemma mem_models {n} (l : Literal n) M : M ∈ l.models ↔ (M l.var ↔ l.isPos) := by
  simp [models]
  split
  all_goals simp

@[expose]
def negate {n} (l : Literal n) : Literal n :=
  ⟨l.var, !l.isPos⟩

@[simp]
lemma models_negate {n} (l : Literal n) : l.negate.models = l.modelsᶜ := by
  simp only [models, negate]
  grind only [= Set.mem_compl_iff, usr Set.mem_ofPred_eq]

lemma eq_or_eq_negate_iff_var_eq {n} {l l' : Literal n} :
    l.var = l'.var ↔ l = l' ∨ l = l'.negate := by
  rcases l with ⟨v, b⟩
  rcases l' with ⟨v', b'⟩
  have := Bool.eq_or_eq_not b b'
  grind only [negate]

end Literal

/-! ## Clause -/

/-- A clause is a disjuction of literals. -/
abbrev Clause n := List (Literal n)

namespace Clause

def models {n} (γ : Clause n) : Models n :=
  { M | ∃ l ∈ γ, M ∈ l.models }

@[simp]
lemma mem_models {n} (γ : Clause n) M : M ∈ γ.models ↔ ∃ l ∈ γ, M ∈ l.models := by
  simp [models]

@[simp]
lemma models_nil {n} : models ([] : Clause n) = ∅ := by
  simp only [models, List.not_mem_nil, false_and, exists_false, Set.ofPred_false]

@[simp]
lemma models_append {n} (γ1 γ2 : Clause n) : models (γ1 ++ γ2) = γ1.models ∪ γ2.models := by
  ext M
  grind only [models, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]

def vars {n} (γ : Clause n) : VarSet n :=
  VarSet.ofList (γ.map Literal.var)

@[simp]
lemma mem_vars {n} (γ : Clause n) {i} : i ∈ γ.vars ↔ ∃ l ∈ γ, l.var = i := by
  simp only [vars, VarSet.mem_ofList, List.mem_map]

@[simp]
lemma vars_cons {n} (γ : Clause n) {l} : Clause.vars (l :: γ) = γ.vars.insert l.var := by
  rw [SetLike.ext_iff]
  grind only [vars, VarSet.mem_insert, List.map_cons, VarSet.mem_ofList, List.mem_cons]

end Clause

/-! ## Cube -/

/-- A cube is a conjunction of literals. -/
abbrev Cube n := List (Literal n)

namespace Cube

def models {n} (δ : Cube n) : Models n :=
  { M | ∀ l ∈ δ, M ∈ l.models }

@[simp]
lemma mem_models {n} (δ : Cube n) M : M ∈ δ.models ↔ ∀ l ∈ δ, M ∈ l.models := by
  simp [models]

@[simp]
lemma models_append {n} (δ1 δ2 : Cube n) : models (δ1 ++ δ2) = δ1.models ∩ δ2.models := by
  ext M
  grind only [models, List.mem_append, Set.mem_ofPred_eq, Set.mem_inter_iff]

@[simp]
lemma models_nil {n} : models ([] : Cube n) = Set.univ := by
  simp only [models, List.not_mem_nil, IsEmpty.forall_iff, implies_true, Set.ofPred_true]

@[simp]
lemma models_cons {n l} (δ : Cube n) : models (l :: δ) = l.models ∩ δ.models := by
  ext M
  simp only [models, List.mem_cons, forall_eq_or_imp, Set.mem_ofPred_eq, Set.mem_inter_iff]

def vars {n} (δ : Cube n) : VarSet n :=
  VarSet.ofList (δ.map Literal.var)

@[simp]
lemma mem_vars {n} (δ : Cube n) i : i ∈ δ.vars ↔ ∃ l ∈ δ, i = l.var := by
  grind only [vars, Literal, VarSet.mem_ofList, List.mem_map]

@[simp]
lemma vars_cons {n} (δ : Cube n) {l} : Cube.vars (l :: δ) = δ.vars.insert l.var := by
  rw [SetLike.ext_iff]
  grind only [vars, VarSet.mem_insert, List.map_cons, VarSet.mem_ofList, List.mem_cons]

-- TODO : remove
lemma vars_append {n} (δ δ' : Cube n) : Cube.vars (δ ++ δ') = δ.vars ∪ δ'.vars := by
  rw [SetLike.ext_iff]
  grind only [vars, VarSet.mem_union, VarSet.mem_ofList, = List.map_append, = List.mem_append]

def consistent {n} (δ : Cube n) : Bool :=
  δ.all fun l ↦ l.negate ∉ δ

lemma consistent_iff {n} {δ : Cube n} : δ.consistent ↔ δ.models ≠ ∅ := by
  simp only [consistent, decide_not, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, ne_eq, Set.ext_iff, mem_models, Set.mem_empty_iff_false, iff_false,
    not_forall, not_exists, not_not, Literal.mem_models]
  constructor
  · intro h1
    use fun i ↦ ⟨i, true⟩ ∈ δ
    rintro ⟨v, b⟩ h2
    grind only [Literal.negate]
  · rintro ⟨M, h1⟩ l h2 h3
    have h4 := h1 l.negate h3
    simp only [Literal.negate] at h4
    grind only

end Cube

/-- The negation of a clause -/
def Clause.neg {n} (γ : Clause n) : Cube n :=
  γ.map Literal.negate

lemma Clause.models_neg {n} {γ : Clause n} : γ.neg.models = γ.modelsᶜ := by
  simp [neg, Cube.models, Clause.models, compl]

/-- The negation of a cube -/
def Cube.neg {n} (δ : Cube n) : Clause n :=
  δ.map Literal.negate

lemma Cube.models_neg {n} {δ : Cube n} : δ.neg.models = δ.modelsᶜ := by
  simp [neg, Cube.models, Clause.models, compl]

/-! ## CNF -/

/-- A CNF-formula is a conjunction of clauses. -/
abbrev CNF n := List (Clause n)

namespace CNF

def models {n} (φ : CNF n) : Models n :=
  { M | ∀ γ ∈ φ, M ∈ γ.models }

@[simp]
lemma mem_models {n} (φ : CNF n) {M} : M ∈ φ.models ↔ ∀ γ ∈ φ, M ∈ γ.models := by
  simp [models]

@[simp]
lemma models_nil {n} : CNF.models ([] : CNF n) = Set.univ := by
  simp only [models, List.not_mem_nil, IsEmpty.forall_iff, implies_true, Set.ofPred_true]

@[simp]
lemma models_cons {n} (φ : CNF n) {γ} : CNF.models (γ :: φ) = γ.models ∩ φ.models := by
  simp only [models, List.mem_cons, Clause.models, Set.mem_ofPred_eq, forall_eq_or_imp,
    Set.inter_def]

@[simp]
lemma models_append {n} (φ ψ : CNF n) : (φ ++ ψ).models = φ.models ∩ ψ.models := by
  ext M
  simp
  grind

lemma models_mem_empty {n} (φ : CNF n) (h : [] ∈ φ) : φ.models = ∅ := by
  grind only [mem_models, = Set.mem_empty_iff_false, Clause.mem_models, ← List.not_mem_nil]

def vars {n} (φ : CNF n) : VarSet n :=
  φ.foldr (fun γ V ↦ V ∪ γ.vars) ∅

@[simp]
lemma mem_vars {n} (φ : CNF n) {i} : i ∈ φ.vars ↔ ∃ γ ∈ φ, i ∈ γ.vars := by
  induction φ with
  | nil => grind only [vars, List.foldr_nil, VarSet.mem_empty, List.not_mem_nil]
  | cons γ φ ih =>
    grind only [vars, Clause.mem_vars, List.foldr_cons, VarSet.mem_union, List.mem_cons]

@[simp]
lemma vars_cons {n γ} {φ : CNF n} : CNF.vars (γ :: φ) = γ.vars ∪ φ.vars := by
  simp only [SetLike.ext_iff, mem_vars, List.mem_cons, Clause.mem_vars, exists_eq_or_imp,
    VarSet.mem_union, implies_true]

@[simp]
lemma forall_iff_subset_models {n} {φ : CNF n} {Ms} : (∀ γ ∈ φ, Ms ⊆ γ.models) ↔ Ms ⊆ φ.models := by
  grind only [Set.subset_def, Clause.mem_models, models, Set.mem_ofPred_eq]

lemma models_equiv_right {n} {φ : CNF n} {M M' : Formula.Model n} :
    (∀ i ∈ vars φ, M i = M' i) → M ∈ models φ → M' ∈ models φ := by
  simp [Literal.mem_models]
  grind

end CNF

/-! ## DNF -/

/-- A DNF-formula is a conjunction of cubes. -/
abbrev DNF n := List (Cube n)

def DNF.models {n} (φ : DNF n) : Models n :=
  { M |  ∃ δ ∈ φ, M ∈ δ.models }

@[simp]
lemma DNF.mem_models {n} (φ : DNF n) {M} : M ∈ φ.models ↔ ∃ δ ∈ φ, M ∈ δ.models := by
  simp [models]

@[simp]
lemma DNF.exists_iff_models_subset {n} {φ : DNF n} {Ms} :
    (∀ δ ∈ φ, δ.models ⊆ Ms) ↔ φ.models ⊆ Ms := by
  grind only [Set.subset_def, Cube.mem_models, models, Set.mem_ofPred_eq]

/-! ## PartialModel -/
/-- Partial models are partial assignments. In contrast to `Model`, these are used at runtime. -/
structure PartialModel (n : ℕ) where
  pos : VarSet n
  neg : VarSet n
  disjoint : pos ∩ neg = ∅
  deriving DecidableEq

namespace PartialModel

@[simps]
instance {n} : Membership (Literal n) (PartialModel n) where
  mem M
  | ⟨i, true⟩ => i ∈ M.pos
  | ⟨i, false⟩ => i ∈ M.neg

lemma mem_iff {n} (M : PartialModel n) l :
    l ∈ M ↔ l.var ∈ M.pos ∧ l.isPos ∨ l.var ∈ M.neg ∧ ¬l.isPos := by
  rw [mem_def]
  grind only

instance {n l} {M : PartialModel n} : Decidable (l ∈ M) := by
  rw [mem_def]
  split
  all_goals
    exact VarSet.instDecidableMemFin

def vars {n} (M : PartialModel n) : VarSet n :=
  M.pos ∪ M.neg

lemma vars_eq {n} (M : PartialModel n) : M.vars = M.pos ∪ M.neg := (rfl)

lemma mem_vars {n i} {M : PartialModel n} : i ∈ M.vars ↔ ∃ l ∈ M, l.var = i := by
  simp only [vars_eq, VarSet.mem_union, mem_iff]
  constructor
  · rintro (h | h)
    · use ⟨i, true⟩; grind only
    · use ⟨i, false⟩; grind only
  · grind only

/-- All models corresponding to to partial model `M`. -/
def models {n} (M : PartialModel n) : Models n :=
  { M' | (∀ i ∈ M.pos, M' i) ∧ (∀ i ∈ M.neg, ¬ M' i) }

lemma mem_models' {n} (M : PartialModel n) {M'} :
    M' ∈ M.models ↔ (∀ i ∈ M.pos, M' i) ∧ (∀ i ∈ M.neg, ¬ M' i) := by
  simp [models]

lemma mem_models {n} {M : PartialModel n} {M'} : M' ∈ M.models ↔ ∀ l ∈ M, M' ∈ l.models := by
  simp only [models, Set.mem_ofPred_eq, Literal.models]
  constructor
  · grind [mem_def]
  · intro h1
    constructor
    · intro i hi
      specialize h1 ⟨i, true⟩ hi
      simp_all only [Set.mem_ofPred_eq]
    · intro i hi
      specialize h1 ⟨i, false⟩ hi
      simp_all only [Set.mem_ofPred_eq, not_false_eq_true]

lemma models_nonempty {n} (M : PartialModel n) : M.models.Nonempty := by
  use fun i ↦ ⟨i, true⟩ ∈ M
  simp only [mem_models, Literal.mem_models, mem_def]
  intro l
  split
  case h_1 l i => tauto
  case h_2 l i =>
    have := M.disjoint
    simp_all only [SetLike.ext_iff, VarSet.mem_inter, VarSet.mem_empty, iff_false, not_and,
      Bool.false_eq_true]
    grind only [mem_def]

-- TODO : remove?
lemma subset_models_of_mem {n} {M : PartialModel n} {l} : l ∈ M →  M.models ⊆ l.models := by
  simp [Set.subset_def, mem_models]
  grind

def empty {n} : PartialModel n :=
  ⟨∅, ∅, by simp⟩

@[simp]
lemma vars_empty {n} : (@empty n).vars = ∅ := by
  simp only [empty, vars_eq, VarSet.union_empty]

@[simp]
lemma models_empty {n} : (@empty n).models = Set.univ := by
  simp [empty, Set.ext_iff, mem_models]
  grind

/-- Returns none if the negation of the literal already occurs in M -/
def insert {n} (M : PartialModel n) : Literal n → Option (PartialModel n)
  | ⟨i, true⟩ =>
    if h : i ∈ M.neg then
      none
    else
      some { M with
        pos := M.pos.insert i
        disjoint := by
          have := M.disjoint
          grind only [VarSet.inter_eq_empty_iff, VarSet.mem_insert]
        }
  | ⟨i, false⟩ =>
    if h : i ∈ M.pos then
      none
    else
      some { M with
        neg := M.neg.insert i
        disjoint := by
          have := M.disjoint
          grind only [VarSet.inter_eq_empty_iff, VarSet.mem_insert]
        }

@[simp]
lemma insert_eq_none_iff {n} {M : PartialModel n} {l} : M.insert l = none ↔ l.negate ∈ M := by
  simp [mem_def, insert, Literal.negate]
  grind

@[simp]
lemma insert_eq_some_iff {n} {M M' : PartialModel n} {l} :
    M.insert l = some M' ↔ l.negate ∉ M ∧ ∀ l', l' ∈ M' ↔ l' ∈ M ∨ l' = l := by
  simp only [insert, mem_def, Literal.negate]
  split
  all_goals
    simp only [Option.dite_none_left_eq_some, Option.some.injEq]
    constructor
    · grind only [VarSet.mem_insert]
    · rintro ⟨h1, h2⟩
      use h1
      congr 1
      all_goals
        simp only [SetLike.ext_iff, VarSet.mem_insert]
        intro i
        have h3 := h2 ⟨i, false⟩
        specialize h2 ⟨i, true⟩
        grind only

lemma vars_insert {n} {M M' : PartialModel n} {l} (h : M.insert l = some M') :
    M'.vars = M.vars.insert l.var := by
  have ⟨h1, h2⟩ := insert_eq_some_iff.1 h
  simp only [SetLike.ext_iff, mem_vars, h2, VarSet.mem_insert]
  grind

lemma models_insert {n} {M M' : PartialModel n} {l} :
    M.insert l = some M' → M'.models = M.models ∩ l.models := by
  simp only [insert_eq_some_iff, Set.ext_iff, mem_models, Set.mem_inter_iff]
  grind

def foldl {α n} (f : α → Literal n → α) (init : α) (M : PartialModel n) : α :=
  M.pos.foldl (fun a i ↦ f a ⟨i, true⟩) (M.neg.foldl (fun a i ↦ f a ⟨i, false⟩) init)

lemma foldl_cons {α n} {M : PartialModel n} {f : Literal n → α} {a} :
    a ∈ M.foldl (fun a l ↦ f l :: a) [] ↔ ∃ l ∈ M, a = f l := by
  simp only [foldl, VarSet.foldl_cons, List.not_mem_nil, or_false, mem_def]
  grind

def toCNF {n} (M : PartialModel n) : CNF n :=
  M.foldl (fun φ l ↦ [l] :: φ) []

lemma mem_toCNF {n} {M : PartialModel n} {γ} : γ ∈ M.toCNF ↔ ∃ l ∈ M, γ = [l] := by
  simp [toCNF, foldl_cons, mem_def]

lemma models_toCNF {n} {M : PartialModel n} : M.toCNF.models = M.models := by
  ext M'
  simp only [CNF.mem_models, mem_toCNF, Clause.mem_models, forall_exists_index, and_imp,
    mem_models]
  grind only [= List.mem_cons, ← List.not_mem_nil]

def toCube {n} (M : PartialModel n) : Cube n :=
  M.foldl (fun δ l ↦ l :: δ) []

@[simp]
lemma vars_toCube {n} {M : PartialModel n} : M.toCube.vars = M.vars := by
  simp [toCube, foldl_cons, mem_vars, SetLike.ext_iff, Cube.mem_vars]
  grind only

@[simp]
lemma models_toCube {n} {M : PartialModel n} : M.toCube.models = M.models := by
  ext M'
  simp [toCube, foldl_cons, mem_models]

end PartialModel

namespace Cube
/-- Translate `δ` to a partial model. Returns `none` if `δ` is inconsistent. -/
def toPartialModel {n} (δ : Cube n) : Option (PartialModel n) :=
  δ.foldlM PartialModel.insert PartialModel.empty

@[simp]
lemma toPartialModel_eq_none_iff {n} {δ : Cube n} :
    δ.toPartialModel = none ↔ δ.models = ∅ := by
  suffices h1 : ∀ M, δ.foldlM PartialModel.insert M = none ↔ δ.models ∩ M.models = ∅ by
    have := h1 PartialModel.empty
    simp_all only [PartialModel.models_empty, Set.inter_univ, toPartialModel]
  induction δ with
  | nil =>
    intro M
    have := M.models_nonempty
    simp_all only [List.foldlM_nil, Option.pure_def, reduceCtorEq, models, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, Set.ofPred_true, Set.univ_inter, Set.nonempty_iff_ne_empty]
  | cons l δ' ih =>
    intro M
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_none_iff, models_cons, ih]
    cases h1 : M.insert l with
    | none =>
      simp only [reduceCtorEq, IsEmpty.forall_iff, implies_true, Set.inter_assoc, true_iff]
      rw [PartialModel.insert_eq_none_iff] at h1
      apply PartialModel.subset_models_of_mem at h1
      grind [Literal.models_negate]
    | some M' =>
      have := M.models_insert h1
      grind only [PartialModel.insert_eq_some_iff, Option.some.injEq]

@[simp]
lemma models_toPartialModel {n} {δ : Cube n} {M} :
    δ.toPartialModel = some M → M.models = δ.models := by
  suffices h1 :
    ∀ M', (δ.foldlM PartialModel.insert M') = some M → M.models = δ.models ∩ M'.models by
    intro h2
    have := h1 PartialModel.empty h2
    simp_all only [PartialModel.models_empty, Set.inter_univ]
  induction δ generalizing M with
  | nil =>
    grind only [models, = List.foldlM_nil, = Option.pure_apply, = Set.mem_inter_iff,
      usr Set.mem_ofPred_eq, ← List.not_mem_nil]
  | cons l δ' ih =>
    simp_all only [List.foldlM_cons, Option.bind_eq_bind, models_cons, Option.bind_eq_some_iff]
    rintro M'' ⟨M', h3, h4⟩
    grind only [PartialModel.models_insert h3]

end Formula.Cube


/-! ## Formula -/

/-- Type class for formulas with variables `Fin n`. The variables are ordered by ordering `<`. -/
class Formula n (R : Type) where
  /--
  The variables associated with the formula `φ`. Note that not all of these variables need
  to 'appear' in `φ`.
  -/
  vars : (φ : R) → VarSet n

  /-- The models of the formula `φ` -/
  models : (φ : R) → Formula.Models n

  /--
  If two assignments coincide on the variables of `φ`, then the second is a model of `φ`
  if the first one is a model of `φ`.
  -/
  models_equiv_right (φ : R) (M M' : Formula.Model n) :
    (∀ i ∈ vars φ, M i = M' i) → M ∈ models φ → M' ∈ models φ

namespace Formula

/--
If two assignments `M` and `M'` coincide on the variables of `φ`, then `M` is a model of
`φ` iff `M'` is a model of `φ`.
-/
lemma models_equiv {n} {R} [h : Formula n R] {φ : R} {M M' : Model n}
    (h1 : ∀ i ∈ h.vars φ, M i = M' i) : M ∈ h.models φ ↔ M' ∈ h.models φ := by
  constructor
  · apply models_equiv_right
    exact h1
  · apply models_equiv_right
    grind

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

@[expose]
def Clause.rename {n} {dom : VarSet n} (r : Renaming dom) (γ : Clause n) : Clause n :=
  γ.map (Literal.rename r)

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
    (φ.rename r).models = φ.models.preimage (Model.rename r) := by
  simp only [models, rename, List.mem_map, Clause.rename, Clause.models, Literal.mem_models,
    Set.mem_ofPred_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Literal.rename,
    exists_exists_and_eq_and, Set.preimage_ofPred_eq, Model.rename]

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
      simp [PartialModel.vars, hi]
    · apply h1
      simp [PartialModel.vars, hj]
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
  simp only [models, rename, VarSet.mem_rename, forall_exists_index, and_imp, Set.mem_ofPred_eq,
    Set.preimage_ofPred_eq, Model.rename]
  grind

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

end Validator.Formula.ToDNF
