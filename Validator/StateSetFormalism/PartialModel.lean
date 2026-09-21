module

public import Validator.StateSetFormalism.Basic

/-! # PartialModel
This file provides the definition of partial models and operations and lemmas for working with them.
-/

namespace Validator

open STRIPS (VarSet)

public section

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
  simp only [models, Set.mem_ofPred_eq, Literal.mem_models]
  constructor
  · grind [mem_def]
  · intro h1
    constructor
    · intro i hi
      specialize h1 ⟨i, true⟩ hi
      grind only
    · intro i hi
      specialize h1 ⟨i, false⟩ hi
      grind only

lemma models_nonempty {n} (M : PartialModel n) : M.models.Nonempty := by
  use fun i ↦ ⟨i, true⟩ ∈ M
  simp only [mem_models, Literal.mem_models, mem_def]
  intro l
  split
  case h_1 l i => simp only [iff_true, imp_self]
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
  simp [mem_def, insert, Literal.negate_eq]
  grind

@[simp]
lemma insert_eq_some_iff {n} {M M' : PartialModel n} {l} :
    M.insert l = some M' ↔ l.negate ∉ M ∧ ∀ l', l' ∈ M' ↔ l' ∈ M ∨ l' = l := by
  simp only [insert, mem_def, Literal.negate_eq]
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
    simp_all only [Set.nonempty_iff_ne_empty, ne_eq, List.foldlM_nil, Option.pure_def, reduceCtorEq,
      models_nil, Set.univ_inter]
  | cons l δ' ih =>
    intro M
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_none_iff, models_cons, ih]
    cases h1 : M.insert l with
    | none =>
      simp only [reduceCtorEq, IsEmpty.forall_iff, implies_true, Set.inter_assoc, true_iff]
      rw [PartialModel.insert_eq_none_iff] at h1
      grind [Literal.models_negate, PartialModel.subset_models_of_mem h1]
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
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, models_nil, Set.univ_inter,
      forall_eq]
  | cons l δ' ih =>
    simp_all only [List.foldlM_cons, Option.bind_eq_bind, models_cons, Option.bind_eq_some_iff]
    rintro M'' ⟨M', h3, h4⟩
    grind only [PartialModel.models_insert h3]
