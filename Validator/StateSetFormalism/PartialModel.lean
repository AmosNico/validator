module

public import Validator.StateSetFormalism.Basic

/-! # PartialModel
This file provides the definition of partial models and operations and lemmas for working with them.
-/

namespace Validator

open STRIPS (VarSet)

public section

/-- Partial models are partial assignments. In contrast to `Model`, these are used at runtime. -/
@[ext]
structure PartialModel (n : ℕ) where
  pos : VarSet n
  neg : VarSet n
  disjoint : pos ∩ neg = ∅
deriving DecidableEq

namespace PartialModel

instance {n} : Membership (Literal n) (PartialModel n) where
  mem M
  | ⟨i, true⟩ => i ∈ M.pos
  | ⟨i, false⟩ => i ∈ M.neg

lemma mem_pos_iff {n} (M : PartialModel n) i : i ∈ M.pos ↔ ⟨i, true⟩ ∈ M := by rfl

lemma mem_neg_iff {n} (M : PartialModel n) i : i ∈ M.neg ↔ ⟨i, false⟩ ∈ M := by rfl

lemma mem_iff {n} (M : PartialModel n) l :
    l ∈ M ↔ l.var ∈ M.pos ∧ l.isPos ∨ l.var ∈ M.neg ∧ ¬l.isPos := by
  rcases l with ⟨i, (true | false)⟩
  · grind only [mem_neg_iff]
  · grind only [mem_pos_iff]

@[grind .]
lemma not_mem_or_negate_not_mem {n} (M : PartialModel n) : ∀ l, l ∉ M ∨ l.negate ∉ M := by
  grind [mem_iff, !Literal.isPos_negate, !Literal.var_negate, VarSet.inter_eq_empty_iff,
    M.disjoint]

@[ext 500]
lemma ext' {n} {M M' : PartialModel n} : (∀ l, l ∈ M ↔ l ∈ M') → M = M' := by
  intro h
  ext i
  · simp only [mem_pos_iff, h]
  · simp only [mem_neg_iff, h]

instance {n l} {M : PartialModel n} : Decidable (l ∈ M) :=
  decidable_of_iff' _ (mem_iff M l)

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

lemma var_mem_vars {n} {l : Literal n} {M : PartialModel n} :
    l.var ∈ M.vars ↔ l ∈ M ∨ l.negate ∈ M := by
  grind only [mem_vars, Literal.eq_or_eq_negate_iff_var_eq]

/-- All models corresponding to to partial model `M`. -/
def models {n} (M : PartialModel n) : Models n :=
  { M' | (∀ i ∈ M.pos, M' i) ∧ (∀ i ∈ M.neg, ¬ M' i) }

lemma mem_models' {n} (M : PartialModel n) {M'} :
    M' ∈ M.models ↔ (∀ i ∈ M.pos, M' i) ∧ (∀ i ∈ M.neg, ¬ M' i) := by
  simp [models]

lemma mem_models {n} {M : PartialModel n} {M'} : M' ∈ M.models ↔ ∀ l ∈ M, M' ∈ l.models := by
  simp only [models, Set.mem_ofPred_eq, Literal.mem_models]
  constructor
  · grind [mem_iff]
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
  simp only [mem_models, Literal.mem_models, mem_iff]
  intro l
  have h := M.disjoint
  simp only [VarSet.ext_iff, VarSet.mem_inter, VarSet.mem_empty, iff_false, not_and] at h
  grind only [mem_iff]

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
  simp [empty, Set.ext_iff, mem_models, mem_iff]

/--
The partial model equivalent to the conjunction of the given partial model and the given literal.
-/
-- The condition `l.var ∉ M.vars` can be weakened to `l.negate ∉ M` if needed.
def insert {n} (M : PartialModel n) (l : Literal n) (h : l.var ∉ M.vars) : PartialModel n :=
  match l with
  | ⟨i, true⟩ => { M with
    pos := M.pos.insert i
    disjoint := by
      simp only [vars_eq, VarSet.mem_union, not_or] at h
      grind [VarSet.inter_eq_empty_iff, VarSet.mem_insert, M.disjoint]
    }
  | ⟨i, false⟩ => { M with
    neg := M.neg.insert i
    disjoint := by
      simp only [vars_eq, VarSet.mem_union, not_or] at h
      grind only [VarSet.inter_eq_empty_iff, VarSet.mem_insert, M.disjoint]
    }

@[simp]
lemma mem_insert_iff {n} {M : PartialModel n} {l h} :
    ∀ l', l' ∈ M.insert l h ↔ l' ∈ M ∨ l' = l := by
  simp only [insert]
  split
  all_goals
    simp only [mem_iff, VarSet.mem_insert, Bool.not_eq_true, Literal.ext_iff]
    grind only

@[simp]
lemma vars_insert {n} {M : PartialModel n} {l h} :
    (M.insert l h).vars = M.vars.insert l.var := by
  ext i
  grind only [mem_vars, VarSet.mem_insert, M.mem_insert_iff]

/-- Returns none if the negation of the literal already occurs in M -/
def insert? {n} (M : PartialModel n) (l : Literal n) : Option (PartialModel n) :=
  if h : l.var ∈ M.vars then
    if l ∈ M then M else none
  else
    M.insert l h

@[simp]
lemma insert?_eq_none_iff {n} {M : PartialModel n} {l} : M.insert? l = none ↔ l.negate ∈ M := by
  grind only [insert?, var_mem_vars, M.not_mem_or_negate_not_mem l]

@[simp]
lemma insert?_eq_some_iff {n} {M M' : PartialModel n} {l} :
    M.insert? l = some M' ↔ l.negate ∉ M ∧ ∀ l', l' ∈ M' ↔ l' ∈ M ∨ l' = l := by
  simp only [insert?]
  split
  next h =>
    simp only [var_mem_vars] at h
    simp only [Option.ite_none_right_eq_some, Option.some.injEq, PartialModel.ext'_iff]
    grind only [not_mem_or_negate_not_mem]
  next h =>
    simp only [var_mem_vars, not_or] at h
    simp [Option.some.injEq, PartialModel.ext'_iff]
    grind only

lemma vars_insert? {n} {M M' : PartialModel n} {l} (h : M.insert? l = some M') :
    M'.vars = M.vars.insert l.var := by
  have ⟨h1, h2⟩ := insert?_eq_some_iff.1 h
  ext i
  grind only [mem_vars, VarSet.mem_insert]

lemma models_insert? {n} {M M' : PartialModel n} {l} :
    M.insert? l = some M' → M'.models = M.models ∩ l.models := by
  simp only [insert?_eq_some_iff, Set.ext_iff, mem_models, Set.mem_inter_iff]
  grind

def foldl {α n} (f : α → Literal n → α) (init : α) (M : PartialModel n) : α :=
  M.pos.foldl (fun a i ↦ f a ⟨i, true⟩) (M.neg.foldl (fun a i ↦ f a ⟨i, false⟩) init)

lemma foldl_cons {α n} {M : PartialModel n} {f : Literal n → α} {a} :
    a ∈ M.foldl (fun a l ↦ f l :: a) [] ↔ ∃ l ∈ M, a = f l := by
  simp only [foldl, VarSet.foldl_cons, List.not_mem_nil, or_false, mem_iff]
  grind only [Literal]

def toCNF {n} (M : PartialModel n) : CNF n :=
  M.foldl (fun φ l ↦ [l] :: φ) []

lemma mem_toCNF {n} {M : PartialModel n} {γ} : γ ∈ M.toCNF ↔ ∃ l ∈ M, γ = [l] := by
  simp [toCNF, foldl_cons, mem_iff]

lemma models_toCNF {n} {M : PartialModel n} : M.toCNF.models = M.models := by
  ext M'
  simp only [CNF.mem_models, mem_toCNF, Clause.mem_models, forall_exists_index, and_imp,
    mem_models]
  grind only [= List.mem_cons, ← List.not_mem_nil]

def toCube {n} (M : PartialModel n) : Cube n :=
  M.foldl (fun δ l ↦ l :: δ) []

@[simp]
lemma vars_toCube {n} {M : PartialModel n} : M.toCube.vars = M.vars := by
  simp [toCube, foldl_cons, mem_vars, VarSet.ext_iff, Cube.mem_vars]
  grind only

@[simp]
lemma models_toCube {n} {M : PartialModel n} : M.toCube.models = M.models := by
  ext M'
  simp [toCube, foldl_cons, mem_models]

end PartialModel

namespace Cube
/-- Translate `δ` to a partial model. Returns `none` if `δ` is inconsistent. -/
def toPartialModel {n} (δ : Cube n) : Option (PartialModel n) :=
  δ.foldlM PartialModel.insert? PartialModel.empty

@[simp]
lemma toPartialModel_eq_none_iff {n} {δ : Cube n} :
    δ.toPartialModel = none ↔ δ.models = ∅ := by
  suffices h1 : ∀ M, δ.foldlM PartialModel.insert? M = none ↔ δ.models ∩ M.models = ∅ by
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
    cases h1 : M.insert? l with
    | none =>
      simp only [reduceCtorEq, IsEmpty.forall_iff, implies_true, Set.inter_assoc, true_iff]
      rw [PartialModel.insert?_eq_none_iff] at h1
      grind [Literal.models_negate, PartialModel.subset_models_of_mem h1]
    | some M' =>
      have := M.models_insert? h1
      grind only [PartialModel.insert?_eq_some_iff, Option.some.injEq]

@[simp]
lemma models_toPartialModel {n} {δ : Cube n} {M} :
    δ.toPartialModel = some M → M.models = δ.models := by
  suffices h1 :
    ∀ M', (δ.foldlM PartialModel.insert? M') = some M → M.models = δ.models ∩ M'.models by
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
    grind only [PartialModel.models_insert? h3]
