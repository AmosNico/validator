module

public import Mathlib.Order.SetNotation
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

lemma not_mem_pos_or_not_mem_neg {n} (M : PartialModel n) : ∀ i, i ∉ M.pos ∨ i ∉ M.neg := by
  grind only [VarSet.inter_eq_empty_iff, M.disjoint]

@[grind .]
lemma not_mem_or_negate_not_mem {n} (M : PartialModel n) : ∀ l, l ∉ M ∨ l.negate ∉ M := by
  grind only [mem_iff, !Literal.isPos_negate, !Literal.var_negate, VarSet.inter_eq_empty_iff,
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
  simp only [vars_eq, VarSet.mem_union, mem_iff, Literal.exists_iff, Bool.exists_bool]
  grind only

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
  simp_rw [models, Set.mem_ofPred_eq, Literal.mem_models]
  simp_rw [Literal.forall_iff, Bool.forall_bool, mem_iff]
  grind only

lemma models_nonempty {n} (M : PartialModel n) : M.models.Nonempty := by
  use fun i ↦ ⟨i, true⟩ ∈ M
  simp only [mem_models, Literal.mem_models, mem_iff]
  grind only [not_mem_pos_or_not_mem_neg]

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

@[simp]
lemma models_insert {n} {M : PartialModel n} {l h1} :
    (M.insert l h1).models = M.models ∩ l.models := by
  ext M'
  grind only [mem_models, mem_insert_iff, Set.mem_inter_iff]

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

/-- Two partial models are compatible if they agree on their common variables. -/
def Compatible {n} (M1 M2 : PartialModel n) : Prop :=
  (M1.pos ∪ M2.pos) ∩ (M1.neg ∪ M2.neg) = ∅

lemma compatible_iff {n} {M1 M2 : PartialModel n} :
    M1.Compatible M2 ↔ (M1.pos ∪ M2.pos) ∩ (M1.neg ∪ M2.neg) = ∅ := by rfl

lemma compatible_iff_mem {n} {M1 M2 : PartialModel n} :
    M1.Compatible M2 ↔ ∀ l, l ∉ M1 ∨ l.negate ∉ M2 := by
  simp only [compatible_iff, VarSet.inter_eq_empty_iff, VarSet.mem_union, not_or]
  simp only [mem_iff, Literal.var_negate, Literal.isPos_negate]
  simp only [Literal.forall_iff, Bool.forall_bool]
  grind only [not_mem_pos_or_not_mem_neg]

lemma compatible_iff_models {n} {M1 M2 : PartialModel n} :
    M1.Compatible M2 ↔ (M1.models ∩ M2.models).Nonempty := by
  simp only [compatible_iff, VarSet.inter_eq_empty_iff, VarSet.mem_union, not_or]
  simp only [Set.nonempty_def, Set.mem_inter_iff, mem_models']
  constructor
  · intro h1
    use fun i ↦ i ∈ M1.pos ∨ i ∈ M2.pos
    grind only
  · grind only

lemma compatible_symm {n} {M1 M2 : PartialModel n} : M1.Compatible M2 ↔ M2.Compatible M1 := by
  simp only [compatible_iff, VarSet.inter_eq_empty_iff, VarSet.mem_union]
  grind only

/-- The conjunction of two compatible partial models. -/
def and {n} (M1 M2 : PartialModel n) (h : M1.Compatible M2) :
    PartialModel n :=
  ⟨M1.pos ∪ M2.pos, M1.neg ∪ M2.neg, h⟩

@[simp]
lemma pos_and {n} {M1 M2 : PartialModel n} {h : M1.Compatible M2} :
    (M1.and M2 h).neg = M1.neg ∪ M2.neg := (rfl)

@[simp]
lemma neg_and {n} {M1 M2 : PartialModel n} {h : M1.Compatible M2} :
    (M1.and M2 h).pos = M1.pos ∪ M2.pos := (rfl)

@[simp]
lemma mem_and {n} {M1 M2 : PartialModel n} {h : M1.Compatible M2} {l} :
    l ∈ M1.and M2 h ↔ l ∈ M1 ∨ l ∈ M2 := by
  grind only [mem_iff, !neg_and, !pos_and, VarSet.mem_union]

@[simp, grind =]
lemma vars_and {n} {M1 M2 : PartialModel n} {h} :
    (M1.and M2 h).vars = M1.vars ∪ M2.vars := by
  ext i
  grind only [vars_eq, neg_and, pos_and, VarSet.mem_union]

@[simp, grind =]
lemma models_and {n} {M1 M2 : PartialModel n} {h} :
    (M1.and M2 h).models = M1.models ∩ M2.models := by
  ext M
  grind only [and, mem_models', VarSet.mem_union, Set.mem_inter_iff]

lemma and_symm {n} {M1 M2 : PartialModel n} {h} :
    ∃ h', M1.and M2 h = M2.and M1 h' := by
  use compatible_symm.1 h
  rw [PartialModel.ext'_iff]
  grind only [mem_and]

/--
Returns the conjunction of two partial models.
Returns `none` if the conjunction of the two partial models is inconsistent.
-/
def and? {n} (M1 M2 : PartialModel n) : Option (PartialModel n) :=
  let pos := M1.pos ∪ M2.pos
  let neg := M1.neg ∪ M2.neg
  if h : pos ∩ neg = ∅ then
    return ⟨pos, neg, h⟩
  else
    none

@[simp, grind =]
lemma and?_eq_some_iff {n} {M1 M2 M3 : PartialModel n} :
    M1.and? M2 = some M3 ↔ ∃ h1, M1.and M2 h1 = M3 := by
  grind only [and?, compatible_iff, and, = Option.pure_apply]

/-- Restrict the given partial model to the given set of variables. -/
def restrict {n} (M : PartialModel n) (vars : VarSet n) : PartialModel n where
  pos := M.pos ∩ vars
  neg := M.neg ∩ vars
  disjoint := by grind only [VarSet.inter_eq_empty_iff, VarSet.mem_inter, M.disjoint]

@[simp]
lemma pos_restrict {n} {M : PartialModel n} {vars} : (M.restrict vars).pos = M.pos ∩ vars := (rfl)

@[simp]
lemma neg_restrict {n} {M : PartialModel n} {vars} : (M.restrict vars).neg = M.neg ∩ vars := (rfl)

@[simp]
lemma vars_restrict {n} {M : PartialModel n} {vars} : (M.restrict vars).vars = M.vars ∩ vars := by
  ext i
  grind only [vars_eq, !pos_restrict, !neg_restrict, VarSet.mem_inter, VarSet.mem_union]

@[simp]
lemma mem_restrict {n} {M : PartialModel n} {vars l} :
    l ∈ M.restrict vars ↔ l ∈ M ∧ l.var ∈ vars := by
  grind only [restrict, mem_iff, VarSet.mem_inter]

lemma models_subset_models_restrict {n} {M : PartialModel n} {vars} :
    M.models ⊆ (M.restrict vars).models := by
  simp only [Set.subset_def, mem_models', pos_restrict, VarSet.mem_inter, and_imp, neg_restrict]
  grind only

@[simp]
lemma restrict_inter {n} {M : PartialModel n} {V1 V2} :
    M.restrict (V1 ∩ V2) = (M.restrict V1).restrict V2 := by
  rw [PartialModel.ext'_iff]
  grind only [mem_restrict, VarSet.mem_inter]

@[simp]
lemma restrict_vars_eq_self_iff {n} {M : PartialModel n} {vars} :
    M.restrict vars = M ↔ M.vars ⊆ vars := by
  simp only [PartialModel.ext_iff, pos_restrict, VarSet.ext_iff, VarSet.mem_inter,
    neg_restrict, vars_eq, VarSet.subset_iff, VarSet.mem_union]
  grind only

@[simp]
lemma restrict_vars_self {n} {M : PartialModel n} : M.restrict M.vars = M := by
  simp only [restrict_vars_eq_self_iff, VarSet.subset_iff, imp_self, implies_true]

@[simp]
lemma and_restrict_left {n} {M1 M2 : PartialModel n} {h} : (M1.and M2 h).restrict M1.vars = M1 := by
  ext i
  · simp only [vars_eq, pos_restrict, neg_and, VarSet.mem_inter, VarSet.mem_union]
    suffices i ∈ M1.neg → i ∉ M2.pos by grind only
    simp only [compatible_iff, VarSet.inter_eq_empty_iff, VarSet.mem_union, not_or] at h
    grind only [M2.not_mem_pos_or_not_mem_neg]
  · simp only [vars_eq, neg_restrict, pos_and, VarSet.mem_inter, VarSet.mem_union]
    suffices i ∈ M1.pos → i ∉ M2.neg by grind only
    simp only [compatible_iff, VarSet.inter_eq_empty_iff, VarSet.mem_union, not_or] at h
    grind only [M2.not_mem_pos_or_not_mem_neg]

@[simp]
lemma and_restrict_right {n} {M1 M2 : PartialModel n} {h} :
    (M1.and M2 h).restrict M2.vars = M2 := by
  grind only [!and_symm, !and_restrict_left]

lemma restrict_eq_iff_compatible {n} {M1 M2 : PartialModel n} :
    M1.restrict M2.vars = M2.restrict M1.vars ↔ M1.Compatible M2 := by
  rw [compatible_iff_models, PartialModel.ext_iff]
  simp only [pos_restrict, neg_restrict, PartialModel.vars_eq]
  simp only [VarSet.ext_iff, VarSet.mem_inter, VarSet.mem_union]
  constructor
  · intro h1
    use fun i ↦ i ∈ M1.pos ∨ i ∈ M2.pos
    simp only [Set.mem_inter_iff, mem_models', not_or]
    grind only [M1.not_mem_pos_or_not_mem_neg, M2.not_mem_pos_or_not_mem_neg]
  · rintro ⟨M, hM⟩
    simp only [Set.mem_inter_iff, mem_models'] at hM
    grind only [M1.not_mem_pos_or_not_mem_neg, M2.not_mem_pos_or_not_mem_neg]

/--
Expand the given partial model `M` to `2 ^ |Varset.ofList xs|` partial models over
`M.vars ∪ Varset.ofList xs`.
-/
-- TODO : implement iterator for `VarSet` and use it here instead of `List`
private def expandAux {n} (M : PartialModel n) (xs : List (Fin n))
    (h1 : xs.Nodup) (h2 : ∀ x ∈ xs, x ∉ M.vars) : List (PartialModel n) :=
  match xs with
  | [] => [M]
  | x :: xs' =>
    let M1 := M.insert ⟨x, false⟩ (by grind only [= List.mem_cons])
    let M2 := M.insert ⟨x, true⟩ (by grind only [= List.mem_cons])
    have hM1 : ∀ x ∈ xs', x ∉ M1.vars := by
      simp only [vars_insert, VarSet.mem_insert, not_or, M1]
      grind only [= List.nodup_cons, = List.mem_cons]
    have hM2 : ∀ x ∈ xs', x ∉ M2.vars := by
      simp only [vars_insert, VarSet.mem_insert, not_or, M2]
      grind only [= List.nodup_cons, = List.mem_cons]
    M1.expandAux xs' (by grind) hM1 ++ M2.expandAux xs' (by grind) hM2

private lemma vars_of_mem_expandAux {n} {M : PartialModel n} {xs h1 h2} {M' : PartialModel n} :
    M' ∈ M.expandAux xs h1 h2 → M'.vars = M.vars ∪ VarSet.ofList xs := by
  fun_induction expandAux with
  | case1 M =>
    grind only [List.mem_cons, !VarSet.ofList_nil, List.not_mem_nil, VarSet.union_empty]
  | case2 M x xs h1 h2 M1 M2 hM1 hM2 ih1 ih2 =>
    simp only [List.mem_append, VarSet.ofList_cons]
    simp [VarSet.ext_iff] at ⊢ ih1 ih2
    rintro (h3 | h3)
    · grind only [ih1 h3, vars_insert, VarSet.mem_insert]
    · grind only [ih2 h3, vars_insert, VarSet.mem_insert]

private lemma mem_expandAux_aux1 {n} {M M' : PartialModel n} {l hl} :
    M'.restrict (M.insert l hl).vars = M.insert l hl → M'.restrict M.vars = M := by
  rintro h1
  refine ext' (fun l' ↦ ?_)
  simp only [mem_restrict]
  if heq : l' = l then
    grind only [mem_vars]
  else
    simp only [PartialModel.ext'_iff, mem_restrict] at h1
    simp only [vars_insert, VarSet.mem_insert, mem_insert_iff] at h1
    have h2 := h1 l'.negate
    specialize h1 l'
    simp only [Literal.ext_iff, Literal.var_negate, Literal.isPos_negate] at *
    grind only [not_mem_or_negate_not_mem]

private lemma mem_expandAux_aux2 {n} {M M' : PartialModel n} {l hl} :
    M'.restrict M.vars = M → l ∈ M' → M'.restrict (M.insert l hl).vars = M.insert l hl := by
  rintro h1 h2
  refine ext' (fun l' ↦ ?_)
  simp only [vars_insert, mem_restrict, VarSet.mem_insert, mem_insert_iff]
  if heq : l' = l then
    grind only
  else
    simp only [PartialModel.ext'_iff, mem_restrict] at h1
    simp only [← h1 l', heq, or_false, and_congr_right_iff, or_iff_left_iff_imp]
    grind only [not_mem_or_negate_not_mem, Literal.eq_or_eq_negate_iff_var_eq]

private lemma mem_expandAux {n} {M : PartialModel n} {xs h1 h2} {M' : PartialModel n} :
    M' ∈ M.expandAux xs h1 h2 ↔ M'.vars = M.vars ∪ VarSet.ofList xs ∧ M'.restrict M.vars = M := by
  constructor
  · intro h3
    simp only [vars_of_mem_expandAux h3, true_and]
    fun_induction expandAux with
    | case1 M =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
      rw [← h3, restrict_vars_eq_self_iff]
      grind only
    | case2 M x xs h1 h2 M1 M2 hM1 hM2 ih1 ih2 =>
      simp only [List.mem_append] at h3
      rcases h3 with (h3 | h3)
      · exact mem_expandAux_aux1 (ih1 h3)
      · exact mem_expandAux_aux1 (ih2 h3)
  · rintro ⟨h3, h4⟩
    fun_induction expandAux with
    | case1 M =>
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      simp only [VarSet.ofList_nil, VarSet.union_empty] at h3
      symm
      rw [← h4, restrict_vars_eq_self_iff, h3]
      grind only
    | case2 M x xs h1 h2 M1 M2 hM1 hM2 ih1 ih2 =>
      simp only [List.mem_append]
      simp only [VarSet.ofList_cons, VarSet.ext_iff, VarSet.mem_union, VarSet.mem_insert,
        VarSet.mem_ofList] at h3
      have h5 : M'.vars = VarSet.insert x M.vars ∪ VarSet.ofList xs := by
        simp only [VarSet.ext_iff, VarSet.mem_union, VarSet.mem_insert, VarSet.mem_ofList]
        grind only
      specialize ih1 (by simp only [h5, vars_insert, M1])
      specialize ih2 (by simp only [h5, vars_insert, M2])
      specialize h3 x
      simp only [or_true, iff_true, PartialModel.mem_vars] at h3
      rcases h3 with ⟨l, hl, rfl⟩
      cases h6 : l.isPos with
      | false => exact .inl <| ih1 <| mem_expandAux_aux2 h4 (by simp only [← h6, hl])
      | true => exact .inr <| ih2 <| mem_expandAux_aux2 h4 (by simp only [← h6, hl])

private lemma models_subset_expandAux {n} {M : PartialModel n} {V h1 h2} :
    M.models ⊆ ⋃ M' ∈ M.expandAux V h1 h2, M'.models := by
  intro M1 hM1
  simp only [Set.mem_iUnion, mem_expandAux, exists_prop]
  -- Using induction avoids the requirement of `M` being decidable.
  induction V with
  | nil =>
    simp only [VarSet.ofList_nil, VarSet.union_empty]
    use M
    simp only [restrict_vars_self, and_self, hM1]
  | cons i V ih =>
    simp only [List.nodup_cons, List.mem_cons, forall_eq_or_imp, VarSet.ofList_cons] at h1 h2 ⊢
    simp_all only [not_false_eq_true, implies_true, forall_const]
    rcases ih with ⟨M', ⟨h3, h4⟩, h5⟩
    simp only [VarSet.ext_iff, VarSet.mem_union, VarSet.mem_ofList] at h3
    if h : M1 i then
      use M'.insert ⟨i, true⟩ (by grind only)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · ext i'
        grind only [vars_insert, VarSet.mem_insert, VarSet.mem_union, VarSet.mem_ofList]
      · rw [PartialModel.ext'_iff] at ⊢ h4
        grind only [mem_restrict, mem_insert_iff]
      · grind only [!models_insert, Set.mem_inter_iff, Literal.mem_models]
    else
      use M'.insert ⟨i, false⟩ (by grind only)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · ext i'
        grind only [vars_insert, VarSet.mem_insert, VarSet.mem_union, VarSet.mem_ofList]
      · rw [PartialModel.ext'_iff] at ⊢ h4
        grind only [mem_restrict, mem_insert_iff]
      · grind only [!models_insert, Set.mem_inter_iff, Literal.mem_models]

private lemma models_expandAux {n} (M : PartialModel n) {V h1 h2} :
    M.models = ⋃ M' ∈ M.expandAux V h1 h2, M'.models := by
  ext M1
  constructor
  · intro hM1
    exact models_subset_expandAux hM1
  · simp only [Set.mem_iUnion, mem_expandAux, exists_prop]
    rintro ⟨M', ⟨h3, h4⟩, h5⟩
    rw [← h4]
    exact models_subset_models_restrict h5

/-- Expand the given partial model `M` to `2 ^ |V \ M.vars|` partial models over `M.vars ∪ V`. -/
-- TODO : implement this as an iterator, as `Implicant` only needs to check a linear amount of
-- partial models, avoiding the exponential complexity
def expand {n} (M : PartialModel n) (V : VarSet n) : List (PartialModel n) :=
  M.expandAux (V \ M.vars).toList VarSet.toList_nodup (by simp)

lemma vars_of_mem_expand {n} {M : PartialModel n} {V} {M' : PartialModel n} :
    M' ∈ M.expand V → M'.vars = M.vars ∪ V := by
  intro h
  have := vars_of_mem_expandAux h
  simp_all only [VarSet.ofList_toList, VarSet.ext_iff, VarSet.mem_union, VarSet.mem_diff]
  grind only

lemma mem_expand {n} {M : PartialModel n} {V} {M' : PartialModel n} :
    M' ∈ M.expand V ↔ M'.vars = M.vars ∪ V ∧ M'.restrict M.vars = M := by
  simp only [expand, mem_expandAux, VarSet.ofList_toList, VarSet.ext_iff, VarSet.mem_union,
    VarSet.mem_diff, and_congr_left_iff]
  grind only

lemma expand_restrict {n} {M : PartialModel n} {V} {M'} :
    M' ∈ (M.restrict V).expand V ↔ ∃ M'' ∈ M.expand V, M''.restrict V = M' := by
  simp only [mem_expand, vars_restrict]
  constructor
  · intro ⟨h1, h2⟩
    obtain ⟨rfl⟩ : M'.vars = V := by
      rw [VarSet.ext_iff]
      grind only [VarSet.mem_union, VarSet.mem_inter]
    rw [VarSet.inter_comm, restrict_inter, restrict_vars_self, restrict_eq_iff_compatible] at h2
    use M'.and M h2
    rw [vars_and, VarSet.union_comm]
    simp only [and_restrict_right, and_self, and_restrict_left]
  · rintro ⟨M'', ⟨h1, h2⟩, rfl⟩
    have h : V ∩ (M.vars ∩ V) = M.vars ∩ V := by
      simp [VarSet.ext_iff, VarSet.mem_inter]
    rw [← restrict_inter, h, restrict_inter, h2]
    simp only [vars_restrict, h1, VarSet.ext_iff, VarSet.mem_inter, VarSet.mem_union, and_true]
    grind only

lemma subset_models_of_expand {n} {M : PartialModel n} {V} :
    ∀ M' ∈ M.expand V, M'.models ⊆ M.models := by
  simp only [mem_expand]
  intro M' ⟨h1, h2⟩ M'' h3
  simp only [mem_models'] at ⊢ h3
  simp only [PartialModel.ext_iff, pos_restrict, VarSet.ext_iff, VarSet.mem_inter,
    neg_restrict] at h2
  grind only

@[simp]
lemma models_expand {n} (M : PartialModel n) V :
    M.models = ⋃ M' ∈ M.expand V, M'.models := by
  simp only [expand, ← models_expandAux]

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

def toCNF {n} (M : PartialModel n) : CNF n :=
  M.foldl (fun φ l ↦ [l] :: φ) []

lemma mem_toCNF {n} {M : PartialModel n} {γ} : γ ∈ M.toCNF ↔ ∃ l ∈ M, γ = [l] := by
  simp [toCNF, foldl_cons, mem_iff]

lemma models_toCNF {n} {M : PartialModel n} : M.toCNF.models = M.models := by
  ext M'
  simp only [CNF.mem_models, mem_toCNF, Clause.mem_models, forall_exists_index, and_imp,
    mem_models]
  grind only [= List.mem_cons, ← List.not_mem_nil]

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
