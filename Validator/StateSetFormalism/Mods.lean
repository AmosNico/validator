module

public import Validator.StateSetFormalism.Formula
import Std.Data.HashSet.Lemmas

-- TODO : make more efficient and move to Basic.lean

def Std.HashSet.filterMap {α} [BEq α] [Hashable α] {β} [BEq β] [Hashable β]
    (f : α → Option β) (m : Std.HashSet α) : Std.HashSet β :=
  Std.HashSet.ofList (m.toList.filterMap f)

@[simp]
lemma Std.HashSet.mem_filterMap {α} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {f : α → Option β} {m : Std.HashSet α} {b : β} :
    b ∈ m.filterMap f ↔ ∃ a ∈ m, f a = some b := by
  simp only [filterMap, mem_ofList, List.contains_eq_mem, List.mem_filterMap, mem_toList,
    decide_eq_true_eq]

def Std.HashSet.biUnion {α} [BEq α] [Hashable α] {β} [BEq β] [Hashable β]
    (f : α → Std.HashSet β) (m : Std.HashSet α) : Std.HashSet β :=
  Std.HashSet.ofList (m.toList.flatMap fun m ↦ (f m).toList)

@[simp]
lemma Std.HashSet.mem_flatMap {α} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {f : α → Std.HashSet β} {m : Std.HashSet α} {b : β} :
    b ∈ m.biUnion f ↔ ∃ a ∈ m, b ∈ f a := by
  simp only [biUnion, mem_ofList, List.contains_eq_mem, List.mem_flatMap, mem_toList,
    decide_eq_true_eq]

def Std.HashSet.attachMap {α} [BEq α] [LawfulBEq α] [Hashable α] {β} [BEq β] [Hashable β]
     (m : Std.HashSet α) (f : (a : α) → a ∈ m → β): Std.HashSet β :=
  Std.HashSet.ofList (m.toList.attach.map fun ⟨a, ha⟩ ↦ f a (Std.HashSet.mem_toList.1 ha))

@[simp]
lemma Std.HashSet.mem_attachMap {α} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {m : Std.HashSet α} {f : (a : α) → a ∈ m → β} {b : β} :
    b ∈ m.attachMap f ↔ ∃ a ha, f a ha = b := by
  simp only [attachMap, mem_ofList, List.contains_eq_mem, List.mem_map, List.mem_attach, true_and,
    Subtype.exists, mem_toList, decide_eq_true_eq]

namespace Validator
open Formula STRIPS

public instance {n} : Hashable (PartialModel n) where
  hash M := mixHash (hash M.pos.toBitVec) (hash M.neg.toBitVec)

public structure MODS n where
  private vars : VarSet n
  private mods : Std.HashSet (PartialModel n)
  private vars_eq : ∀ M ∈ mods, M.vars = vars

namespace PartialModel

/--
Returns the conjunction of two partial models.
Returns `none` if the conjunction of the two partial models is inconsistent.
-/
def and {n} (M1 M2 : PartialModel n) : Option (PartialModel n) :=
  let pos := M1.pos ∪ M2.pos
  let neg := M1.neg ∪ M2.neg
  if h : pos ∩ neg = ∅ then
    return ⟨pos, neg, h⟩
  else
    none

lemma vars_and {n} {M1 M2 M : PartialModel n} :
    M1.and M2 = some M → M.vars = M1.vars ∪ M2.vars := by
  simp only [and, Option.pure_def, Option.dite_none_right_eq_some, Option.some.injEq]
  rintro ⟨h1, rfl⟩
  simp only [vars_eq, SetLike.ext_iff, VarSet.mem_union]
  tauto

@[grind →]
lemma models_and {n} {M1 M2 M : PartialModel n} :
    M1.and M2 = some M → M.models = M1.models ∩ M2.models := by
  simp only [and, Option.pure_def, Option.dite_none_right_eq_some, Option.some.injEq]
  rintro ⟨h1, rfl⟩
  simp only [Set.ext_iff, mem_models', VarSet.mem_union, Set.mem_inter_iff]
  grind only

lemma isSome_and_iff {n} {M1 M2 : PartialModel n} :
    (M1.and M2).isSome ↔ M1.models ∩ M2.models ≠ ∅ := by
  simp only [and, VarSet.inter_eq_empty_iff, VarSet.mem_union, not_or, Option.pure_def,
    Option.isSome_dite]
  simp only [ne_eq, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and, not_forall, not_not]
  simp only [mem_models', exists_and_left, exists_prop]
  constructor
  · intro h1
    use fun i ↦ i ∈ M1.pos ∨ i ∈ M2.pos
    grind only
  · grind only

def restrict {n} (M : PartialModel n) (vars : VarSet n) : PartialModel n where
  pos := M.pos ∩ vars
  neg := M.neg ∩ vars
  disjoint := by grind only [VarSet.inter_eq_empty_iff, VarSet.mem_inter, M.disjoint]

@[simp]
lemma pos_restrict {n} {M : PartialModel n} {vars} : (M.restrict vars).pos = M.pos ∩ vars := rfl

@[simp]
lemma neg_restrict {n} {M : PartialModel n} {vars} : (M.restrict vars).neg = M.neg ∩ vars := rfl

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

/--
If two partial models `M1` and `M2` agree on their common variables,
then their conjunction is well-defined.
-/
lemma exists_of_restrict_eq {n} {M1 M2 : PartialModel n} :
    M1.restrict M2.vars = M2.restrict M1.vars → ∃ M3 : PartialModel n, M1.and M2 = some M3 := by
  intro h1
  rw [← Option.isSome_iff_exists ,isSome_and_iff]
  simp only [ne_eq, ← Set.nonempty_iff_ne_empty]
  use fun i ↦ i ∈ M1.pos ∨ i ∈ M2.pos
  simp only [Set.mem_inter_iff, mem_models', not_or]
  simp only [PartialModel.ext_iff, pos_restrict, neg_restrict, PartialModel.vars_eq] at h1
  simp only [VarSet.ext_iff, VarSet.mem_inter, VarSet.mem_union] at h1
  grind only [VarSet.inter_eq_empty_iff, M1.disjoint, M2.disjoint]

/--
If two partial models `M1` and `M2` agree on their common variables,
then their conjunction is well-defined.
-/
lemma exists_iff_restrict_eq {n} {M1 M2 : PartialModel n} :
    M1.restrict M2.vars = M2.restrict M1.vars ↔ ∃ M3 : PartialModel n, M1.and M2 = some M3 := by
  rw [← Option.isSome_iff_exists ,isSome_and_iff]
  simp only [ne_eq, ← Set.nonempty_iff_ne_empty]
  simp only [PartialModel.ext_iff, pos_restrict, neg_restrict, PartialModel.vars_eq]
  simp only [VarSet.ext_iff, VarSet.mem_inter, VarSet.mem_union]
  constructor
  · intro h1
    use fun i ↦ i ∈ M1.pos ∨ i ∈ M2.pos
    simp only [Set.mem_inter_iff, mem_models', not_or]
    grind only [VarSet.inter_eq_empty_iff, M1.disjoint, M2.disjoint]
  · rintro ⟨M, hM⟩
    simp only [Set.mem_inter_iff, mem_models'] at hM
    grind only [VarSet.inter_eq_empty_iff, M1.disjoint, M2.disjoint]

/--
If two partial models `M1` and `M2` agree on their common variables,
then their conjunction is well-defined.
-/
lemma restrict_eq_iff {n} {M1 M2 : PartialModel n} :
    M1.restrict M2.vars = M2.restrict M1.vars ↔ M1.models ∩ M2.models ≠ ∅ := by
  simp only [ne_eq, ← Set.nonempty_iff_ne_empty]
  simp only [PartialModel.ext_iff, pos_restrict, neg_restrict, PartialModel.vars_eq]
  simp only [VarSet.ext_iff, VarSet.mem_inter, VarSet.mem_union]
  constructor
  · intro h1
    use fun i ↦ i ∈ M1.pos ∨ i ∈ M2.pos
    simp only [Set.mem_inter_iff, mem_models', not_or]
    grind only [VarSet.inter_eq_empty_iff, M1.disjoint, M2.disjoint]
  · rintro ⟨M, hM⟩
    simp only [Set.mem_inter_iff, mem_models'] at hM
    grind only [VarSet.inter_eq_empty_iff, M1.disjoint, M2.disjoint]

/--
Expand the given partial model `M` to `2 ^ |Varset.ofList xs|` partial models over
`M.vars ∪ Varset.ofList xs`.
-/
-- TODO : implement iterator for `VarSet` and use it here instead of `List`
def expand' {n} (M : PartialModel n) (xs : List (Fin n))
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
    M1.expand' xs' (by grind) hM1 ++ M2.expand' xs' (by grind) hM2

lemma vars_of_mem_expand' {n} {M : PartialModel n} {xs h1 h2} {M' : PartialModel n} :
    M' ∈ M.expand' xs h1 h2 → M'.vars = M.vars ∪ VarSet.ofList xs := by
  fun_induction expand' with
  | case1 M =>
    grind only [List.mem_cons, !VarSet.ofList_nil, List.not_mem_nil, VarSet.union_empty]
  | case2 M x xs h1 h2 M1 M2 hM1 hM2 ih1 ih2 =>
    simp only [List.mem_append, VarSet.ofList_cons]
    simp [VarSet.ext_iff] at ⊢ ih1 ih2
    rintro (h3 | h3)
    · grind only [ih1 h3, vars_insert, VarSet.mem_insert]
    · grind only [ih2 h3, vars_insert, VarSet.mem_insert]

lemma mem_expand'_aux1 {n} {M M' : PartialModel n} {l hl} :
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

lemma mem_expand'_aux2 {n} {M M' : PartialModel n} {l hl} :
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

lemma mem_expand' {n} {M : PartialModel n} {xs h1 h2} {M' : PartialModel n} :
    M' ∈ M.expand' xs h1 h2 ↔ M'.vars = M.vars ∪ VarSet.ofList xs ∧ M'.restrict M.vars = M := by
  constructor
  · intro h3
    simp only [vars_of_mem_expand' h3, true_and]
    fun_induction expand' with
    | case1 M =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
      simp only [← h3, restrict_vars_eq_self_iff]
      grind only
    | case2 M x xs h1 h2 M1 M2 hM1 hM2 ih1 ih2 =>
      simp only [List.mem_append] at h3
      rcases h3 with (h3 | h3)
      · exact mem_expand'_aux1 (ih1 h3)
      · exact mem_expand'_aux1 (ih2 h3)
  · rintro ⟨h3, h4⟩
    fun_induction expand' with
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
      | false => exact .inl <| ih1 <| mem_expand'_aux2 h4 (by simp only [← h6, hl])
      | true => exact .inr <| ih2 <| mem_expand'_aux2 h4 (by simp only [← h6, hl])

/-- Expand the given partial model `M` to `2 ^ |V \ M.vars|` partial models over `M.vars ∪ V`. -/
-- TODO : implement this as an iterator, as `Implicant` only needs to check a linear amount of
-- partial models, avoiding the exponential complexity
def expand {n} (M : PartialModel n) (V : VarSet n) : List (PartialModel n) :=
  M.expand' (V \ M.vars).toList VarSet.toList_nodup (by simp)

lemma vars_of_mem_expand {n} {M : PartialModel n} {V} {M' : PartialModel n} :
    M' ∈ M.expand V → M'.vars = M.vars ∪ V := by
  intro h
  have := vars_of_mem_expand' h
  simp_all only [VarSet.ofList_toList, VarSet.ext_iff, VarSet.mem_union, VarSet.mem_diff]
  grind only

lemma mem_expand {n} {M : PartialModel n} {V} {M' : PartialModel n} :
    M' ∈ M.expand V ↔ M'.vars = M.vars ∪ V ∧ M'.restrict M.vars = M := by
  simp only [expand, mem_expand', VarSet.ofList_toList, VarSet.ext_iff, VarSet.mem_union,
    VarSet.mem_diff, and_congr_left_iff]
  grind only

lemma expand_restrict {n} {M : PartialModel n} {V} {M'} :
    M' ∈ (M.restrict V).expand V ↔ ∃ M'' ∈ M.expand V, M''.restrict V = M' := by
  simp only [mem_expand, vars_restrict]
  constructor
  · intro ⟨h1, h2⟩
    obtain ⟨rfl⟩ : M'.vars = V := by
      simp_all only [VarSet.ext_iff, VarSet.mem_union, VarSet.mem_inter]
      tauto
    rw [VarSet.inter_comm, restrict_inter, restrict_vars_self, exists_iff_restrict_eq] at h2
    rcases h2 with ⟨M'', h2⟩
    use M''
    rw [vars_and h2, VarSet.union_comm]

    sorry
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

lemma models_expand {n} (M : PartialModel n) V :
    M.models = ⋃ M' ∈ M.expand V, M'.models := by
  ext M1
  simp only [Set.mem_iUnion, mem_expand, exists_prop]
  constructor
  · intro hM1
    use M
    sorry
  · rintro ⟨M', ⟨h1, h2⟩, h3⟩
    simp only [mem_models'] at ⊢ h3
    simp only [PartialModel.ext_iff, pos_restrict, VarSet.ext_iff, VarSet.mem_inter,
      neg_restrict] at h2
    grind only

/-
lemma disjoint {n} {V : VarSet n} {M1 M2 : PartialModel V} {M} :
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

def isTrivial_aux {n} (acc : Vector (Bool × Bool) n) : Clause n → Vector (Bool × Bool) n
  | [] => acc
  | ⟨i, true⟩ :: ls => isTrivial_aux (acc.set i (true, acc[i].2)) ls
  | ⟨i, false⟩ :: ls => isTrivial_aux (acc.set i (acc[i].1, true)) ls

lemma getElem_isTrivial_aux {n acc} {γ : Clause n} {b1 b2} {i} :
    (γ.isTrivial_aux acc)[i.val] = (b1, b2) ↔
    (b1 = acc[i].1 || ⟨i, true⟩ ∈ γ) ∧ (b2 = acc[i].2 || ⟨i, false⟩ ∈ γ) := by
  fun_induction isTrivial_aux
  case _ acc => grind only [← List.not_mem_nil, usr Fin.isLt, = Fin.getElem_fin]
  case _ acc j γ ih =>
    simp_all only [Fin.getElem_fin, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons,
      Bool.decide_or]
    constructor
    · grind only [= Vector.getElem_set]
    · intro h
      sorry
  sorry

def isTrivial {n} (γ : Clause n) : Bool :=
  (true, true) ∈ isTrivial_aux (Vector.replicate n (false, false)) γ

lemma isTrivial_iff' {n} {γ : Clause n} : isTrivial γ ↔ ∃ l ∈ γ, l.negate ∈ γ := by
  simp only [isTrivial, Vector.mem_iff_getElem', Fin.getElem_fin, getElem_isTrivial_aux,
    Vector.getElem_replicate, Bool.true_eq_false, decide_false, Bool.false_or, decide_eq_true_eq]
  constructor
  · grind only [Literal.negate_eq]
  · rintro ⟨⟨v, (true | false)⟩, h⟩
    all_goals grind only [Literal.negate_eq]

lemma isTrivial_iff {n} {γ : Clause n} : isTrivial γ ↔ γ.models = Set.univ := by
  sorry

lemma mem_models' {n} (γ : Clause n) (M : Model n) :
    M ∈ γ.models ↔ (∃ l ∈ γ, M ∈ l.models) ∨ γ.isTrivial := by
  simp_all only [mem_models, isTrivial_iff, Set.eq_univ_iff_forall, iff_self_or, implies_true]

end Clause
namespace MODS

def models {n} (φ : MODS n) : Models n :=
  { M | ∃ M' ∈ φ.mods, M ∈ PartialModel.models M' }

@[simp]
lemma mem_models {n} {φ : MODS n} {M} : M ∈ φ.models ↔ ∃ M' ∈ φ.mods, M ∈ M'.models := by
  simp [models]

lemma restrict_mem_mods {n} {φ : MODS n} {M : PartialModel n} (h : φ.vars ⊆ M.vars) :
    M.restrict φ.vars ∈ φ.mods ↔ M.models ⊆ φ.models := by
  simp only [Set.subset_def, mem_models]
  constructor
  · grind only [PartialModel.mem_models', !PartialModel.pos_restrict, !PartialModel.neg_restrict,
      VarSet.mem_inter]
  · intro h'
    have h1 : ∀ i ∈ M.neg, i ∉ M.pos := by
      grind only [VarSet.inter_eq_empty_iff, M.disjoint]
    specialize h' (fun i ↦ i ∈ M.pos) (by grind only [PartialModel.mem_models'])
    rcases h' with ⟨M', h2, h3⟩
    have h4 : M.restrict φ.vars = M' := by
      simp [PartialModel.mem_models'] at h3
      rw [← φ.vars_eq M' h2] at ⊢ h
      ext i
      · grind only [PartialModel.vars_eq, !PartialModel.pos_restrict, VarSet.mem_inter,
          VarSet.mem_union]
      · have : ∀ i ∈ M'.neg, i ∈ M.neg := by
          simp only [PartialModel.vars_eq, VarSet.subset_iff, VarSet.mem_union] at h
          grind only
        grind only [PartialModel.vars_eq, !PartialModel.neg_restrict, VarSet.mem_inter,
          VarSet.mem_union]
    simp only [h4, h2]

lemma models_subset_models_iff {n} {φ : MODS n} {M : PartialModel n} :
    M.models ⊆ φ.models ↔ ∀ M' ∈ (M.restrict φ.vars).expand φ.vars, M' ∈ φ.mods := by
  simp only [PartialModel.expand_restrict, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h1 M' hM'
    have h2 := PartialModel.subset_models_of_expand M' hM'
    have h3 := Set.Subset.trans h2 h1
    have h4 : φ.vars ⊆ M'.vars := by
      rw [PartialModel.vars_of_mem_expand hM']
      simp only [VarSet.subset_iff, VarSet.mem_union]
      tauto
    rwa [← restrict_mem_mods h4] at h3
  · rw [M.models_expand φ.vars]
    intro h1 M' hM'
    simp only [Set.mem_iUnion, exists_prop] at hM'
    rcases hM' with ⟨M'', h2, hM'⟩
    specialize h1 M'' h2
    rw [PartialModel.mem_expand] at h2
    simp only [mem_models]
    grind only [PartialModel.mem_models', !PartialModel.pos_restrict, !PartialModel.neg_restrict,
      VarSet.mem_inter]

@[no_expose]
public instance {n} : Formula n (MODS n) where

  vars φ := φ.vars

  models := models

  models_equiv_right φ M M' := by
    simp only [mem_models, PartialModel.mem_models, Literal.mem_models]
    rintro h1 ⟨M'', h2, h3⟩
    use M'', h2
    have h4 := φ.vars_eq M'' h2
    simp only [← h4, PartialModel.mem_vars] at h1
    grind only

@[no_expose]
public instance {n} : Top n (MODS n) where

  top := ⟨∅, {PartialModel.empty}, by simp⟩

  models_top := by
    simp only [Formula.models, Std.HashSet.singleton_eq_insert, Set.eq_univ_iff_forall, mem_models,
      Std.HashSet.mem_insert, beq_iff_eq, Std.HashSet.not_mem_empty, or_false, exists_eq_left',
      PartialModel.models_empty, Set.mem_univ, implies_true]

@[no_expose]
public instance {n} : Bot n (MODS n) where

  bot := ⟨∅, ∅, by simp⟩

  vars_bot := by simp only [Formula.vars]

  models_bot := by
    simp only [Formula.models, Set.eq_empty_iff_forall_notMem, mem_models,
      Std.HashSet.not_mem_empty, false_and, exists_false, not_false_eq_true, implies_true]

@[no_expose]
public instance {n} : ClausalEntailment n (MODS n) where

  entails φ γ := φ.mods.all (fun M ↦ γ.any fun l ↦ l ∈ M) || γ.isTrivial

  entails_iff := by
    intro φ γ
    simp only [Bool.or_eq_true, Std.HashSet.all_eq_true_iff_forall_mem, List.any_eq_true,
      decide_eq_true_eq, Formula.models, Set.subset_def, mem_models, forall_exists_index, and_imp]
    constructor
    · intro h M M' hM' hM
      rcases h with h | h
      · specialize h M' hM'
        rcases h with ⟨l, h1, h2⟩
        rw [Clause.mem_models]
        use l, h1
        simp_all only [PartialModel.mem_models]
      · rw [Clause.isTrivial_iff, Set.eq_univ_iff_forall] at h
        exact h M
    · simp only [Clause.mem_models', or_iff_not_imp_right]
      intro h1 h2 M hM
      by_contra h3
      obtain ⟨M', h4, h5⟩ : ∃ M', M' ∈ M.models ∧ M' ∉ γ.models := by
        let M' := fun i ↦ i ∈ M.pos ∨ ⟨i, false⟩ ∈ γ
        have hM' : M' ∈ M.models := by
          simp_all only [PartialModel.mem_models, Literal.mem_models, Bool.false_eq_true,
            not_false_eq_true, forall_const, PartialModel.mem_iff, Bool.not_eq_true, M']
          intro l hl
          rcases hl with ⟨h4, h5⟩ | ⟨h4, h5⟩
          · simp only [h4, true_or, h5]
          · simp only [h5, Bool.false_eq_true, iff_false, not_or]
            constructor
            · have := M.disjoint
              grind only [VarSet.inter_eq_empty_iff]
            · intro h6
              simp only [not_exists, not_and] at h3
              specialize h3 _ h6
              grind only [PartialModel.mem_iff]
        use M', hM'
        specialize h1 M' M hM hM' h2
        simp_all only [Clause.isTrivial_iff', not_exists, not_and, PartialModel.mem_models,
          Literal.mem_models, Clause.mem_models, not_true_eq_false, M']
        rcases h1 with ⟨l, h1, h4⟩
        rcases l with ⟨v, true | false⟩
        · grind only
        · simp_all
          specialize h3 _ h1
          specialize h2 _ h1
          grind only [Literal.negate_eq, PartialModel.mem_iff]
      specialize h1 M' M hM h4 h2
      grind only [Clause.mem_models]

@[no_expose]
public instance {n} : Implicant n (MODS n) where

  entails δ φ := match δ.toPartialModel with
    | some M =>
      if φ.vars ⊆ M.vars then
        M.restrict φ.vars ∈ φ.mods
      else
        M.restrict φ.vars |>.expand φ.vars |>.all (· ∈ φ.mods)
    | none => true

  entails_iff δ φ := by
    simp only [Formula.models]
    split
    next M h1 =>
      rw [← Cube.models_toPartialModel h1]
      split
      next h2 => simp only [restrict_mem_mods h2, decide_eq_true_eq]
      next h2 => simp only [List.all_eq_true, decide_eq_true_eq, models_subset_models_iff]
    next h =>
      rw [Cube.toPartialModel_eq_none_iff] at h
      simp only [h, Set.empty_subset]

@[no_expose]
public instance {n} : BoundedConjuction n (MODS n) where

  and φ ψ := {
    vars := φ.vars ∪ ψ.vars
    mods :=
      φ.mods.biUnion fun δ ↦ ψ.mods.filterMap fun δ' ↦ δ.and δ'
    vars_eq := by
      simp only [Std.HashSet.mem_flatMap, Std.HashSet.mem_filterMap, forall_exists_index, and_imp]
      intro M M1 h1 M2 h2
      rw [← φ.vars_eq M1 h1, ← ψ.vars_eq M2 h2]
      exact PartialModel.vars_and
    }

  models_and φ ψ := by
    simp only [Formula.models, Set.ext_iff, mem_models, Std.HashSet.mem_flatMap,
      Std.HashSet.mem_filterMap, Set.mem_inter_iff]
    intro M
    constructor
    · grind only [→ PartialModel.models_and, = Set.mem_inter_iff]
    · rintro ⟨⟨M1, hM1, h1⟩, M2, hM2, h2⟩
      have h3 : M1.models ∩ M2.models ≠ ∅ := by
        simp only [ne_eq, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_forall, not_not]
        use M
      rw [← PartialModel.isSome_and_iff, Option.isSome_iff_exists] at h3
      rcases h3 with ⟨M', hM'⟩
      grind only [= Set.mem_inter_iff, PartialModel.models_and hM']

@[no_expose]
public instance {n} : OfPartialModel n (MODS n) where

  ofPartialModel M := ⟨M.vars, {M}, by simp⟩

  vars_ofPartialModel := by simp only [Formula.vars, implies_true]

  models_ofPartialModel := by simp only [Formula.models, models, Std.HashSet.singleton_eq_insert,
    Std.HashSet.mem_insert, beq_iff_eq, Std.HashSet.not_mem_empty, or_false, exists_eq_left',
    Set.ofPred_mem_eq, implies_true]

@[no_expose]
public instance {n} : Rename n (MODS n) where

  rename φ V r h1 := {
    vars :=  φ.vars.map r.rename
    mods :=
      φ.mods.attachMap fun M hM ↦ PartialModel.rename r M (φ.vars_eq M hM ▸ h1)
    vars_eq := by
      simp only [Std.HashSet.mem_attachMap, forall_exists_index]
      intro M' M hM rfl
      simp only [← φ.vars_eq M hM, SetLike.ext_iff, PartialModel.mem_vars_rename, VarSet.mem_map]
      grind only [PartialModel.mem_vars]
    }

  vars_rename φ V r h1 := by
    simp only [Formula.vars, VarSet.mem_map, Set.mem_image, SetLike.mem_coe]
    grind only

  models_rename φ V r h1 := by
    simp [Formula.models, Set.ext_iff]

@[no_expose]
public instance {n} : ToCNF n (MODS n) where

  toCNF := sorry

  models_toCNF := sorry

@[no_expose]
public instance {n} : ToDNF n (MODS n) where

  toDNF φ := φ.mods.toList.map PartialModel.toCube

  models_toDNF := by
    simp only [Formula.models, Set.ext_iff, DNF.mem_models, List.mem_map, Std.HashSet.mem_toList,
      exists_exists_and_eq_and, PartialModel.models_toCube, mem_models, implies_true]

end Validator.MODS
