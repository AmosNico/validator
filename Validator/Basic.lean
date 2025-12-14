import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.List.Sort

lemma Array.lt_of_getElem?_eq_some {α a} {xs : Array α} {i : ℕ}
  (h : xs[i]? = some a) : i < xs.size := by
  apply Array.getElem_of_getElem? at h
  rcases h
  assumption

@[simp]
lemma Fintype.elems_eq_univ {α} [h : Fintype α] [DecidableEq α] : h.elems = Finset.univ :=
  by
    ext a
    simp [Fintype.complete]

def Vector.elems {α} [h : Fintype α] [DecidableEq α] : (n : ℕ) → Finset (Vector α n)
| 0 => {#v[]}
| n + 1 => Finset.biUnion (elems n) fun v ↦ h.elems.image v.push

instance {α} [Fintype α] [DecidableEq α] {n} : Fintype (Vector α n) where

  elems := Vector.elems n

  complete :=
    by
      induction n with
      | zero => simp [Vector.elems]
      | succ n ih =>
        simp [Vector.forall_cons_iff, Vector.elems]
        intro a v
        use v, ih v, a

/--
Combine every element of the first list with every element of the second list
using the function `f`.
-/
def List.productWith {α β γ} (f : α → β → γ) (as : List α) (bs : List β) : List γ :=
  List.map (fun (a, b) ↦ f a b) <| List.product as bs

/--
Use foldr to combine any element of the first list with any element of the second list,
the third list, etc.
Note that the size of the result is exponential in the number of lists.
-/
def List.mulr {α β} (f : α → β → β) (init : β) : List (List α) → List β :=
  List.foldr (List.productWith f) [init]

def List.multiply {α} : List (List (List α)) → List (List α) :=
  List.mulr (· ++ ·) []

@[simp]
lemma List.multiply_nil {α} :
  multiply (α := α) [] = [[]] :=
  by
    simp [multiply, mulr]

@[simp]
lemma List.multiply_cons {α} {asss} {ass : List (List α)} :
  multiply (ass :: asss) = ass.flatMap (fun as ↦ (multiply asss).map (as ++ ·)) :=
  by
    simp [multiply, mulr, productWith, List.product.eq_1, List.map_flatMap]
    congr

/--
Similar to `List.merge`, but also remove duplicates.
I tried to combine `List.merge` with `List.dedup`, but there are no lemmas for
`List.dedup` with sorted. There is also `Array.mergeDedup`, but that also has no lemmas.
-/
def List.mergeDedup {α} [Ord α] : (xs ys : List α) → List α
| [], ys => ys
| xs, [] => xs
| x :: xs, y :: ys =>
  match compare x y with
  | .lt => x :: mergeDedup xs (y :: ys)
  | .eq => x :: mergeDedup xs ys
  | .gt => y :: mergeDedup (x :: xs) ys

lemma List.mem_mergeDedup {α} [LinearOrder α] {xs ys : List α} {a} :
  a ∈ mergeDedup xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  fun_induction mergeDedup
  all_goals simp
  all_goals grind

lemma List.mergeDedup_sorted {α} [LinearOrder α] {xs ys : List α} :
  xs.Sorted (· < ·) → ys.Sorted (· < ·) → (mergeDedup xs ys).Sorted (· < ·) := by
  fun_induction mergeDedup
  all_goals simp
  case _ x xs y ys h ih =>
    simp [compare_lt_iff_lt] at h
    simp_all [mem_mergeDedup]
    intro h1 h2 h3 h4 x' hx'
    rcases hx' with hx' | rfl | hx'
    · grind
    · exact h
    · specialize h3 x' hx'
      exact Trans.trans h h3
  case _ x xs y ys h ih =>
    simp [mem_mergeDedup]
    grind
  case _ x xs y ys h ih =>
    simp [compare_gt_iff_gt] at h
    simp_all [mem_mergeDedup]
    intro h1 h2 h3 h4 x' hx'
    rcases hx' with (rfl | hx') | hx'
    · exact h
    · specialize h1 x' hx'
      exact Trans.trans h h1
    · grind

def List.diff' {α} [Ord α] : (xs ys : List α) → List α
| [], _ => []
| xs, [] => xs
| x :: xs, y :: ys =>
  match compare x y with
  | .lt => x :: diff' xs (y :: ys)
  | .eq => diff' xs ys
  | .gt => diff' (x :: xs) ys

lemma List.mem_diff' {α} [LinearOrder α] {xs ys : List α}
  (h1 : xs.Sorted (· < ·)) (h2 : ys.Sorted (· < ·)) :
  ∀ a, a ∈ diff' xs ys ↔ a ∈ xs ∧ a ∉ ys := by
  fun_induction diff'
  all_goals simp
  all_goals
    simp at h1 h2
    simp_all [compare_lt_iff_lt, compare_gt_iff_gt]
    grind

lemma List.diff'_sorted {α} [LinearOrder α] {xs ys : List α} :
  xs.Sorted (· < ·) → ys.Sorted (· < ·) → (diff' xs ys).Sorted (· < ·) := by
  fun_induction diff'
  all_goals simp_all [mem_diff']

lemma List.map_toFinset {α β} [DecidableEq α] [DecidableEq β] {f : α → β} {xs : List α} :
  (xs.map f).toFinset = xs.toFinset.image f := by
  ext b
  simp

@[simp]
lemma Set.inter_compl_subset_union_compl
  {α} [Fintype α] {s1 s2 s3 s4 : Set α} :
  s1 ∩ s2ᶜ ⊆ s3 ∪ s4ᶜ ↔ s1 ∩ s4 ⊆ s3 ∪ s2 := by
  simp [Set.subset_def]
  grind
