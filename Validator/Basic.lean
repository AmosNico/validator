module

public import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.List.Sort

--@[simp 50]
public lemma Array.lt_of_getElem?_eq_some {α a} {xs : Array α} {i : ℕ}
    (h : xs[i]? = some a) : i < xs.size := by
  apply Array.getElem_of_getElem? at h
  rcases h
  assumption

/-
@[simp]
lemma Finset.biUnion_union {α β}
  {s1 s2 : Finset α} {f : α → Finset β} [DecidableEq β] [DecidableEq α] :
  (s1 ∪ s2).biUnion f = s1.biUnion f ∪ s2.biUnion f :=
  by
    induction s1 using Finset.cons_induction with
    | empty => simp
    | cons a s1' h ih => simp_all

def List.biUnion {α β} [DecidableEq β] (l : List α) (f : α → Finset β) : Finset β :=
  Finset.biUnion (l.map f).toFinset id

@[simp]
lemma List.mem_biUnion {α β} [DecidableEq β] {l : List α} {f : α → Finset β} :
  ∀ b, b ∈ l.biUnion f ↔ ∃ a ∈ l, b ∈ f a :=
  by simp [List.biUnion]

@[simp]
lemma List.biUnion_empty {α β} [Fintype β] [DecidableEq β] {f : α → Finset β} :
  biUnion [] f = ∅ :=
  by simp [biUnion]

@[simp]
lemma List.biUnion_cons {α β} [Fintype β] [DecidableEq β] {f : α → Finset β} {a as} :
  biUnion (a :: as) f = f a ∪ biUnion as f :=
  by
    ext b
    simp [biUnion]

@[simp]
lemma List.biUnion_singleton {α β} [Fintype β] [DecidableEq β] {f : α → Finset β} {a} :
  biUnion [a] f = f a :=
  by simp [biUnion]
-/
/-
instance {α} [DecidableEq α] : Std.Commutative fun (x1 x2 : Finset α) => x1 ∩ x2 where
  comm := Finset.inter_comm

instance {α} [DecidableEq α] : Std.Associative fun (x1 x2 : Finset α) => x1 ∩ x2 where
  assoc := Finset.inter_assoc


def Finset.biInter {α β} [Fintype β] [DecidableEq β] (s : Finset α) (f : α → Finset β) : Finset β :=
  Finset.fold Inter.inter Fintype.elems f s

@[simp]
lemma Finset.mem_biInter {α β} [Fintype β] [DecidableEq β] {f : α → Finset β} {s : Finset α} {b} :
  b ∈ s.biInter f ↔ ∀ a ∈ s, b ∈ f a :=
  by
    simp [Finset.biInter]
    induction s using Finset.cons_induction with
    | empty =>
      simp
      exact Fintype.complete b
    | cons a s ha ih =>
      simp_all

@[simp]
lemma Finset.biInter_empty {α β} [Fintype β] [DecidableEq β] {f : α → Finset β} :
  biInter ∅ f = Fintype.elems :=
  by simp [Finset.biInter]

@[simp]
lemma Finset.biInter_singleton {α β} [Fintype β] [DecidableEq β] {f : α → Finset β} {a} :
  biInter {a} f = f a :=
  by
    simp [biInter]
    intro x hx
    exact Fintype.complete x

@[simp]
lemma Finset.biInter_union {α β}
  {s1 s2 : Finset α} {f : α → Finset β} [Fintype β] [DecidableEq β] [DecidableEq α] :
  (s1 ∪ s2).biInter f = s1.biInter f ∩ s2.biInter f :=
  by
    induction s1 using Finset.cons_induction with
    | empty => ext; simp [Fintype.complete]
    | cons a s1' h ih => aesop

def List.biInter {α β} [Fintype β] [DecidableEq β] (l : List α) (f : α → Finset β) : Finset β :=
  Finset.biInter (l.map f).toFinset id

@[simp]
lemma List.biInter_empty {α β} [Fintype β] [DecidableEq β] {f : α → Finset β} :
  biInter [] f = Fintype.elems :=
  by simp [biInter]

@[simp]
lemma List.biInter_cons {α β} [Fintype β] [DecidableEq β] {f : α → Finset β} {a as} :
  biInter (a :: as) f = f a ∩ biInter as f :=
  by
    ext b
    simp [biInter]

@[simp]
lemma List.biInter_singleton {α β} [Fintype β] [DecidableEq β] {f : α → Finset β} {a} :
  biInter [a] f = f a :=
  by simp [biInter]

@[simp]
lemma List.mem_biInter {α β} [Fintype β] [DecidableEq β] {l : List α} {f : α → Finset β} :
  ∀ b, b ∈ l.biInter f ↔ ∀ a ∈ l, b ∈ f a :=
  by simp [List.biInter]
-/
@[simp]
public lemma Fintype.elems_eq_univ {α} [h : Fintype α] : h.elems = Finset.univ := by
  ext a
  simp [Fintype.complete]

public def Vector.elems {α} [h : Fintype α] [DecidableEq α] : (n : ℕ) → Finset (Vector α n)
  | 0 => {#v[]}
  | n + 1 => Finset.biUnion (elems n) fun v ↦ h.elems.image v.push

public instance {α} [Fintype α] [DecidableEq α] {n} : Fintype (Vector α n) where
  elems := Vector.elems n
  complete := by
    induction n with
    | zero => simp [Vector.elems]
    | succ n ih =>
      simp only [Vector.elems, Fintype.elems_eq_univ, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_univ, true_and, Vector.forall_cons_iff]
      intro a v
      use v, ih v, a

/-- Variant of `Vector.mem_iff_getElem` using `Fin`. -/
public lemma Vector.mem_iff_getElem' {α n} {a : α} {xs : Vector α n} :
    a ∈ xs ↔ ∃ i : Fin n, xs[i] = a := by
  simp only [mem_iff_getElem, Fin.getElem_fin]
  constructor
  · rintro ⟨i, hi, h1⟩
    use ⟨i, hi⟩
  · grind only [usr Fin.isLt]

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

/-
/--
Given a list of lists, combine every element of the first list with every element of the second
list, every element of third list etc using the combinator `f`.
-/
def List.multiply {α β} (f : α → β → β) (init : β) : List (List α) → List β
| [] => [init]
| [] :: _ => []
| (a :: as) :: ass => (ass.multiply f init).map (f a ·) ++ multiply f init (as :: ass)
-/

public def List.multiply {α} : List (List (List α)) → List (List α) :=
  List.mulr (· ++ ·) []

@[simp]
public lemma List.multiply_nil {α} : multiply (α := α) [] = [[]] := by
  simp [multiply, mulr]

@[simp]
public lemma List.multiply_cons {α} {asss} {ass : List (List α)} :
    multiply (ass :: asss) = ass.flatMap (fun as ↦ (multiply asss).map (as ++ ·)) := by
  simp [multiply, mulr, productWith, List.product.eq_1, List.map_flatMap]
  congr
/-
@[simp]
lemma List.mem_multiply_cons {α} {asss ass} {as : List α} :
  as ∈ multiply (ass :: asss) ↔ ∃ as1 as2, as = as1 ++ as2 ∧ as1 ∈ ass ∧ as2 ∈ multiply asss :=
  by
    simp [multiply, mulr, productWith]
    grind

lemma List.mem_multiply {α} {asss as} :
  as ∈ multiply asss ↔ ∃ f : Fin asss.length → List α,
  as = (List.finRange asss.length).flatMap f ∧ ∀ i : Fin asss.length, f i ∈ asss[i] :=
  by
    constructor
    · induction asss generalizing as with
      | nil =>
        simp [multiply, mulr, foldr_nil]
      | cons ass asss ih =>
        simp_all [multiply, mulr, foldr_cons]
        rintro as has as' h1 rfl
        rcases ih h1 with ⟨f, rfl, h2⟩
        let f' : Fin (asss.length + 1) → List α := fun i ↦
          match i with
          | 0 => as
          | ⟨i + 1, h⟩ => f ⟨i, by omega⟩
        use f'
        constructor
        · simp_all [f', List.finRange_succ, List.flatMap_map]
          congr
        · grind
    · induction asss generalizing as with
      | nil =>
        simp [multiply, mulr, foldr_nil]
      | cons ass asss ih =>
        simp_all [multiply, mulr, foldr_cons]
        intro f rfl h
        let f' : Fin asss.length → List α := fun i ↦ f i.succ
        use f 0, h 0, flatMap f' (finRange asss.length)
        specialize @ih (flatMap f' (finRange asss.length)) f' rfl
        simp_all [f', List.finRange_succ, List.flatMap_map]
        apply ih
        intro i
        apply h
-/


public lemma List.map_toFinset {α β} [DecidableEq α] [DecidableEq β] {f : α → β} {xs : List α} :
    (xs.map f).toFinset = xs.toFinset.image f := by
  ext b
  simp

public lemma List.length_flatten_short {α} (ass : List (List α)) (h : ∀ as ∈ ass, as.length < 2) :
    ass.flatten.length ≤ ass.length := by
  induction ass with
  | nil => simp
  | cons as ass ih => grind

@[simp]
public lemma Set.inter_compl_subset_union_compl {α} {s1 s2 s3 s4 : Set α} :
    s1 ∩ s2ᶜ ⊆ s3 ∪ s4ᶜ ↔ s1 ∩ s4 ⊆ s3 ∪ s2 := by
  simp [Set.subset_def]
  grind
