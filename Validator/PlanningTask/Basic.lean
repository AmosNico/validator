/- TODO : Copyright -/
import Mathlib.Data.Fintype.Powerset
import Validator.PlanningTask.Core

namespace Validator

/-! # Additional definitions for the STRIPS formalism

This file extends `Validator.PlanningTask.Core` by implementing
* new operations for working with `Path`,
* definition for reachability of states,
* methods to get all (goal)states of a planning problem,
* definitions of progression and regression,
* lemmas to work with progression and regression.
-/

/-! ## Path -/
namespace Path

/-! ### snoc -/
/--
In `Path.cons`, paths are expanded by adding states at the front of the path
(leaving the last state unchanged). `Path.snoc` allows to extend the path at the back,
leaving the first state unchanged. The name snoc comes from reading cons in reverse order.
-/
def snoc {n} {pt : STRIPS n} a {s1} s2 {s3} (ha : a ∈ pt.actions)
 (π : Path pt s1 s2) (succ : Successor a s2 s3) : Path pt s1 s3 :=
   match π with
   | empty s => cons a s3 ha succ (empty s3)
   | cons a' s4 ha' succ' π' =>
       let π'' := snoc a s2 ha π' succ
       cons a' s4 ha' succ' π''

/-- The length of a path. -/
def length {n} {pt : STRIPS n} {s s'} : Path pt s s' → ℕ
| empty _ => 0
| cons _ _ _ _ π => π.length + 1

@[simp]
lemma length_snoc {n} {pt : STRIPS n} {a s1 s2 s3}
  {ha : a ∈ pt.actions} {π : Path pt s1 s2} {succ : Successor a s2 s3} :
  length (snoc a s2 ha π succ) = π.length + 1 :=
  by
    induction π with
    | empty s => simp[snoc, length]
    | cons a' s2 ha' succ' π ih => simp [snoc, length, ih]

/--
Convert `Path.cons`, where we have access to the first action and the second state of the path,
to `Path.snoc`, where we have access to the last action and the second to last state of the path.
-/
lemma cons_to_snoc {n} {pt : STRIPS n} {a : Action n} {s1 s2 s3 : State n}
  (ha : a ∈ pt.actions) (succ : Successor a s1 s2) (π : Path pt s2 s3) :
  ∃ s2' a', ∃ (ha' : a' ∈ pt.actions) (π' : Path pt s1 s2') (succ' : Successor a' s2' s3),
  cons a s2 ha succ π = snoc a' s2' ha' π' succ' ∧ π.length = π'.length :=
  by
    cases heq : π with
    | empty s2' =>
      use s1, a, ha, empty s1, succ
      simp [snoc, length]
    | @cons a' s1 s2' s2 ha' succ' π' =>
      -- For termination
      have : π'.length < π.length := by
        subst heq
        simp [length]
      obtain ⟨s2'', a'', ha'', π'', succ'', heq, heq'⟩ := cons_to_snoc ha' succ' π'
      use s2'', a'', ha'', cons a s2 ha succ π'', succ''
      simp only [length, Nat.add_right_cancel_iff]
      rw [heq, heq']
      simp [snoc]

/--
Allows to perform cases with `Path.empty` and `Path.snoc` instead of `Path.empty` and `Path.cons`.
-/
lemma snocCases {n : ℕ} {pt : STRIPS n}
  {motive : (s s' : State n) → Path pt s s' → Prop}
  {s s' : State n} (π : Path pt s s')
  (empty : (s : State n) → motive s s (Path.empty s))
  (snoc : (a : Action n) → {s1 : State n} → (s2 : State n) → {s3 : State n} →
    (ha : a ∈ pt.actions) → (π' : Path pt s1 s2) → (succ : Successor a s2 s3) →
      motive s1 s3 (snoc a s2 ha π' succ)) :
  motive s s' π :=
    match π with
    | .empty s => empty s
    | cons a s2 ha succ π =>
      have ⟨s2', a', ha', π', succ', heq_cons, heq_length⟩ := cons_to_snoc ha succ π
      by
      rw [heq_cons]
      apply snoc

/-! ### append -/

/--
Given a path form a `s1` to `s2` and a path from `s2` to `s3`, we obtain a path from `s1` to `s3`.
-/
def append {n} {pt : STRIPS n} {s1 s2 s3} : Path pt s1 s2 → Path pt s2 s3 → Path pt s1 s3
| empty s, π => π
| cons a s2' ha succ π', π => cons a s2' ha succ (append π' π)

instance {n} {pt : STRIPS n} {s1 s2 s3} :
  HAppend (Path pt s1 s2) (Path pt s2 s3) (Path pt s1 s3) where
  hAppend := append

/-! ### Mem -/

/-- A state `s` is a member of a path `π` if `π` traverses through `s`. -/
def Mem {n} {pt : STRIPS n} {s1 s2} (s : State n) : (π : Path pt s1 s2) → Prop
| empty s' => s = s'
| cons _ _ _ _ π => s = s1 ∨ Mem s π

instance {n} {pt : STRIPS n} {s1 s2} : Membership (State n) (Path pt s1 s2) where
  mem π s := Path.Mem s π

@[simp]
lemma mem_empty {n} {pt : STRIPS n} {s s' : State n} : s ∈ @Path.empty _ pt s' ↔ s = s' :=
  by simp [instMembershipState, Mem]

@[simp]
lemma mem_cons {n : ℕ} {pt : STRIPS n} {a s1 s2 s3} {ha : a ∈ pt.actions}
  {succ : Successor a s1 s2} {π : Path pt s2 s3} {s} :
  s ∈ cons a s2 ha succ π ↔ s = s1 ∨ s ∈ π :=
  by simp [instMembershipState, Path.Mem]

@[simp]
lemma mem_snoc {n : ℕ} {pt : STRIPS n} {a s1 s2 s3} {ha : a ∈ pt.actions}
  {π : Path pt s1 s2} {succ : Successor a s2 s3} {s} :
  s ∈ snoc a s2 ha π succ ↔ s = s3 ∨ s ∈ π :=
  by
    induction π with
    | empty s1 =>
      simp [instMembershipState, snoc]
      tauto
    | @cons a' s1 s2 s2' ha' succ' π ih =>
      simp only [snoc, mem_cons]
      rw [ih]
      tauto

lemma first_mem {n} {pt : STRIPS n} {s1 s2} (π : Path pt s1 s2) : s1 ∈ π :=
  by
    cases π
    all_goals simp

lemma last_mem {n} {pt : STRIPS n} {s1 s2} (π : Path pt s1 s2) : s2 ∈ π :=
  by
    induction π with
    | empty s => simp
    | @cons a s1 s2 s3 ha succ π ih =>
      simp [mem_cons, ih]

lemma mem_append {n} {pt : STRIPS n} {s1 s2 s3} (π₁ : Path pt s1 s2) (π₂ : Path pt s2 s3) :
  ∀ s, s ∈ (π₁ ++ π₂) ↔ s ∈ π₁ ∨ s ∈ π₂ :=
  by
    induction π₁ with
    | empty =>
      simp [instHAppend, Path.append, Path.first_mem]
    | cons =>
      simp_all [instHAppend, Path.append]
      tauto

/-! ### split -/

/--
If a state `s` lies on a path `π` from `s1` to `s2`, then there is a path from the `s1` to `s` and
a path from `s` to `s2`. -/
lemma split {n} {pt : STRIPS n} {s1 s2 s} (π : Path pt s1 s2) (h : s ∈ π) :
  Nonempty (Path pt s1 s × Path pt s s2) :=
  by
  cases π with
  | empty s =>
    simp only [mem_empty] at h
    subst h
    use Path.empty s, Path.empty s
  | cons a s3 ha succ π =>
    simp only [mem_cons] at h
    rcases h with rfl | h
    · use Path.empty s, cons a s3 ha succ π
    · obtain ⟨π₁, π₂⟩ := split π h
      use cons a s3 ha succ π₁, π₂

end Path

/-! ## Additional definitions for STRIPS -/

/-! ### Reachable -/

/--
A state `s'` is reachable from `s` if there is a path from `s` to `s'`.
This is the `Prop` version of `Path`.
-/
abbrev Reachable {n} (pt : STRIPS n) (s s' : State n) : Prop :=
  Nonempty (Path pt s s')

lemma reachable_self {n pt} : ∀ s : State n, Reachable pt s s :=
  by
    intro s
    simp only [Reachable]
    constructor
    exact Path.empty s

namespace STRIPS

/-! ### states and goal_states -/

/-- The set of all goal states of the given planning problem. -/
def goal_states {n} (pt : STRIPS n) : States n :=
  { s | pt.GoalState s }

/-! ### progression and regression -/

/-- The progression of a set of states `S` by an action `a`. -/
def progression' {n} (_ : STRIPS n) (S : States n) (a : Action n) : States n :=
  { s | ∃ s' ∈ S, Successor a s' s }

/-- The progression of a set of states `S` by a set of actions `A`. -/
def progression {n} (pt : STRIPS n) (S : States n) (A : Actions n) : States n :=
  { s | ∃ a ∈ A, s ∈ progression' pt S a }

/-- The regression of a set of states `S` by an action `a`. -/
def regression' {n} (_ : STRIPS n) (S : States n) (a : Action n) : States n :=
  { s | ∃ s' ∈ S, Successor a s s' }

/-- The regression of a set of states `S` by a set of actions `A`. -/
def regression {n} (pt : STRIPS n) (S : States n) (A : Actions n) : States n :=
  { s | ∃ a ∈ A, s ∈ regression' pt S a }

end STRIPS

lemma mem_progression {n} {pt : STRIPS n} {A S} :
  ∀ s : State n, s ∈ pt.progression S A ↔ ∃ a ∈ A, ∃ s' ∈ S, Successor a s' s :=
  by simp [STRIPS.progression, STRIPS.progression']

lemma mem_progression_of_successor {n} {pt : STRIPS n} {S s s' A a}
  (hs : s ∈ S) (ha : a ∈ A) (h : Successor a s s') : s' ∈ pt.progression S A :=
  by
    rw [mem_progression]
    use a, ha, s

lemma progression_union_states {n} {pt : STRIPS n} {S1 S2 A} :
  pt.progression (S1 ∪ S2) A = pt.progression S1 A ∪ pt.progression S2 A :=
  by
    ext s
    simp [mem_progression]
    grind

lemma progression_union_actions {n} {pt : STRIPS n} {S A1 A2} :
  pt.progression S (A1 ∪ A2) = pt.progression S A1 ∪ pt.progression S A2 :=
  by
    ext s
    simp [mem_progression]
    grind

lemma progression_monotone_states {n} {pt : STRIPS n} {A} : Monotone (pt.progression · A) :=
  by
    intro S1 S2 hS s hs
    simp_all only [Set.le_eq_subset, mem_progression]
    obtain ⟨a, ha, s', hs', succ⟩ := hs
    use a, ha, s', hS hs'

lemma progression_monotone_actions {n} {pt : STRIPS n} {S} : Monotone (pt.progression S) :=
  by
    intro A1 A2 hA s hs
    simp_all only [Set.le_eq_subset, mem_progression]
    obtain ⟨a, ha, s', hs', succ⟩ := hs
    use a, hA ha, s'

lemma mem_regression {n} {pt : STRIPS n} {S A} :
 ∀ s : State n, s ∈ pt.regression S A ↔ ∃ a ∈ A, ∃ s' ∈ S, Successor a s s' :=
  by simp [STRIPS.regression, STRIPS.regression']

lemma mem_regression_of_successor {n} {pt : STRIPS n} {S s s' A a}
  (hs : s ∈ S) (ha : a ∈ A) (h : Successor a s' s) : s' ∈ pt.regression S A :=
  by
    rw [mem_regression]
    use a, ha, s

lemma sub_progression_iff_sub_regression {n} {pt : STRIPS n} {S S' A} :
  pt.progression S A ⊆ S' ↔ pt.regression S'ᶜ A ⊆ Sᶜ :=
  by
    constructor
    · intro h1 s hs_regr
      obtain ⟨a, ha, s', hs', succ⟩ := (mem_regression s).1 hs_regr
      simp only [Set.mem_compl_iff] at ⊢ hs'
      by_contra hs1
      apply hs'
      apply h1
      rw [mem_progression]
      use a, ha, s
    · intro h1 s' hs'_progr
      obtain ⟨a, ha, s, hs, succ⟩ := (mem_progression s').1 hs'_progr
      by_contra hs'
      apply Set.mem_compl at hs'
      have hs_regr : s ∈ pt.regression S'ᶜ A := by
        rw [mem_regression]
        use a, ha, s'
      have : s ∈ Sᶜ := h1 hs_regr
      simp_all

end Validator
