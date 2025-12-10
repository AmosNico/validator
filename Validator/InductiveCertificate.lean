/- TODO : copyright -/
import Validator.PlanningTask.Basic

namespace Validator

/-! # Inductive Certificates

We formalize the simple version of Inductive Certificates for unsolvability
of automated planning as introduced in [ERH2017] and [ES2019].
This file includes :
* the definition of inductive sets and inductive certificates,
* soundness of inductive certificates, and
* completeness of inductive certificates.
* the construction of the set of reachable states (which is not needed anymore)
-/

/-! ### Inductive Sets and Inductive Certificates -/

/-- A set `S` is inductive if `S[pt.actions] ⊆ S`. -/
abbrev InductiveSet {n} (pt : STRIPS n) (S : States n) :=
  pt.progression S pt.actions ⊆ S

/--
An inductive certificate for a state `s` is an inductive set containing `s`
which does not contain any goal state.
-/
abbrev InductiveCertificateState {n} (pt : STRIPS n) (s : State n) (S : States n) :=
    s ∈ S ∧ (∀ s ∈ S, ¬ pt.GoalState s) ∧ InductiveSet pt S

/--
An inductive certificate for the a planning task is an inductive certificate for the initial state.
-/
abbrev InductiveCertificate {n} (pt : STRIPS n) (S : States n) :=
  InductiveCertificateState pt pt.init S

namespace InductiveCertificate

/-! ### Soundness of Inductive Certificates -/

theorem soundness' {n} {pt : STRIPS n} {s S} :
  InductiveCertificateState pt s S → UnsolvableState pt s :=
  by
    rintro ⟨hs, h1, h2⟩
    unfold UnsolvableState
    apply IsEmpty.mk
    rintro ⟨s', π, h3⟩
    induction π with
    | empty s' => simp_all
    | @cons a s1 s2 s3 ha h π ih =>
      refine ih ?_ h3
      show s2 ∈ S
      apply h2
      exact mem_progression_of_successor hs ha h

/--
Inductive certificates are sound, i.e. if an inductive certificate exists,
then the planning problem is unsolvable.
-/
theorem soundness {n} {pt : STRIPS n} {S} :
  InductiveCertificate pt S → Unsolvable pt :=
  soundness'

/-! ### Completeness of Inductive Certificates -/

theorem completeness' {n} {pt : STRIPS n} {s} :
  UnsolvableState pt s → ∃ S, InductiveCertificateState pt s S :=
  by
    unfold UnsolvableState
    rintro ⟨h1⟩
    use { s' | Reachable pt s s' }
    simp [InductiveCertificateState]
    split_ands
    · exact reachable_self s
    · intro s' h2 h3
      apply h1
      exact Plan.mk s' h2 h3
    · intro s' h
      simp_all [STRIPS.progression, STRIPS.progression']
      obtain ⟨a, ha, s'', h2, h3⟩ := h
      obtain π : Path pt s s'' := Classical.choice h2
      constructor
      show Path pt s s'
      exact Path.snoc a s'' ha π h3

/--
Inductive certificates are complete, i.e. if a planning problem is unsolvable,
then an inductive certificate for the planning problem exists.
-/
theorem completeness {n} {pt : STRIPS n} :
  Unsolvable pt → ∃ S, InductiveCertificate pt S :=
  completeness'

/-! ### Construction of Reachable States (Unused)

Previously the definition of `States` used `Finset` instead of `Set`.
To construct the set of reachable states in `completeness'`, we had to either show that
the the predicate `Reachable` is decidable, or give a construction for the set of all
reachable states. As the former is usually done by checking whether a state is in the
set of all reachable states, we gave a direct construction.

The following definitions make this construction, but note that all underlying definitions
now use `Set` instead of `Finset`. The construction is not needed anymore, but maybe it is
usefull for someone someday.
-/

/--
The `k`-th expansion of a set of states `S` contains all states which are reachable from
a state in `S` by a path with length at most `k`.
-/
def expand {n} (pt : STRIPS n) (S : States n) : (k : ℕ) → States n
| 0 => S
| k + 1 => S ∪ pt.progression (expand pt S k) pt.actions

lemma expand_progression {n} (pt : STRIPS n) (S : States n) (k : ℕ) :
  expand pt (pt.progression S pt.actions) k = pt.progression (expand pt S k) pt.actions :=
  by
    induction k with
    | zero => simp [expand]
    | succ k ih => rw [expand, ih, expand, progression_union_states]

lemma expand_monotone {n} (pt : STRIPS n) (S : States n) : Monotone (expand pt S) :=
  by
    apply monotone_nat_of_le_succ
    intro k
    induction k with
    | zero => simp [expand]
    | succ k ih =>
      rw [expand, expand]
      apply Set.union_subset_union_right
      apply progression_monotone_states
      exact ih

lemma expand_monotone_states {n} (pt : STRIPS n) (k : ℕ) : Monotone (expand pt · k) :=
  by
    intro S1 S2 hS
    induction k with
    | zero =>
      simp [expand]
      exact hS
    | succ k ih =>
      simp_all [expand, Set.subset_union_of_subset_left]
      apply Set.subset_union_of_subset_right
      apply progression_monotone_states
      exact ih

/-- A set over a finite type is finite. -/
noncomputable instance {α} [Fintype α] {S : Set α} : Fintype (↑S) :=
  Fintype.ofFinite S

/--
`Finset` over a finite type `α` forms a complete lattice.
This uses that `Finset α` is a finite type, and therefore every set over `Finset α` is finite,
so one can use `Finset.inf` and `Finset.sup`.
-/
noncomputable instance {α} [Fintype α] [DecidableEq α] : CompleteLattice (Finset α) where
  sSup S := Finset.sup (Set.toFinset S) id

  le_sSup := by
    intro S as has a ha
    simp
    use as

  sSup_le := by
    intro S as h
    apply Finset.sup_le
    simp_all

  sInf S := Finset.inf (Set.toFinset S) id

  sInf_le := by
    intro S as has
    apply Finset.inf_le
    simp
    exact has

  le_sInf := by
    intro S as ha
    apply Finset.le_inf
    simp_all

/--
The set of all reachable_states reachable from `s` can be constructed as the union
of `expand pt {s} k` for all natural numbers `k`.
-/
noncomputable def reachable_states {n} (pt : STRIPS n) (s : State n) : States n :=
  ⨆ k : ℕ, expand pt {s} k

/--
If `f` is a monotone function from `ℕ` to a complete lattice where the relation `>` is
well-founded, then there exists `n ∈ ℕ` such that the suppremum `⨆ k : ℕ, f k` is equal to
`f n`.

This implies that there exists `n` such that `reachable_states pt s` is equal to
the `n`-th expansion `expand pt {s} n`.
-/
lemma exists_eq_iSup_monotone {β : Type} [CompleteLattice β] [WellFoundedGT β]
  (f : ℕ → β) (hf : Monotone f) : ∃ n, f n = ⨆ k : ℕ, f k :=
  by
    obtain ⟨I, hI⟩ := Finset.exists_sup_eq_iSup f
    rw [← hI]
    cases Classical.em I.Nonempty with
    | inl h =>
      use I.sup id
      exact Finset.comp_sup_eq_sup_comp_of_nonempty hf h
    | inr h =>
      simp at h
      subst h
      use 0
      apply iSup_eq_bot.1 (symm hI)

/-- States in the `k`-th expansion of `s` are reachable from `s`. -/
lemma mem_reachable_helper {n} {pt : STRIPS n} {s s'} {k}
  (hs' : s' ∈ expand pt {s} k) : Reachable pt s s' :=
  by
    induction k generalizing s' with
    | zero =>
      simp [expand] at hs'
      rw [hs']
      exact reachable_self s
    | succ k ih =>
      rw [expand] at hs'
      simp at hs'
      cases hs' with
      | inl hs' =>
        rw [hs']
        exact reachable_self s
      | inr hs' =>
        simp [mem_progression] at hs'
        obtain ⟨a, ha, s'', hs'', succ⟩ := hs'
        obtain ⟨π⟩ := ih hs''
        constructor
        show Path pt s s'
        exact Path.snoc a s'' ha π succ

/--
The members of `reachable_states` are exactly the states in the state space which are reachable.
-/
theorem mem_reachable {n} (pt : STRIPS n) {s s'} : s' ∈ reachable_states pt s ↔ Reachable pt s s' :=
  by
    unfold reachable_states
    constructor
    · obtain ⟨k, hk⟩ : ∃ k, expand pt {s} k = ⨆ a, expand pt {s} a :=
        exists_eq_iSup_monotone (expand pt {s}) (expand_monotone pt {s})
      rw [← hk]
      exact mem_reachable_helper
    · rintro ⟨π⟩
      suffices {s'} ≤ ⨆ k, expand pt {s} k from by simp_all
      apply le_iSup_of_le π.length
      induction π with
      | empty s'' => simp [Path.length, expand]
      | @cons a s1 s2 s3 ha succ π ih =>
        simp [Path.length, expand, ← expand_progression]
        apply Or.inr
        simp at ih
        have h : {s2} ⊆ pt.progression {s1} pt.actions := by
          simp
          exact mem_progression_of_successor (by simp) ha succ
        apply expand_monotone_states pt π.length h
        apply ih

end Validator.InductiveCertificate
