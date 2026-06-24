module

public import Validator.PlanningTask.Basic

public section

namespace Validator

/-! # Inductive Certificates

We formalize the simple version of Inductive Certificates for unsolvability
of automated planning as introduced in [ERH2017] and [ES2019].
This file includes :
* the definition of inductive sets and inductive certificates,
* soundness of inductive certificates, and
* completeness of inductive certificates.
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
    InductiveCertificateState pt s S → UnsolvableState pt s := by
  rintro ⟨hs, h1, h2⟩
  constructor
  rintro ⟨s', π, h3⟩
  induction π with
  | empty s' => exact h1 s' hs h3
  | @cons a s1 s2 s3 ha h π ih =>
    refine ih ?_ h3
    show s2 ∈ S
    apply h2
    exact STRIPS.mem_progression_of_successor hs ha h

/--
Inductive certificates are sound, i.e. if an inductive certificate exists,
then the planning problem is unsolvable.
-/
theorem soundness {n} {pt : STRIPS n} {S} : InductiveCertificate pt S → Unsolvable pt :=
  soundness'

/-! ### Completeness of Inductive Certificates -/

theorem completeness' {n} {pt : STRIPS n} {s} :
    UnsolvableState pt s → ∃ S, InductiveCertificateState pt s S := by
  unfold UnsolvableState
  rintro ⟨h1⟩
  use { s' | Reachable pt s s' }
  simp only [InductiveCertificateState, Set.mem_setOf_eq, Nonempty.forall]
  split_ands
  · exact reachable_self s
  · intro s' π h3
    apply h1
    exact Plan.mk s' π h3
  · intro s' h
    simp only [STRIPS.mem_progression, Set.mem_setOf_eq] at h
    rcases h with ⟨a, ha, s'', h2, h3⟩
    obtain π : Path pt s s'' := Classical.choice h2
    constructor
    show Path pt s s'
    exact Path.snoc a s'' ha π h3

/--
Inductive certificates are complete, i.e. if a planning problem is unsolvable,
then an inductive certificate for the planning problem exists.
-/
theorem completeness {n} {pt : STRIPS n} : Unsolvable pt → ∃ S, InductiveCertificate pt S :=
  completeness'

end Validator.InductiveCertificate

end
