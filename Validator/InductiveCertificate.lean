module

public import Strips.PlanningTask

public section

open STRIPS

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
abbrev InductiveSet {n} (pt : PlanningTask n) (S : States n) :=
  pt.progression S pt.actions ⊆ S

/--
An inductive certificate for a state `s` is an inductive set containing `s`
which does not contain any goal state.
-/
abbrev InductiveCertificateState {n} (pt : PlanningTask n) (s : State n) (S : States n) :=
  s ∈ S ∧ (∀ s ∈ S, ¬ pt.GoalState s) ∧ InductiveSet pt S

/--
An inductive certificate for the a planning task is an inductive certificate for the initial state.
-/
abbrev InductiveCertificate {n} (pt : PlanningTask n) (S : States n) :=
  InductiveCertificateState pt pt.init S

namespace InductiveCertificate

/-! ### Soundness of Inductive Certificates -/

theorem soundness' {n} {pt : PlanningTask n} {s S} :
    InductiveCertificateState pt s S → pt.UnsolvableState s := by
  rintro ⟨hs, h1, h2⟩
  constructor
  rintro ⟨s', π, h3⟩
  induction π with
  | empty s' => exact h1 s' hs h3
  | @cons a s1 s2 s3 ha h π ih =>
    refine ih ?_ h3
    show s2 ∈ S
    apply h2
    exact pt.mem_progression_of_successor hs ha h

/--
Inductive certificates are sound, i.e. if an inductive certificate exists,
then the planning problem is unsolvable.
-/
theorem soundness {n} {pt : PlanningTask n} {S} : InductiveCertificate pt S → pt.Unsolvable :=
  soundness'

/-! ### Completeness of Inductive Certificates -/

theorem completeness' {n} {pt : PlanningTask n} {s} :
    pt.UnsolvableState s → ∃ S, InductiveCertificateState pt s S := by
  rintro ⟨h1⟩
  use { s' | pt.Reachable s s' }
  simp only [InductiveCertificateState, Set.mem_setOf_eq, Nonempty.forall]
  split_ands
  · exact pt.reachable_self s
  · intro s' π h3
    apply h1
    exact ⟨s', π, h3⟩
  · intro s' h
    simp only [pt.mem_progression, Set.mem_setOf_eq] at h
    rcases h with ⟨a, ha, s'', h2, h3⟩
    obtain π : pt.Path s s'' := Classical.choice h2
    constructor
    show pt.Path s s'
    exact PlanningTask.Path.snoc a s'' ha π h3

/--
Inductive certificates are complete, i.e. if a planning problem is unsolvable,
then an inductive certificate for the planning problem exists.
-/
theorem completeness {n} {pt : PlanningTask n} : pt.Unsolvable → ∃ S, InductiveCertificate pt S :=
  completeness'

end Validator.InductiveCertificate

end
