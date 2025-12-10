import Validator.Basic
import Validator.InductiveCertificate
import Validator.StateSetFormalism.Formalism

namespace Validator.ProofSystem
open Formalism

/-! # Proof System for Certifying Unsolvability

We define the proof system for unsolvability described in [ES2019],
which was originally introduced in [ERH2017]. More specifically this file contains
* the definition of dead states and dead state sets,
* a shallow embedding of the proof system, and
* proofs for soundness and completeness of the system.

## Dead States and Dead State Sets
-/

/-- A state `s` is dead iff it is not part of any plan for `pt`. -/
abbrev DeadState {n} (pt : STRIPS n) (s : State n) : Prop :=
  ∀ plan : Plan pt pt.init, s ∉ plan.path

/-- Alternative definiton of dead states. -/
lemma dead_state_iff {n} (pt : STRIPS n) (s : State n) :
  DeadState pt s ↔ ¬ Reachable pt pt.init s ∨ UnsolvableState pt s := by
  simp [DeadState, UnsolvableState]
  constructor
  · contrapose
    simp
    intro π plan
    use Plan.mk plan.last (π ++ plan.path) plan.goal
    simp [Path.mem_append]
    exact Or.inl (Path.last_mem π)
  · rintro h ⟨s', π, hgoal⟩ hs
    simp at hs
    obtain ⟨π₁, π₂⟩ := Path.split π hs
    rcases h with h | h
    · exact h.false π₁
    · exact h.false (Plan.mk s' π₂ hgoal)

/-- A set of states is dead iff all its members are dead. -/
abbrev Dead {n} (pt : STRIPS n) (S : States n) : Prop :=
  ∀ s ∈ S, DeadState pt s

/-! ## Proof System -/
/--
A derivation (or proof tree) in the proof system deriving the statement `conclusion`.
-/
inductive Derivation {n} (pt : STRIPS n) : (conclusion : Prop) → Type 1
/-- Basic statement 1 -/
| B1 R [Formalism pt R] {S S'} :
  IsLiteralInter pt R S →
  IsLiteralUnion pt R S' →
  (S ⊆ S') →
  Derivation pt (S ⊆ S')
/-- Basic statement 2 -/
| B2 R [Formalism pt R] {S S'} :
  IsProgrInter pt R S →
  IsLiteralUnion pt R S' →
  (S ⊆ S') →
  Derivation pt (S ⊆ S')
/-- Basic statement 3 -/
| B3 R [Formalism pt R] {S S'} :
  IsRegrInter pt R S →
  IsLiteralUnion pt R S' →
  (S ⊆ S') →
  Derivation pt (S ⊆ S')
/-- Basic statement 4 -/
| B4 R R' [Formalism pt R] [Formalism pt R'] {S S'} :
  IsLiteral pt R S →
  IsLiteral pt R' S' →
  S ⊆ S' →
  Derivation pt (S ⊆ S')
/-- Basic statement 5 -/
| B5 (A A' : Actions n) : A ⊆ A' → Derivation pt (A ⊆ A')
/-- Empty set Dead -/
| ED : Derivation pt (Dead pt ∅)
/-- Union Dead -/
| UD S S' :
  Derivation pt (Dead pt S) →
  Derivation pt (Dead pt S') →
  Derivation pt (Dead pt (S ∪ S'))
/-- Subset Dead -/
| SD S S' :
  Derivation pt (Dead pt S') →
  Derivation pt (S ⊆ S') →
  Derivation pt (Dead pt S)
/-- Progression Goal -/
| PG S S' :
  Derivation pt (pt.progression S pt.actions ⊆ S ∪ S') →
  Derivation pt (Dead pt S') →
  Derivation pt (Dead pt (S ∩ pt.goal_states)) →
  Derivation pt (Dead pt S)
/-- Progression Initial -/
| PI S S' :
  Derivation pt (pt.progression S pt.actions ⊆ S ∪ S') →
  Derivation pt (Dead pt S') →
  Derivation pt ({pt.init} ⊆ S) →
  Derivation pt (Dead pt Sᶜ)
/-- Regression Goal -/
| RG S S' :
  Derivation pt (pt.regression S pt.actions ⊆ S ∪ S') →
  Derivation pt (Dead pt S') →
  Derivation pt (Dead pt (Sᶜ ∩ pt.goal_states)) →
  Derivation pt (Dead pt Sᶜ)
/-- Regression Initial -/
| RI S S' :
  Derivation pt (pt.regression S pt.actions ⊆ S ∪ S') →
  Derivation pt (Dead pt S') →
  Derivation pt ({pt.init} ⊆ Sᶜ) →
  Derivation pt (Dead pt S)
/-- Conclusion Initial -/
| CI : Derivation pt (Dead pt {pt.init}) → Derivation pt (Unsolvable pt)
/-- Conclusion Goal -/
| CG : Derivation pt (Dead pt pt.goal_states) → Derivation pt (Unsolvable pt)
/-- Union Right -/
| UR {α} (E E' : Set α) : Derivation pt (E ⊆ E ∪ E')
/-- Union Left -/
| UL {α} (E E' : Set α) : Derivation pt (E ⊆ E' ∪ E)
/-- Intersection Right -/
| IR {α} (E E' : Set α) : Derivation pt (E ∩ E' ⊆ E)
/-- Intersection Left -/
| IL {α} (E E' : Set α) : Derivation pt (E' ∩ E ⊆ E)
/-- DIstributivity -/
| DI {α} (E E' E'' : Set α) : Derivation pt ((E ∪ E') ∩ E'' ⊆ (E ∩ E'') ∪ (E' ∩ E''))
/-- Subset Union -/
| SU {α} (E E' E'' : Set α) :
  Derivation pt (E ⊆ E'') →
  Derivation pt (E' ⊆ E'') →
  Derivation pt (E ∪ E' ⊆ E'')
/-- Subset Intersection -/
| SI {α} (E E' E'' : Set α) :
  Derivation pt (E ⊆ E') →
  Derivation pt (E ⊆ E'') →
  Derivation pt (E ⊆ E' ∩ E'')
/-- Subset Transitivity -/
| ST {α} (E E' E'' : Set α) :
  Derivation pt (E ⊆ E') →
  Derivation pt (E' ⊆ E'') →
  Derivation pt (E ⊆ E'')
/-- Action Transitivity -/
| AT S S' A A' :
  Derivation pt (pt.progression S A ⊆ S') →
  Derivation pt (A' ⊆ A) →
  Derivation pt (pt.progression S A' ⊆ S')
/-- Action Union -/
| AU S S' A A' :
  Derivation pt (pt.progression S A ⊆ S') →
  Derivation pt (pt.progression S A' ⊆ S') →
  Derivation pt (pt.progression S (A ∪ A') ⊆ S')
/-- Progression Transitivity -/
| PT S S' S'' A :
  Derivation pt (pt.progression S A ⊆ S'') →
  Derivation pt (S' ⊆ S) →
  Derivation pt (pt.progression S' A ⊆ S'')
/-- Progression Union -/
| PU S S' S'' A :
  Derivation pt (pt.progression S A ⊆ S'') →
  Derivation pt (pt.progression S' A ⊆ S'') →
  Derivation pt (pt.progression (S ∪ S') A ⊆ S'')
/-- Progression to Regression -/
| PR S S' A :
  Derivation pt (pt.progression S A ⊆ S') →
  Derivation pt (pt.regression (S'ᶜ) A ⊆ Sᶜ)
/-- Regression to Progression -/
| RP S S' A :
  Derivation pt (pt.regression (S'ᶜ) A ⊆ Sᶜ) →
  Derivation pt (pt.progression S A ⊆ S')

/-! ## Soundness of the Proof System -/

private lemma progression_aux {n} {pt : STRIPS n} {S S'} {s1 s2}
  (hs1 : s1 ∈ S) (π₁ : Path pt pt.init s1) (π₂ : Path pt s1 s2) (hgoal : pt.GoalState s2)
  (h1 : pt.progression S pt.actions ⊆ S ∪ S') (h2 : Dead pt S') : ∀ s ∈ π₂, s ∈ S :=
  by
    induction π₂ with
    | empty s =>
      simp
      exact hs1
    | @cons a s1 s2 s3 ha succ π₂ ih =>
      intro s' hs'
      simp at hs'
      cases hs' with
      | inl heq =>
        subst heq
        exact hs1
      | inr hs' =>
        have hs2 : s2 ∈ pt.progression S pt.actions :=
          mem_progression_of_successor hs1 ha succ
        have : s2 ∉ S' := by
          by_contra h
          have h' : DeadState pt s2 := h2 s2 h
          let π : Path pt pt.init s3 := π₁ ++ Path.cons a s2 ha succ π₂
          apply h' (Plan.mk s3 π hgoal)
          simp [π, Path.mem_append]
          suffices s2 ∈ π₂ by simp_all
          exact Path.first_mem π₂
        have hs2 : s2 ∈ S := by
          apply h1 at hs2
          simp_all
        exact ih hs2 (Path.snoc a s1 ha π₁ succ) hgoal s' hs'

lemma progression_goal {n} {pt : STRIPS n} {S S'}
  (h1 : pt.progression S pt.actions ⊆ S ∪ S')
  (h2 : Dead pt S')
  (h3 : Dead pt (S ∩ pt.goal_states)) :
  Dead pt S :=
  by
    rintro s hs ⟨s', π, hgoal⟩ s_in_π
    obtain ⟨π₁, π₂⟩ := Path.split π s_in_π
    have s'_in_π₂ : s' ∈ π₂ := Path.last_mem π₂
    have s'_in_S : s' ∈ S :=
      progression_aux hs π₁ π₂ hgoal h1 h2 s' s'_in_π₂
    have hs' : s' ∈ S ∩ pt.goal_states := by simp_all [STRIPS.goal_states]
    apply h3 s' hs' (Plan.mk s' π hgoal)
    exact Path.last_mem π

lemma progression_initial {n} {pt : STRIPS n} {S S'}
  (h1 : pt.progression S pt.actions ⊆ S ∪ S')
  (h2 : Dead pt S')
  (h3 : {pt.init} ⊆ S) :
  Dead pt (Sᶜ) :=
  by
    rintro s hs ⟨s', π, hgoal⟩ s_in_π
    simp at h3
    have s_in_S : s ∈ S :=
      progression_aux h3 (Path.empty pt.init) π hgoal h1 h2 s s_in_π
    simp at hs
    exact hs s_in_S

-- Unable to use regular induction on π₁ (I assume because pt.init is not a variable)
private lemma regression_aux {n} {pt : STRIPS n} {S S'} {s1 s2}
  (hs1 : s1 ∈ S) (π₁ : Path pt pt.init s1) (π₂ : Path pt s1 s2) (hgoal : pt.GoalState s2)
  (h1 : pt.regression S pt.actions ⊆ S ∪ S') (h2 : Dead pt S') : ∀ s ∈ π₁, s ∈ S :=
  by
    cases heq : π₁ using Path.snocCases with
    | empty s =>
      simp
      exact hs1
    | snoc a s0 ha π₁' succ =>
      intro s' hs'
      simp at hs'
      cases hs' with
      | inl heq =>
        subst heq
        exact hs1
      | inr hs' =>
        have hs0 : s0 ∈ pt.regression S pt.actions :=
          mem_regression_of_successor hs1 ha succ
        have : s0 ∉ S' := by
          by_contra h
          have h' : DeadState pt s0 := h2 s0 h
          let π : Path pt pt.init s2 := π₁' ++ Path.cons a s1 ha succ π₂
          apply h' (Plan.mk s2 π hgoal)
          simp [π, Path.mem_append]
        have hs0 : s0 ∈ S := by
          apply h1 at hs0
          simp_all
        have : π₁'.length < π₁.length := by simp [heq]
        apply regression_aux hs0 π₁' (Path.cons a s1 ha succ π₂) hgoal h1 h2
        exact hs'
  termination_by π₁.length

lemma regression_goal {n} {pt : STRIPS n} {S S'}
  (h1 : pt.regression S pt.actions ⊆ S ∪ S')
  (h2 : Dead pt S')
  (h3 : Dead pt (Sᶜ ∩ pt.goal_states)) :
  Dead pt Sᶜ :=
  by
    rintro s hs ⟨s', π, hgoal⟩ s_in_π
    obtain ⟨π₁, π₂⟩ := Path.split π s_in_π
    have hs' : s' ∈ S := by
      by_contra h
      exact h3 s' (by simp_all [STRIPS.goal_states]) (Plan.mk s' π hgoal) (Path.last_mem π)
    have s_in_S : s ∈ S :=
      regression_aux hs' π (Path.empty s') hgoal h1 h2 s s_in_π
    simp at hs
    exact hs s_in_S

lemma regression_initial {n} {pt : STRIPS n} {S S'}
  (h1 : pt.regression S pt.actions ⊆ S ∪ S')
  (h2 : Dead pt S')
  (h3 : {pt.init} ⊆ Sᶜ) :
  Dead pt S :=
  by
    rintro s hs ⟨s', π, hgoal⟩ s_in_π
    simp at h3
    apply h3
    obtain ⟨π₁, π₂⟩ := Path.split π s_in_π
    apply regression_aux hs π₁ π₂ hgoal h1 h2
    exact Path.first_mem π₁

namespace Derivation

/--
The proof system is sound, i.e. given a derivation in the proof system,
the conclusion of this derivation holds.
-/
theorem soundness {n} {pt : STRIPS n} {conclusion} : (d : Derivation pt conclusion) → conclusion
| B1 _ _ _ h => h
| B2 _ _ _ h => h
| B3 _ _ _ h => h
| B4 _ _ _ _ h => h
| B5 _ _ h => h
| ED => by simp [Dead]
| UD S S' d1 d2 =>
  by
    simp [Dead]
    intro s hs
    cases hs with
    | inl hs =>
      apply d1.soundness
      exact hs
    | inr hs =>
      apply d2.soundness
      exact hs
| SD S S' d1 d2 =>
  by
    simp [Dead]
    intro s hs
    show DeadState pt s
    apply d1.soundness
    apply d2.soundness
    exact hs
| PG S S' d1 d2 d3 =>
  by
    apply progression_goal
    · exact d1.soundness
    · exact d2.soundness
    · exact d3.soundness
| PI S S' d1 d2 d3 =>
  by
    apply progression_initial
    · exact d1.soundness
    · exact d2.soundness
    · exact d3.soundness
| RG S S' d1 d2 d3 =>
  by
    apply regression_goal
    · exact d1.soundness
    · exact d2.soundness
    · exact d3.soundness
| RI S S' d1 d2 d3 =>
  by
    apply regression_initial
    · exact d1.soundness
    · exact d2.soundness
    · exact d3.soundness
| CI d =>
  by
    constructor
    have h : DeadState pt pt.init :=
      d.soundness pt.init (by simp)
    simp [DeadState, Path.first_mem] at h
    exact h
| CG d =>
  by
    constructor
    intro plan
    have h : DeadState pt plan.last :=
      d.soundness plan.last (by simp_all [plan.goal, STRIPS.goal_states])
    apply h plan
    exact Path.last_mem plan.path
| UR E E' => by simp
| UL E E' => by simp
| IR E E' => by simp
| IL E E' => by simp
| DI E E' E'' => by simp [Set.union_inter_distrib_right]
| SU E E' E'' d1 d2 => by
  apply Set.union_subset
  · exact d1.soundness
  · exact d2.soundness
| SI E E' E'' d1 d2 => by
  apply Set.subset_inter
  · exact d1.soundness
  · exact d2.soundness
| ST E E' E'' d1 d2 => by
  apply subset_trans
  · exact d1.soundness
  · exact d2.soundness
| AT S S' A A' d1 d2 => by
  apply subset_trans
  · apply progression_monotone_actions
    exact d2.soundness
  · exact d1.soundness
| AU S S' A A' d1 d2 => by
  rw[progression_union_actions]
  apply Set.union_subset
  · exact d1.soundness
  · exact d2.soundness
| PT S S' S'' A d1 d2 => by
  apply subset_trans
  · apply progression_monotone_states
    exact d2.soundness
  · exact d1.soundness
| PU S S' S'' A d1 d2 => by
  rw[progression_union_states]
  apply Set.union_subset
  · exact d1.soundness
  · exact d2.soundness
| PR S S' A d1 => by
  apply sub_progression_iff_sub_regression.1
  exact d1.soundness
| RP S S' A d1 => by
  apply sub_progression_iff_sub_regression.2
  exact d1.soundness

/-! ## Completeness of the Proof System -/

open IsLiteral IsVariable in
/--
Given an `InductiveCertificate` for a planning task `pt`,
construct a `Derivation` in the proof system showing that `pt` is unsolvable.
-/
def fromInductiveCertificate {n} {pt : STRIPS n} {S} :
  InductiveCertificate pt S → Derivation pt (Unsolvable pt)
| ⟨h1,h2,h3⟩ =>
  by
    apply CI
    · apply SD {pt.init} S
      · apply PG S ∅
        · apply ST (pt.progression S pt.actions) S (S ∪ ∅)
          · apply B2 (States n)
            · exact IsProgrInter.empty <| IsVariableInter.single <| explicit S
            · exact IsLiteralUnion.single <| pos <| explicit S
            · exact h3
          · exact UR S ∅
        · exact ED
        · apply SD (S ∩ pt.goal_states) ∅
          · exact ED
          · apply B1 (States n)
            · exact IsLiteralInter.inter
                (IsLiteralInter.single <| pos <| explicit S)
                (IsLiteralInter.single <| pos <| goal)
            · exact IsLiteralUnion.single <| pos <| empty
            · simp [Set.eq_empty_iff_forall_notMem, STRIPS.goal_states]
              exact h2
      · apply B1 (States n)
        · exact IsLiteralInter.single <| pos <| init
        · exact IsLiteralUnion.single <| pos <| explicit S
        · simp [h1]
/--
The proof system is complete, i.e. if the planning task `pt` is unsolvable,
then there exists a derivation in the proof system showing that `pt` is unsolvable.
-/
theorem completeness {n} {pt : STRIPS n} :
  Unsolvable pt → Nonempty (Derivation pt (Unsolvable pt)) :=
  by
    intro h
    constructor
    apply fromInductiveCertificate
    exact Classical.choose_spec (InductiveCertificate.completeness h)

end Validator.ProofSystem.Derivation
