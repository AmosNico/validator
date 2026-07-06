module

public import Validator.Certificate.SetExpr

open Validator STRIPS

public structure Constraint (α : Type) where

  prop : α → Prop

  verify' :  Result α prop

  elim_exists :
    (∃ a, prop a) → {a // prop a ∧ ∀ a', prop a' → a' = a}

  message : Option String := none

namespace Constraint

variable {n : ℕ} {pt : PlanningTask n}

open ConstraintType

public def elim_exists_0 {prop : Unit → Prop} :
    (∃ v, prop v) → {v // prop v ∧ ∀ v', prop v' → v' = v} := by
  intro h'
  use ()
  rcases h' with ⟨⟨⟩, hv⟩
  simp_all

macro "elim_exists_1" e:term : tactic => do
  `(tactic|
    intro h <;>
    cases heq : $e with
    | some S =>
      cases S
      all_goals simp_all
      rename_i S'ᵢ
      exact ⟨S'ᵢ, by simp_all⟩
    | none => simp_all)

macro "elim_exists_2" e:term : tactic => do
  `(tactic|
    intro h <;>
    simp_all <;>
    cases heq : $e with
    | some S =>
      cases S
      all_goals simp_all
      rename_i S'ᵢ S''ᵢ
      exact ⟨(S'ᵢ, S''ᵢ), by simp_all⟩
    | none => simp_all)

public abbrev valid {α} (h : Constraint α) : Prop
  := ∃ a, h.prop a

/-
  TODO : Error messages in verify can be unclear (mostly in combination with eq, leftEq etc.),
  but improving them would likely require significant changes. For now it is good enough.
-/
public def verify {α} (h : Constraint α) : Result α (h.prop) :=
  withErrorMessage h.message h.verify'

public def seq {α1 α2} (h1 : Constraint α1) (h2 : α1 → Constraint α2) : Constraint (α1 × α2) where

  prop := fun ⟨a1, a2⟩ ↦ h1.prop a1 ∧ (h2 a1).prop a2

  verify' := do
    let ⟨a1, ha1⟩ ← h1.verify
    let ⟨a2, ha2⟩ ← (h2 a1).verify
    return ⟨(a1, a2), by simp_all⟩

  elim_exists h0 := by
    simp_all only [Prod.exists, exists_and_left, and_imp, Prod.forall]
    have h3 : ∃ v1, h1.prop v1 := by
      rcases h0 with ⟨v1, hv1, _⟩
      use v1, hv1
    obtain ⟨v1, hv1, h4⟩ := h1.elim_exists h3
    have h5 : ∃ v2, (h2 v1).prop v2 := by
      rcases h0 with ⟨v1', hv1', v2, hv2⟩
      rw [h4 v1' hv1'] at hv2
      use v2
    obtain ⟨v2, hv2, h6⟩ := (h2 v1).elim_exists h5
    exact ⟨(v1, v2), by simp_all⟩

@[simp]
public lemma seq.prop_eq {α1 α2} {a a'} (h : Constraint α1) (h' : α1 → Constraint α2) :
    (h.seq h').prop (a, a') = (h.prop a ∧ (h' a).prop a') := (rfl)

public def and {α1 α2} (h1 : Constraint α1) (h2 : Constraint α2) : Constraint (α1 × α2) where

  prop := fun ⟨a1, a2⟩ ↦ h1.prop a1 ∧ h2.prop a2

  verify' := do
    let ⟨a1, ha1⟩ ← h1.verify
    let ⟨a2, ha2⟩ ← h2.verify
    return ⟨(a1, a2), by simp_all⟩

  elim_exists h0 := by
    simp_all only [Prod.exists, exists_and_left, exists_and_right, and_imp, Prod.forall]
    obtain ⟨v1, hv1, h1⟩ := h1.elim_exists h0.1
    obtain ⟨v2, hv2, h2⟩ := h2.elim_exists h0.2
    exact ⟨(v1, v2), by simp_all⟩

infixr:70 "∧ᶜ" => and

@[simp]
public lemma and.prop_eq {α1 α2} {a a'} (h : Constraint α1) (h' : Constraint α2) :
    (h ∧ᶜ h').prop (a, a') = (h.prop a ∧ h'.prop a') := (rfl)

@[simp]
lemma and.valid_eq {α1 α2} (h : Constraint α1) (h' : Constraint α2) :
    (h ∧ᶜ h').valid = (h.valid ∧ h'.valid) := by
  simp [and]

def eq (h : Constraint ℕ) (T : SetType) (Eᵢ : ℕ) : Constraint Unit where

    prop := fun _ ↦ h.prop Eᵢ

    verify' := do
      let ⟨E'ᵢ, h'⟩ ← h.verify'
      if heq : Eᵢ = E'ᵢ
      then return ⟨(), by simp_all⟩
      else T.toConstraintType.throw_not_eq Eᵢ E'ᵢ

    elim_exists := elim_exists_0

    message := h.message

@[simp]
lemma eq.prop_eq {T Eᵢ a} (h : Constraint ℕ) : (h.eq T Eᵢ).prop a = h.prop Eᵢ := (rfl)

public def eqState (h : Constraint ℕ) (Eᵢ : ℕ) :=
  eq h SetType.States Eᵢ

@[simp]
public lemma eqState.prop_eq {Sᵢ a} (h : Constraint ℕ) : (h.eqState Sᵢ).prop a = h.prop Sᵢ := (rfl)

public def eqAction (h : Constraint ℕ) (Eᵢ : ℕ) :=
  eq h SetType.Actions Eᵢ

@[simp]
public lemma eqAction.prop_eq {Aᵢ a} (h : Constraint ℕ) : (h.eqAction Aᵢ).prop a = h.prop Aᵢ :=
  (rfl)

public def leftEq (h : Constraint (ℕ × ℕ)) (T : SetType) (E1ᵢ : ℕ) : Constraint ℕ where

  prop := fun E2ᵢ ↦ h.prop (E1ᵢ, E2ᵢ)

  verify' := do
    let ⟨⟨E1'ᵢ, E2ᵢ⟩, h'⟩ ← h.verify'
    if heq : E1ᵢ = E1'ᵢ
    then return (by
      subst heq
      exact ⟨E2ᵢ, by simp_all⟩)
    else T.toConstraintType.throw_not_eq E1ᵢ E1'ᵢ

  elim_exists h' := by
    obtain ⟨⟨E1'ᵢ, E2ᵢ⟩, h1, h2⟩ := h.elim_exists (by tauto)
    use E2ᵢ
    rcases h' with ⟨E2'ᵢ, h'⟩
    obtain ⟨rfl, rfl⟩ := h2 (E1ᵢ, E2'ᵢ) h'
    use h'
    intro E2'ᵢ h''
    obtain ⟨rfl, rfl⟩ := h2 (E1ᵢ, E2'ᵢ) h''
    rfl

  message := h.message

@[simp]
public lemma leftEq.prop_eq {T E1ᵢ E2ᵢ} (h : Constraint (ℕ × ℕ)) :
    (h.leftEq T E1ᵢ).prop E2ᵢ = h.prop (E1ᵢ, E2ᵢ) := (rfl)

public def leftEqState (h : Constraint (ℕ × ℕ)) (Eᵢ : ℕ) :=
  Constraint.leftEq h SetType.States Eᵢ

@[simp]
public lemma leftEqState.prop_eq {S1ᵢ S2ᵢ} (h : Constraint (ℕ × ℕ)) :
    (h.leftEqState S1ᵢ).prop S2ᵢ = h.prop (S1ᵢ, S2ᵢ) := (rfl)

public def leftEqAction (h : Constraint (ℕ × ℕ)) (Eᵢ : ℕ) :=
  Constraint.leftEq h SetType.Actions Eᵢ

@[simp]
public lemma leftEqAction.prop_eq {A1ᵢ A2ᵢ} (h : Constraint (ℕ × ℕ)) :
    (h.leftEqAction A1ᵢ).prop A2ᵢ = h.prop (A1ᵢ, A2ᵢ) := (rfl)


public def rightEq (h : Constraint (ℕ × ℕ)) (T : SetType) (E2ᵢ : ℕ) : Constraint ℕ where

  prop := fun E1ᵢ ↦ h.prop (E1ᵢ, E2ᵢ)

  verify' := do
    let ⟨⟨E1ᵢ, E2'ᵢ⟩, h'⟩ ← h.verify'
    if heq : E2ᵢ = E2'ᵢ
    then return (by
      subst heq
      exact ⟨E1ᵢ, by simp_all⟩)
    else T.toConstraintType.throw_not_eq E2ᵢ E2'ᵢ

  elim_exists h' := by
    obtain ⟨⟨E1ᵢ, E2'ᵢ⟩, h1, h2⟩ := h.elim_exists (by tauto)
    use E1ᵢ
    rcases h' with ⟨E1'ᵢ, h'⟩
    obtain ⟨rfl, rfl⟩ := h2 (E1'ᵢ, E2ᵢ) h'
    use h'
    intro E1'ᵢ h''
    obtain ⟨rfl, rfl⟩ := h2 (E1'ᵢ, E2ᵢ) h''
    rfl

  message := h.message

@[simp]
public lemma rightEq.prop_eq {T} {E1ᵢ E2ᵢ} (h : Constraint (ℕ × ℕ)) :
    (h.rightEq T E2ᵢ).prop E1ᵢ = h.prop (E1ᵢ, E2ᵢ) := (rfl)

public def rightEqState (h : Constraint (ℕ × ℕ)) (Sᵢ : ℕ) :=
  Constraint.rightEq h SetType.States Sᵢ

@[simp]
public lemma rightEqState.prop_eq {Eᵢ Sᵢ} (h : Constraint (ℕ × ℕ)) :
    (h.rightEqState Sᵢ).prop Eᵢ = h.prop (Eᵢ, Sᵢ) := (rfl)

public def rightEqAction (h : Constraint (ℕ × ℕ)) (Aᵢ : ℕ) :=
  Constraint.rightEq h SetType.Actions Aᵢ

@[simp]
public lemma rightEqAction.prop_eq {Eᵢ Aᵢ} (h : Constraint (ℕ × ℕ)) :
    (h.rightEqAction Aᵢ).prop Eᵢ = h.prop (Eᵢ, Aᵢ) := (rfl)

-- TODO : check if needed
public def bothEq (h : Constraint (ℕ × ℕ)) (T1 T2 : SetType) (E1ᵢ E2ᵢ : ℕ) : Constraint Unit :=
  (h.leftEq T1 E1ᵢ).eq T2 E2ᵢ

@[simp]
public lemma bothEq.prop_eq {T1 T2 Eᵢ E'ᵢ a} (h : Constraint (ℕ × ℕ)) :
    (h.bothEq T1 T2 Eᵢ E'ᵢ).prop a = h.prop (Eᵢ, E'ᵢ) := (rfl)

public def eqStates (h : Constraint (ℕ × ℕ)) (S1ᵢ S2ᵢ : ℕ) :=
  Constraint.bothEq h SetType.States SetType.States S1ᵢ S2ᵢ

@[simp]
public lemma eqStates.prop_eq {S1ᵢ S2ᵢ a} (h : Constraint (ℕ × ℕ)) :
    (h.eqStates S1ᵢ S2ᵢ).prop a = h.prop (S1ᵢ, S2ᵢ) := (rfl)

public def eqStateAction (h : Constraint (ℕ × ℕ)) (Sᵢ Aᵢ : ℕ) :=
  Constraint.bothEq h SetType.States SetType.Actions Sᵢ Aᵢ

@[simp]
public lemma eqStateAction.prop_eq {Sᵢ Aᵢ a} (h : Constraint (ℕ × ℕ)) :
    (h.eqStateAction Sᵢ Aᵢ).prop a = h.prop (Sᵢ, Aᵢ) := (rfl)

def trivial : Constraint Unit where

  prop := fun _ ↦ True

  verify' := pure ⟨(), by simp⟩

  elim_exists := elim_exists_0

def bounds (T : ConstraintType) (limit Eᵢ : ℕ) : Constraint Unit where

  prop := fun _ ↦ Eᵢ < limit

  verify' :=
    if h : Eᵢ < limit
    then return ⟨(), h⟩
    else T.throw_out_of_bounds Eᵢ

  elim_exists := elim_exists_0

@[simp]
lemma bounds.prop_eq {T limit Eᵢ a} : (bounds T limit Eᵢ).prop a ↔ Eᵢ < limit := by
  simp [bounds]

@[simp]
lemma bounds.valid_eq {T} {limit Eᵢ} : (bounds T limit Eᵢ).valid ↔ Eᵢ < limit := by
  apply Iff.intro
  · rintro ⟨⟨⟩, h⟩
    exact h
  · intro h
    use ()
    simp_all

public def actionBounds limit Aᵢ :=
  bounds ActionSetConstraint limit Aᵢ

@[simp]
lemma actionBounds.prop_eq {limit Aᵢ a} : (actionBounds limit Aᵢ).prop a ↔ Aᵢ < limit := by rfl

public def stateBounds limit Sᵢ :=
  bounds StateSetConstraint limit Sᵢ

@[simp]
lemma stateBounds.prop_eq {limit Sᵢ a} : (stateBounds limit Sᵢ).prop a ↔ Sᵢ < limit := by rfl

public def knowledgeBounds limit Kᵢ :=
  bounds KnowledgeConstraint limit Kᵢ

@[simp]
public lemma knowledgeBounds.prop_eq {limit Kᵢ a} :
    (knowledgeBounds limit Kᵢ).prop a ↔ Kᵢ < limit := by rfl

abbrev setBounds (S : SetType) limit Eᵢ :=
  bounds S.toConstraintType limit Eᵢ

public def actionBounds' (C : Certificate pt) (Aᵢ : ℕ) :
  Constraint Unit where

  prop := fun _ ↦ Aᵢ < C.actions.size

  verify' :=
    if h : Aᵢ < C.actions.size
    then return ⟨(), h⟩
    else ActionSetConstraint.throw_out_of_bounds Aᵢ

  elim_exists := elim_exists_0

@[simp]
public lemma actionBounds'.prop_eq {C : Certificate pt} {Aᵢ a} :
    (actionBounds'  C Aᵢ).prop a ↔ Aᵢ < C.actions.size := by
  simp only [actionBounds', ExceptT.stM_eq]

public def stateBounds' (C : Certificate pt) (Sᵢ : ℕ) :
  Constraint Unit where

  prop := fun _ ↦ Sᵢ < C.states.size

  verify' :=
    if h : Sᵢ < C.states.size
    then return ⟨(), h⟩
    else StateSetConstraint.throw_out_of_bounds Sᵢ

  elim_exists := elim_exists_0

@[simp]
public lemma stateBounds'.prop_eq {C : Certificate pt} {Sᵢ a} :
    (stateBounds' C Sᵢ).prop a ↔ Sᵢ < C.states.size := by rfl

public abbrev setBounds' (C : Certificate pt) : (S : SetType) →  ℕ → Constraint Unit
  | SetType.Actions, Aᵢ => actionBounds' C Aᵢ
  | SetType.States, Sᵢ =>  stateBounds' C Sᵢ


public def isActionAll (C : Certificate pt) (Aᵢ : ℕ) : Constraint Unit where

  prop := fun _ ↦ C.actions[Aᵢ]? = ActionSetExpr.all

  verify' :=
    match heq : C.actions[Aᵢ]? with
    | some ActionSetExpr.all => return ⟨(), by simp⟩
    | some A => ActionSetConstraint.throw_unexpected Aᵢ ActionSetExpr.all A
    | none => ActionSetConstraint.throw_out_of_bounds Aᵢ

  elim_exists := elim_exists_0

  message := s!"Verifying that action set  #{Aᵢ} is the set of all actions"

@[simp]
public lemma isActionAll.prop_eq {C : Certificate pt} {Aᵢ a} :
    (isActionAll C Aᵢ).prop a ↔ Aᵢ < C.actions.size ∧ C.actions[Aᵢ]? = ActionSetExpr.all := by
  simp only [isActionAll, iff_and_self]
  exact Array.lt_of_getElem?_eq_some

public def isActionUnion (C : Certificate pt) (Aᵢ : ℕ) : Constraint (ℕ × ℕ) where

  prop := fun (A'ᵢ, A''ᵢ) ↦ C.actions[Aᵢ]? = ActionSetExpr.union A'ᵢ A''ᵢ

  verify' :=
    match C.actions[Aᵢ]? with
    | some (ActionSetExpr.union A'ᵢ A''ᵢ) => pure ⟨(A'ᵢ, A''ᵢ), by simp⟩
    | some A => ActionSetConstraint.throw_unexpected Aᵢ "a union of actions" A
    | none => ActionSetConstraint.throw_out_of_bounds Aᵢ

  elim_exists := by elim_exists_2 C.actions[Aᵢ]?

  message := s!"Verifying that action set #{Aᵢ} is the union of two actions sets"

@[simp]
public lemma isActionUnion.prop_eq {C : Certificate pt} {Aᵢ A'ᵢ A''ᵢ} :
    (isActionUnion C Aᵢ).prop (A'ᵢ, A''ᵢ) ↔
    Aᵢ < C.actions.size ∧ C.actions[Aᵢ]? = ActionSetExpr.union A'ᵢ A''ᵢ := by
  simp only [isActionUnion, eq_mpr_eq_cast, iff_and_self]
  exact Array.lt_of_getElem?_eq_some

open StateSetExpr

public def isStateEmpty (C : Certificate pt) (Sᵢ : ℕ) : Constraint Unit where

  prop := fun _ ↦ C.states[Sᵢ]? = some empty

  verify' :=
  match C.states[Sᵢ]? with
  | some empty => return ⟨(), by simp⟩
  | some S => StateSetConstraint.throw_unexpected Sᵢ (empty (pt := pt)) S
  | none => StateSetConstraint.throw_out_of_bounds Sᵢ

  elim_exists := elim_exists_0

  message := s!"Verifying that state set #{Sᵢ} is {empty (pt := pt)}"

@[simp]
public lemma isStateEmpty.prop_eq {C : Certificate pt} {Sᵢ a} :
    (isStateEmpty C Sᵢ).prop a ↔ Sᵢ < C.states.size ∧ C.states[Sᵢ]? = some empty := by
  simp only [isStateEmpty, iff_and_self]
  exact Array.lt_of_getElem?_eq_some

public def isStateInit (C : Certificate pt) (Sᵢ : ℕ) : Constraint Unit where

  prop := fun _ ↦ C.states[Sᵢ]? = some init

  verify' :=
  match C.states[Sᵢ]? with
  | some init => return ⟨(), by simp⟩
  | some S => StateSetConstraint.throw_unexpected Sᵢ (init (pt := pt)) S
  | none => StateSetConstraint.throw_out_of_bounds Sᵢ

  elim_exists := elim_exists_0

  message := s!"Verifying that state set #{Sᵢ} is {init (pt := pt)}"

@[simp]
public lemma isStateInit.prop_eq {C : Certificate pt} {Sᵢ a} :
    (isStateInit C Sᵢ).prop a ↔ Sᵢ < C.states.size ∧ C.states[Sᵢ]? = some init := by
  simp only [isStateInit, iff_and_self]
  exact Array.lt_of_getElem?_eq_some

public def isStateGoal (C : Certificate pt) (Sᵢ : ℕ) : Constraint Unit where

  prop := fun _ ↦ C.states[Sᵢ]? = some goal

  verify' :=
  match C.states[Sᵢ]? with
  | some goal => return ⟨(), by simp⟩
  | some S => StateSetConstraint.throw_unexpected Sᵢ (goal (pt := pt)) S
  | none => StateSetConstraint.throw_out_of_bounds Sᵢ

  elim_exists := elim_exists_0

  message := s!"Verifying that state set #{Sᵢ} is {goal (pt := pt)}"

@[simp]
public lemma isStateGoal.prop_eq {C : Certificate pt} {Sᵢ a} :
    (isStateGoal C Sᵢ).prop a ↔ Sᵢ < C.states.size ∧ C.states[Sᵢ]? = some goal := by
  simp only [isStateGoal, iff_and_self]
  exact Array.lt_of_getElem?_eq_some

public def isStateNeg (C : Certificate pt) (Sᵢ : ℕ) : Constraint ℕ where

  prop := fun S'ᵢ ↦ C.states[Sᵢ]? = some (neg S'ᵢ)

  verify' :=
    match C.states[Sᵢ]? with
    | some (neg S'ᵢ) => pure ⟨S'ᵢ, by simp⟩
    | some S => StateSetConstraint.throw_unexpected Sᵢ "the complement of a state set" S
    | none => StateSetConstraint.throw_out_of_bounds Sᵢ

  elim_exists := by elim_exists_1 C.states[Sᵢ]?

  message := s!"Verifying that state set #{Sᵢ} is complement of a state set"

@[simp]
public lemma isStateNeg.prop_eq {C : Certificate pt} {Sᵢ S'ᵢ} :
    (isStateNeg C Sᵢ).prop S'ᵢ ↔ Sᵢ < C.states.size ∧ C.states[Sᵢ]? = some (neg S'ᵢ) := by
  simp only [isStateNeg, eq_mpr_eq_cast, iff_and_self]
  exact Array.lt_of_getElem?_eq_some

public def isStateInter (C : Certificate pt) (Sᵢ : ℕ) : Constraint (ℕ × ℕ) where

  prop := fun (S'ᵢ, S''ᵢ) ↦ C.states[Sᵢ]? = some (inter S'ᵢ S''ᵢ)

  verify' :=
    match C.states[Sᵢ]? with
    | some (inter S'ᵢ S''ᵢ) => pure ⟨(S'ᵢ, S''ᵢ), by simp⟩
    | some S => StateSetConstraint.throw_unexpected Sᵢ "an intersection of states" S
    | none => StateSetConstraint.throw_out_of_bounds Sᵢ

  elim_exists := by elim_exists_2 C.states[Sᵢ]?

  message := s!"Verifying that state set #{Sᵢ} is the intersection of two state sets"

@[simp]
public lemma isStateInter.prop_eq {C : Certificate pt} {Sᵢ S'ᵢ S''ᵢ} :
    (isStateInter C Sᵢ).prop (S'ᵢ, S''ᵢ) ↔
    Sᵢ < C.states.size ∧ C.states[Sᵢ]? = some (inter S'ᵢ S''ᵢ) := by
  simp only [isStateInter, eq_mpr_eq_cast, iff_and_self]
  exact Array.lt_of_getElem?_eq_some

public def isStateUnion (C : Certificate pt) (Sᵢ : ℕ) : Constraint (ℕ × ℕ) where

  prop := fun (S'ᵢ, S''ᵢ) ↦ C.states[Sᵢ]? = some (union S'ᵢ S''ᵢ)

  verify' :=
    match C.states[Sᵢ]? with
    | some (union S'ᵢ S''ᵢ) => pure ⟨(S'ᵢ, S''ᵢ), by simp⟩
    | some S => StateSetConstraint.throw_unexpected Sᵢ "a union of states" S
    | none => StateSetConstraint.throw_out_of_bounds Sᵢ

  elim_exists := by elim_exists_2 C.states[Sᵢ]?

  message := s!"Verifying that state set #{Sᵢ} is the union of two state sets"

@[simp]
public lemma isStateUnion.prop_eq {C : Certificate pt} {Sᵢ S'ᵢ S''ᵢ} :
    (isStateUnion C Sᵢ).prop (S'ᵢ, S''ᵢ) ↔
    Sᵢ < C.states.size ∧ C.states[Sᵢ]? = some (union S'ᵢ S''ᵢ) := by
  simp only [isStateUnion, eq_mpr_eq_cast, iff_and_self]
  exact Array.lt_of_getElem?_eq_some

public def isStateProgr (C : Certificate pt) (Sᵢ : ℕ) : Constraint (ℕ × ℕ) where

  prop := fun (S'ᵢ, Aᵢ) ↦ C.states[Sᵢ]? = some (progr S'ᵢ Aᵢ)

  verify' :=
    match C.states[Sᵢ]? with
    | some (progr S'ᵢ Aᵢ) => pure ⟨(S'ᵢ, Aᵢ), by simp⟩
    | some S => StateSetConstraint.throw_unexpected Sᵢ "a progression" S
    | none => StateSetConstraint.throw_out_of_bounds Sᵢ

  elim_exists := by elim_exists_2 C.states[Sᵢ]?

  message := s!"Verifying that state set #{Sᵢ} is a progression"

@[simp]
public lemma isStateProgr.prop_eq {C : Certificate pt} {Sᵢ S'ᵢ Aᵢ} :
  (isStateProgr C Sᵢ).prop (S'ᵢ, Aᵢ) ↔
  Sᵢ < C.states.size ∧ C.states[Sᵢ]? = some (progr S'ᵢ Aᵢ) :=
  by
    simp only [isStateProgr, eq_mpr_eq_cast, iff_and_self]
    exact Array.lt_of_getElem?_eq_some

public def isStateRegr (C : Certificate pt) (Sᵢ : ℕ) : Constraint (ℕ × ℕ) where

  prop := fun (S'ᵢ, Aᵢ) ↦ C.states[Sᵢ]? = some (regr S'ᵢ Aᵢ)

  verify' :=
    match C.states[Sᵢ]? with
    | some (regr S'ᵢ Aᵢ) => pure ⟨(S'ᵢ, Aᵢ), by simp⟩
    | some S => StateSetConstraint.throw_unexpected Sᵢ "a regression" S
    | none => StateSetConstraint.throw_out_of_bounds Sᵢ

  elim_exists := by elim_exists_2 C.states[Sᵢ]?

  message := s!"Verifying that state set #{Sᵢ} is a regression"

@[simp]
public lemma isStateRegr.prop_eq {C : Certificate pt} {Sᵢ S'ᵢ Aᵢ} :
    (isStateRegr C Sᵢ).prop (S'ᵢ, Aᵢ) ↔
    Sᵢ < C.states.size ∧ C.states[Sᵢ]? = some (regr S'ᵢ Aᵢ) := by
  simp only [isStateRegr, eq_mpr_eq_cast, iff_and_self]
  exact Array.lt_of_getElem?_eq_some

public abbrev isUnion (C : Certificate pt) : SetType → ℕ → Constraint (ℕ × ℕ)
  | SetType.Actions => isActionUnion C
  | SetType.States => isStateUnion C

open Knowledge

public def isDeadKnowledge (C : Certificate pt) (Kᵢ : ℕ) : Constraint ℕ where

  prop := fun Sᵢ ↦ ∃ K, C.knowledge[Kᵢ]? = dead Sᵢ K

  verify' :=
    match C.knowledge[Kᵢ]? with
    | some (dead Sᵢ K) => return ⟨Sᵢ, by simp⟩
    | some K => KnowledgeConstraint.throw_unexpected Kᵢ "dead knowledge" K
    | none => KnowledgeConstraint.throw_out_of_bounds Kᵢ

  elim_exists h := by
    cases heq : C.knowledge[Kᵢ]? with
    | some K =>
      cases K
      all_goals simp_all only [Option.some.injEq, reduceCtorEq, exists_false]
      rename_i Sᵢ K
      exact ⟨Sᵢ, by simp_all⟩
    | none => simp_all

  message := s!"Verifying that knowledge #{Kᵢ} is dead-knowledge"

@[simp]
public lemma isDeadKnowledge.prop_eq {C : Certificate pt} {Kᵢ Sᵢ} :
  (isDeadKnowledge C Kᵢ).prop Sᵢ = ∃ K, C.knowledge[Kᵢ]? = dead Sᵢ K := (rfl)

public def isActionSubsetKnowledge (C : Certificate pt) (Kᵢ : ℕ) : Constraint (ℕ × ℕ) where

  prop := fun (Aᵢ, A'ᵢ) ↦ ∃ K, C.knowledge[Kᵢ]? = actionSubset Aᵢ A'ᵢ K

  verify' :=
    match C.knowledge[Kᵢ]? with
    | some (actionSubset Aᵢ A'ᵢ K) => return ⟨(Aᵢ, A'ᵢ), by simp⟩
    | some K => KnowledgeConstraint.throw_unexpected Kᵢ "action subset knowledge" K
    | none => KnowledgeConstraint.throw_out_of_bounds Kᵢ

  elim_exists := by
    simp_all only [Prod.exists, forall_exists_index, Prod.forall]
    cases heq : C.knowledge[Kᵢ]? with
    | some K =>
      cases K
      all_goals
        intro h
        simp_all only [Option.some.injEq, reduceCtorEq, exists_false]
      rename_i Sᵢ S'ᵢ K
      exact ⟨(Sᵢ, S'ᵢ), by simp_all⟩
    | none => intro h; simp_all

  message := s!"Verifying that knowledge #{Kᵢ} is action subset knowledge"

@[simp]
public lemma isActionSubsetKnowledge.prop_eq {C : Certificate pt} {Kᵢ Aᵢ A'ᵢ} :
    (isActionSubsetKnowledge C Kᵢ).prop (Aᵢ, A'ᵢ) =
      ∃ K, C.knowledge[Kᵢ]? = actionSubset Aᵢ A'ᵢ K := (rfl)

public def isStateSubsetKnowledge (C : Certificate pt) (Kᵢ : ℕ) : Constraint (ℕ × ℕ) where

  prop := fun (Sᵢ, S'ᵢ) ↦ ∃ K, C.knowledge[Kᵢ]? = stateSubset Sᵢ S'ᵢ K

  verify' :=
    match C.knowledge[Kᵢ]? with
    | some (stateSubset Sᵢ S'ᵢ K) => return ⟨(Sᵢ, S'ᵢ), by simp⟩
    | some K => KnowledgeConstraint.throw_unexpected Kᵢ "state subset knowledge" K
    | none => KnowledgeConstraint.throw_out_of_bounds Kᵢ

  elim_exists := by
    simp_all only [Prod.exists, forall_exists_index, Prod.forall]
    cases heq : C.knowledge[Kᵢ]? with
    | some K =>
      cases K
      all_goals
        intro h
        simp_all only [Option.some.injEq, reduceCtorEq, exists_false]
      rename_i Sᵢ S'ᵢ K
      exact ⟨(Sᵢ, S'ᵢ), by simp_all⟩
    | none => intro h; simp_all

  message := s!"Verifying that knowledge #{Kᵢ} is state subset knowledge"

@[simp]
public lemma isStateSubsetKnowledge.prop_eq {C : Certificate pt} {Kᵢ Sᵢ S'ᵢ} :
    (isStateSubsetKnowledge C Kᵢ).prop (Sᵢ, S'ᵢ) =
      ∃ K, C.knowledge[Kᵢ]? = stateSubset Sᵢ S'ᵢ K := (rfl)

public abbrev isSubsetKnowledge (C : Certificate pt) : SetType → ℕ → Constraint (ℕ × ℕ)
  | SetType.Actions => isActionSubsetKnowledge C
  | SetType.States => isStateSubsetKnowledge C

end Constraint
