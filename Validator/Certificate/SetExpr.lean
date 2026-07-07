module

public import Validator.Error
public import Validator.Certificate.Certificate

open STRIPS

namespace Validator

variable {n : ℕ} {pt : PlanningTask n}

public inductive SetType
  | Actions
  | States

public inductive ConstraintType
  | ActionSetConstraint
  | StateSetConstraint
  | KnowledgeConstraint

public def SetType.toConstraintType : SetType → ConstraintType
  | Actions => .ActionSetConstraint
  | States => .StateSetConstraint

instance : ToString ConstraintType where
  toString
  | .ActionSetConstraint => "action set"
  | .StateSetConstraint => "state set"
  | .KnowledgeConstraint => "knowledge"

public def ConstraintType.throw_out_of_bounds {α : outParam Type} {p}
    (T : ConstraintType) (Eᵢ : ℕ) : Result α p :=
  throwInvalid s!"There is no {T} with identifier #{Eᵢ}."

public def ConstraintType.throw_not_eq {α : outParam Type} {p}
    (T : ConstraintType) (Eᵢ : ℕ) (E'ᵢ : ℕ) : Result α p :=
  throwInvalid s!"Expected {T} with identifier #{Eᵢ}, but found #{E'ᵢ}."

public def ConstraintType.throw_unexpected {α : outParam Type} {β γ} [ToString β] [ToString γ] {p}
    (T : ConstraintType) (Eᵢ : ℕ) (expected : β) (found : γ) : Result α p :=
  throwInvalid s!"The {T} with identifier #{Eᵢ} is expect to be {expected}, but it is {found}."

def verify_bounds (T : ConstraintType) (limit Eᵢ : ℕ) : Result' (Eᵢ < limit)  :=
  if h : Eᵢ < limit
  then return ⟨(), h⟩
  else T.throw_out_of_bounds Eᵢ

def verify_action_bounds := verify_bounds .ActionSetConstraint

def verify_state_bounds := verify_bounds .StateSetConstraint

def verify_and {p1 p2} (res1 : Result' p1) (res2 : Result' p2) : Result' (p1 ∧ p2) := do
  let ⟨(), h1⟩ ← res1
  let ⟨(), h2⟩ ← res2
  return ⟨(), And.intro h1 h2⟩

def verifyActionsEnum (pt : PlanningTask n) (as : List ℕ) :
    Result' (∀ a ∈ as, a < pt.actions'.length) :=
  if h : ∀ a ∈ as, a < pt.actions'.length then
    return ⟨(), h⟩
  else
    throwInvalid s!"Not all given actions ids exist in the planning task.\
    The following action ids are out of bound:\n {as.filter (· < pt.actions'.length)}"

namespace Certificate

@[expose]
public def validActionSetExpr (C : Certificate pt) (Aᵢ : Fin C.actions.size) : Prop :=
  match C.actions[Aᵢ] with
  | ActionSetExpr.enum as => ∀ a ∈ as, a < pt.actions'.length
  | ActionSetExpr.union A'ᵢ A''ᵢ => A'ᵢ < Aᵢ ∧ A''ᵢ < Aᵢ
  | ActionSetExpr.all => True

@[expose]
public def validStateSetExpr (C : Certificate pt) (Sᵢ : Fin C.states.size) : Prop :=
  match C.states[Sᵢ] with
  | StateSetExpr.empty => True
  | StateSetExpr.init => True
  | StateSetExpr.goal => True
  | StateSetExpr.bdd φ => True
  | StateSetExpr.horn φ => True
  | StateSetExpr.mods φ => True
  | StateSetExpr.neg S'ᵢ => S'ᵢ < Sᵢ
  | StateSetExpr.inter S'ᵢ S''ᵢ => S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ
  | StateSetExpr.union S'ᵢ S''ᵢ => S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ
  | StateSetExpr.progr S'ᵢ Aᵢ => S'ᵢ < Sᵢ ∧ Aᵢ < C.actions.size
  | StateSetExpr.regr S'ᵢ Aᵢ => S'ᵢ < Sᵢ ∧ Aᵢ < C.actions.size

public def verifyActionSetExpr (C : Certificate pt) (Aᵢ : Fin C.actions.size) :
    Result' (C.validActionSetExpr Aᵢ) := by
  unfold validActionSetExpr
  cases C.actions[Aᵢ] with
  | enum as => exact verifyActionsEnum pt as
  | union A'ᵢ A''ᵢ =>
      exact verify_and (verify_action_bounds Aᵢ A'ᵢ) (verify_action_bounds Aᵢ A''ᵢ)
  | all => exact pure ⟨(), True.intro⟩

public def verifyStateSetExpr (C : Certificate pt) (Sᵢ : Fin C.states.size) :
    Result' (C.validStateSetExpr Sᵢ) := by
  unfold validStateSetExpr
  cases C.states[Sᵢ] with
  | empty => exact pure ⟨(), True.intro⟩
  | init => exact pure ⟨(), True.intro⟩
  | goal => exact pure ⟨(), True.intro⟩
  | bdd => exact pure ⟨(), True.intro⟩
  | horn => exact pure ⟨(), True.intro⟩
  | mods => exact pure ⟨(), True.intro⟩
  | neg S'ᵢ => exact verify_state_bounds Sᵢ S'ᵢ
  | inter S'ᵢ S''ᵢ => exact verify_and (verify_state_bounds Sᵢ S'ᵢ) (verify_state_bounds Sᵢ S''ᵢ)
  | union S'ᵢ S''ᵢ => exact verify_and (verify_state_bounds Sᵢ S'ᵢ) (verify_state_bounds Sᵢ S''ᵢ)
  | progr S'ᵢ Aᵢ =>
    exact verify_and (verify_state_bounds Sᵢ S'ᵢ) (verify_action_bounds C.actions.size Aᵢ)
  | regr S'ᵢ Aᵢ =>
    exact verify_and (verify_state_bounds Sᵢ S'ᵢ) (verify_action_bounds C.actions.size Aᵢ)

/-structure SemiValidCertificate (pt : PlanningTask n) extends Certificate pt where
  validActions : ∀ Aᵢ, (⟨actions, states, knowledge⟩ : Certificate pt).validActionSetExpr  Aᵢ
  validStates : ∀ Sᵢ, (⟨actions, states, knowledge⟩ : Certificate pt).validStateSetExpr  Sᵢ-/

public structure validSets (C : Certificate pt) : Prop where
  validActions : ∀ Aᵢ, C.validActionSetExpr Aᵢ
  validStates : ∀ Sᵢ, C.validStateSetExpr Sᵢ

namespace validSets

public abbrev ActionIds (pt : PlanningTask n) := List (Fin pt.actions'.length)

public def ActionIds.toActions (A : ActionIds pt) : Actions n :=
  (A.map (pt.actions'[·])).toFinset

@[simp]
public lemma ActionIds.mem_toActions (A : ActionIds pt) {a} :
    a ∈ A.toActions ↔ ∃ i ∈ A, pt.actions'[i] = a := by
  simp only [toActions, List.coe_toFinset, List.mem_map, Set.mem_setOf_eq]

public def getActionIds {C : Certificate pt} (hC : C.validSets)
    (Aᵢ : Fin C.actions.size) : ActionIds pt :=
  match heq : C.actions[Aᵢ] with
  | ActionSetExpr.enum as => by
    have h' := hC.validActions Aᵢ
    simp only [validActionSetExpr, heq] at h'
    exact (as.attach.map (fun ⟨a, ha⟩ ↦⟨a, h' a ha⟩))
  | ActionSetExpr.union A'ᵢ A''ᵢ =>
    have h' := hC.validActions Aᵢ
    have : A'ᵢ < Aᵢ ∧ A''ᵢ < Aᵢ := by
      simp_all [Certificate.validActionSetExpr]
    hC.getActionIds ⟨A'ᵢ, by omega⟩ ∪ hC.getActionIds ⟨A''ᵢ, by omega⟩
  | ActionSetExpr.all => List.finRange pt.actions'.length

public def getActions {C : Certificate pt} (hC : C.validSets) (Aᵢ : Fin C.actions.size) :
    Actions n :=
  (getActionIds hC Aᵢ).toActions

public lemma getActions_eq {C : Certificate pt} {hC : C.validSets} {Aᵢ} :
    getActions hC Aᵢ = (getActionIds hC Aᵢ).toActions := (rfl)

/-def getActions (C : Certificate pt) (h : C.validSets) (Aᵢ : Fin C.actions.size) : Actions n :=
  match heq : C.actions[Aᵢ] with
  | ActionSetExpr.enum as => by
    have h' := h.actions Aᵢ
    unfold constraintActionSetExpr at h'
    rw [heq] at h'
    simp [Constraint.valid] at h'
    exact (as.attach.map (fun ⟨a, ha⟩ ↦ pt.actions'[a]'(h' a ha))).toFinset
  | ActionSetExpr.union A'ᵢ A''ᵢ =>
    have h' := h.actions Aᵢ
    have : A'ᵢ < Aᵢ ∧ A''ᵢ < Aᵢ := by
      unfold constraintActionSetExpr at h'
      rw[heq] at h'
      simp_all
    C.getActions h ⟨A'ᵢ, by omega⟩ ∪ C.getActions h ⟨A''ᵢ, by omega⟩
  | ActionSetExpr.all => pt.actions-/

public lemma getActionsAll {C : Certificate pt} {hC : C.validSets} Aᵢ
    (h : C.actions[Aᵢ]? = ActionSetExpr.all) : hC.getActions Aᵢ = pt.actions := by
  unfold getActions getActionIds
  split
  all_goals simp_all [ActionIds.toActions, PlanningTask.mem_actions']

public lemma getActionsUnion {C : Certificate pt} {hC : C.validSets}
    (Aᵢ A'ᵢ A''ᵢ : Fin C.actions.size) (h : C.actions[Aᵢ]? = ActionSetExpr.union A'ᵢ A''ᵢ) :
    hC.getActions Aᵢ = hC.getActions A'ᵢ ∪ hC.getActions A''ᵢ := by
  simp only [getActions, ActionIds.toActions, List.map_toFinset, Finset.coe_image,
    List.coe_toFinset]
  rw [getActionIds]
  split
  all_goals simp_all [← Set.image_union]
  grind

public def getStates {C : Certificate pt} (hC : C.validSets) (Sᵢ : Fin C.states.size) : States n :=
  have h := hC.validStates Sᵢ
  match heq : C.states[Sᵢ] with
  | StateSetExpr.empty => ∅
  | StateSetExpr.init => {pt.init}
  | StateSetExpr.goal => pt.goalStates
  | StateSetExpr.bdd φ => φ.val.toStates
  | StateSetExpr.horn φ => φ.val.toStates
  | StateSetExpr.mods φ => φ.val.toStates
  | StateSetExpr.neg S'ᵢ =>
    have : S'ᵢ < Sᵢ := by
      simp_all [Certificate.validStateSetExpr]
    (hC.getStates ⟨S'ᵢ, by omega⟩)ᶜ
  | StateSetExpr.inter S'ᵢ S''ᵢ =>
    have : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      simp_all [Certificate.validStateSetExpr]
    hC.getStates ⟨S'ᵢ, by omega⟩ ∩ hC.getStates ⟨S''ᵢ, by omega⟩
  | StateSetExpr.union S'ᵢ S''ᵢ =>
    have : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      simp_all [Certificate.validStateSetExpr]
    hC.getStates ⟨S'ᵢ, by omega⟩ ∪ hC.getStates ⟨S''ᵢ, by omega⟩
  | StateSetExpr.progr S'ᵢ Aᵢ =>
    have h' : S'ᵢ < Sᵢ ∧ Aᵢ < C.actions.size := by
      simp_all [Certificate.validStateSetExpr]
    progression (hC.getStates ⟨S'ᵢ, by omega⟩) (hC.getActions ⟨Aᵢ, h'.2⟩)
  | StateSetExpr.regr S'ᵢ Aᵢ =>
    have h' : S'ᵢ < Sᵢ ∧ Aᵢ < C.actions.size := by
      simp_all [Certificate.validStateSetExpr]
    regression (hC.getStates ⟨S'ᵢ, by omega⟩) (hC.getActions ⟨Aᵢ, h'.2⟩)

public lemma getStatesEmpty {C : Certificate pt} (hC : C.validSets) Sᵢ
    (h : C.states[Sᵢ]? = some StateSetExpr.empty) : hC.getStates Sᵢ = ∅ := by
  unfold getStates
  split
  all_goals simp_all

public lemma getStatesInit {C : Certificate pt} (hC : C.validSets) Sᵢ
    (h : C.states[Sᵢ]? = some StateSetExpr.init) : hC.getStates Sᵢ = {pt.init} := by
  unfold getStates
  split
  all_goals simp_all

public lemma getStatesGoal {C : Certificate pt} (hC : C.validSets) Sᵢ
    (h : C.states[Sᵢ]? = some StateSetExpr.goal) : hC.getStates Sᵢ = pt.goalStates := by
  unfold getStates
  split
  all_goals simp_all

public lemma getStatesBdd {C : Certificate pt} (hC : C.validSets) Sᵢ {φ}
    (h : C.states[Sᵢ]? = some (StateSetExpr.bdd φ)) : hC.getStates Sᵢ = φ.val.toStates := by
  unfold getStates
  split
  all_goals simp_all

public lemma getStatesHorn {C : Certificate pt} (hC : C.validSets) Sᵢ {φ}
    (h : C.states[Sᵢ]? = some (StateSetExpr.horn φ)) : hC.getStates Sᵢ = φ.val.toStates := by
  unfold getStates
  split
  all_goals simp_all

public lemma getStatesMods {C : Certificate pt} (hC : C.validSets) Sᵢ {φ}
    (h : C.states[Sᵢ]? = some (StateSetExpr.mods φ)) : hC.getStates Sᵢ = φ.val.toStates := by
  unfold getStates
  split
  all_goals simp_all

public lemma getStatesNeg {C : Certificate pt} (hC : C.validSets) (Sᵢ S'ᵢ : Fin C.states.size)
    (h : C.states[Sᵢ]? = some (StateSetExpr.neg S'ᵢ)) : hC.getStates Sᵢ = (hC.getStates S'ᵢ)ᶜ := by
  rw[getStates]
  split
  all_goals simp_all

public lemma getStatesInter {C : Certificate pt} (hC : C.validSets)
    (Sᵢ S'ᵢ S''ᵢ : Fin C.states.size) (h : C.states[Sᵢ]? = some (StateSetExpr.inter S'ᵢ S''ᵢ)) :
    hC.getStates Sᵢ = hC.getStates S'ᵢ ∩ hC.getStates S''ᵢ := by
  rw [getStates]
  split
  all_goals simp_all

public lemma getStatesUnion {C : Certificate pt} (hC : C.validSets)
    (Sᵢ S'ᵢ S''ᵢ : Fin C.states.size) (h : C.states[Sᵢ]? = some (StateSetExpr.union S'ᵢ S''ᵢ)) :
    hC.getStates Sᵢ = hC.getStates S'ᵢ ∪ hC.getStates S''ᵢ := by
  rw [getStates]
  split
  all_goals simp_all

public lemma getStatesProg {C : Certificate pt} (hC : C.validSets) (Sᵢ S'ᵢ : Fin C.states.size)
    (Aᵢ : Fin C.actions.size) (h : C.states[Sᵢ]? = some (StateSetExpr.progr S'ᵢ Aᵢ)) :
    hC.getStates Sᵢ = progression (hC.getStates S'ᵢ) (hC.getActions Aᵢ) := by
  rw [getStates]
  split
  all_goals simp_all

public lemma getStatesRegr {C : Certificate pt} (hC : C.validSets) (Sᵢ S'ᵢ : Fin C.states.size)
    (Aᵢ : Fin C.actions.size) (h : C.states[Sᵢ]? = some (StateSetExpr.regr S'ᵢ Aᵢ)) :
    hC.getStates Sᵢ = regression (hC.getStates S'ᵢ) (hC.getActions Aᵢ) := by
  rw [getStates]
  split
  all_goals simp_all

end Validator.Certificate.validSets
