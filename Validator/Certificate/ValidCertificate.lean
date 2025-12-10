import Validator.Certificate.BasicRules

namespace Validator.Certificate

variable {n : ℕ} {pt : STRIPS n} (C : Certificate pt)
open Validator Constraint ConstraintType Knowledge
open DeadKnowledge ActionSubsetKnowledge StateSubsetKnowledge UnsolvableKnowledge

def constraintUD (Kᵢ S1ᵢ K1ᵢ K2ᵢ : ℕ) :=
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  (isStateUnion C S1ᵢ).seq fun (Sᵢ, S'ᵢ) ↦
    (isDeadKnowledge C K1ᵢ).eqState Sᵢ ∧ᶜ
    (isDeadKnowledge C K2ᵢ).eqState S'ᵢ

/-
TODO : the stateBounds here and in other constraints can be removed, since they are
already checked in isStateSubsetKnowledge C, but that would make valid.deadKnowledgeBound etc
more complicated. Check if it is worth removing them here
-/
def constraintSD (Kᵢ Sᵢ K1ᵢ K2ᵢ : ℕ) :=
  stateBounds' C Sᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  (isDeadKnowledge C K1ᵢ).seq fun S'ᵢ ↦
    (isStateSubsetKnowledge C K2ᵢ).eqStates Sᵢ S'ᵢ

def constraintPG (Kᵢ Sᵢ K1ᵢ K2ᵢ K3ᵢ : ℕ) :=
  stateBounds' C Sᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K3ᵢ ∧ᶜ
  (isStateSubsetKnowledge C K1ᵢ).seq fun (S1ᵢ, S2ᵢ) ↦
    ((((isStateProgr C S1ᵢ).leftEqState Sᵢ).seq fun Aᵢ ↦
      isActionAll C Aᵢ) ∧ᶜ
    ((isStateUnion C S2ᵢ).leftEqState Sᵢ).seq fun S'ᵢ ↦
      (isDeadKnowledge C K2ᵢ).eqState S'ᵢ) ∧ᶜ
  (isDeadKnowledge C K3ᵢ).seq fun S3ᵢ ↦
    ((isStateInter C S3ᵢ).leftEqState Sᵢ).seq fun SGᵢ ↦
      isStateGoal C SGᵢ

def constraintPI (Kᵢ S1ᵢ K1ᵢ K2ᵢ K3ᵢ : ℕ) :=
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K3ᵢ ∧ᶜ
  (isStateNeg C S1ᵢ).seq fun Sᵢ ↦
    ((isStateSubsetKnowledge C K1ᵢ).seq fun (S2ᵢ, S3ᵢ) ↦
      (((isStateProgr C S2ᵢ).leftEqState Sᵢ).seq fun Aᵢ ↦
        isActionAll C Aᵢ) ∧ᶜ
      ((isStateUnion C S3ᵢ).leftEqState Sᵢ).seq fun S'ᵢ ↦
        (isDeadKnowledge C K2ᵢ).eqState S'ᵢ) ∧ᶜ
    ((isStateSubsetKnowledge C K3ᵢ).rightEqState Sᵢ).seq fun SIᵢ ↦
      isStateInit C SIᵢ

def constraintRG (Kᵢ S1ᵢ K1ᵢ K2ᵢ K3ᵢ : ℕ) :=
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K3ᵢ ∧ᶜ
  ((isStateNeg C S1ᵢ).seq fun Sᵢ ↦
    (isStateSubsetKnowledge C K1ᵢ).seq fun (S2ᵢ, S3ᵢ) ↦
      (((isStateRegr C S2ᵢ).leftEqState Sᵢ).seq fun Aᵢ ↦
        isActionAll C Aᵢ) ∧ᶜ
      ((isStateUnion C S3ᵢ).leftEqState Sᵢ).seq fun S'ᵢ ↦
        (isDeadKnowledge C K2ᵢ).eqState S'ᵢ) ∧ᶜ
  (isDeadKnowledge C K3ᵢ).seq fun S4ᵢ ↦
    ((isStateInter C S4ᵢ).leftEqState S1ᵢ).seq fun SGᵢ ↦
      isStateGoal C SGᵢ

def constraintRI (Kᵢ Sᵢ K1ᵢ K2ᵢ K3ᵢ : ℕ) :=
  stateBounds' C Sᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K3ᵢ ∧ᶜ
  (isStateSubsetKnowledge C K1ᵢ).seq fun (S1ᵢ, S2ᵢ) ↦
    (((isStateRegr C S1ᵢ).leftEqState Sᵢ).seq fun Aᵢ ↦
      isActionAll C Aᵢ) ∧ᶜ
    (((isStateUnion C S2ᵢ).leftEqState Sᵢ).seq fun S'ᵢ ↦
      (isDeadKnowledge C K2ᵢ).eqState S'ᵢ) ∧ᶜ
    (isStateSubsetKnowledge C K3ᵢ).seq fun (SIᵢ, S3ᵢ) ↦
      isStateInit C SIᵢ ∧ᶜ
      (isStateNeg C S3ᵢ).eqState Sᵢ

def constraintUR (T : SetType) (Eᵢ E1ᵢ : ℕ) :=
  setBounds' C T Eᵢ ∧ᶜ
  (isUnion C T E1ᵢ).leftEq T Eᵢ

def constraintUL (T : SetType) (Eᵢ E1ᵢ : ℕ) :=
  setBounds' C T Eᵢ ∧ᶜ
  (isUnion C T E1ᵢ).rightEq T Eᵢ

def constraintIR (S1ᵢ Sᵢ : ℕ) :=
  stateBounds' C Sᵢ ∧ᶜ
  (isStateInter C S1ᵢ).leftEqState Sᵢ

def constraintIL (S1ᵢ Sᵢ : ℕ) :=
  stateBounds' C Sᵢ ∧ᶜ
  (isStateInter C S1ᵢ).rightEqState Sᵢ

def constraintDI (S1ᵢ S2ᵢ : ℕ) :=
  (isStateInter C S1ᵢ).seq fun (S3ᵢ, S''ᵢ) ↦
    (isStateUnion C S3ᵢ).seq fun (Sᵢ, S'ᵢ) ↦
      (isStateUnion C S2ᵢ).seq fun (S4ᵢ, S5ᵢ) ↦
        (isStateInter C S4ᵢ).eqStates Sᵢ S''ᵢ ∧ᶜ
        (isStateInter C S5ᵢ).eqStates S'ᵢ S''ᵢ

def constraintSU (T : SetType) (Kᵢ E1ᵢ E''ᵢ K1ᵢ K2ᵢ : ℕ) :=
  setBounds' C T E''ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  (isUnion C T E1ᵢ).seq fun (Eᵢ, E'ᵢ) ↦
    (isSubsetKnowledge C T K1ᵢ).bothEq T T Eᵢ E''ᵢ ∧ᶜ
    (isSubsetKnowledge C T K2ᵢ).bothEq T T E'ᵢ E''ᵢ

def constraintSI (Kᵢ Sᵢ S1ᵢ K1ᵢ K2ᵢ : ℕ) :=
  stateBounds' C Sᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  (isStateInter C S1ᵢ).seq fun (S'ᵢ, S''ᵢ) ↦
    (isStateSubsetKnowledge C K1ᵢ).eqStates Sᵢ S'ᵢ ∧ᶜ
    (isStateSubsetKnowledge C K2ᵢ).eqStates Sᵢ S''ᵢ

def constraintST (T : SetType) (Kᵢ Eᵢ E''ᵢ K1ᵢ K2ᵢ : ℕ) :=
  setBounds' C T Eᵢ ∧ᶜ
  setBounds' C T E''ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  ((isSubsetKnowledge C T K1ᵢ).leftEq T Eᵢ).seq fun E'ᵢ ↦
    (isSubsetKnowledge C T K2ᵢ).bothEq T T E'ᵢ E''ᵢ

def constraintAT (Kᵢ S1ᵢ S'ᵢ K1ᵢ K2ᵢ : ℕ) :=
  stateBounds' C S'ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  (isStateProgr C S1ᵢ).seq fun (Sᵢ, A'ᵢ) ↦
    ((isStateSubsetKnowledge C K1ᵢ).rightEqState S'ᵢ).seq fun S2ᵢ ↦
      ((isStateProgr C S2ᵢ).leftEqState Sᵢ).seq fun Aᵢ ↦
        (isActionSubsetKnowledge C K2ᵢ).bothEq SetType.Actions SetType.Actions A'ᵢ Aᵢ

def constraintAU (Kᵢ S1ᵢ S'ᵢ K1ᵢ K2ᵢ : ℕ) :=
  stateBounds' C S'ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  (isStateProgr C S1ᵢ).seq fun (Sᵢ, A1ᵢ) ↦
    (isActionUnion C A1ᵢ).seq fun (Aᵢ, A'ᵢ) ↦
      (((isStateSubsetKnowledge C K1ᵢ).rightEqState S'ᵢ).seq fun S2ᵢ ↦
        (isStateProgr C S2ᵢ).eqStateAction Sᵢ Aᵢ) ∧ᶜ
      (((isStateSubsetKnowledge C K2ᵢ).rightEqState S'ᵢ).seq fun S3ᵢ ↦
        (isStateProgr C S3ᵢ).eqStateAction Sᵢ A'ᵢ)

def constraintPT (Kᵢ S1ᵢ S''ᵢ K1ᵢ K2ᵢ : ℕ) :=
  stateBounds' C S''ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  (isStateProgr C S1ᵢ).seq fun (S'ᵢ, Aᵢ) ↦
    ((isStateSubsetKnowledge C K1ᵢ).rightEqState S''ᵢ).seq fun S2ᵢ ↦
      ((isStateProgr C S2ᵢ).rightEqAction Aᵢ).seq fun Sᵢ ↦
        (isStateSubsetKnowledge C K2ᵢ).eqStates S'ᵢ Sᵢ

def constraintPU (Kᵢ S1ᵢ S''ᵢ K1ᵢ K2ᵢ : ℕ) :=
  stateBounds' C S''ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K2ᵢ ∧ᶜ
  (isStateProgr C S1ᵢ).seq fun (S2ᵢ, Aᵢ) ↦
    (isStateUnion C S2ᵢ).seq fun (Sᵢ, S'ᵢ) ↦
      (((isStateSubsetKnowledge C K1ᵢ).rightEqState S''ᵢ).seq fun S3ᵢ ↦
        (isStateProgr C S3ᵢ).eqStateAction Sᵢ Aᵢ) ∧ᶜ
      (((isStateSubsetKnowledge C K2ᵢ).rightEqState S''ᵢ).seq fun S4ᵢ ↦
        (isStateProgr C S4ᵢ).eqStateAction S'ᵢ Aᵢ)

def constraintPR (Kᵢ S1ᵢ S2ᵢ K1ᵢ : ℕ) :=
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  (isStateRegr C S1ᵢ).seq fun (S3ᵢ, Aᵢ) ↦
    (isStateNeg C S3ᵢ).seq fun S'ᵢ ↦
      (isStateNeg C S2ᵢ).seq fun Sᵢ ↦
        (((isStateSubsetKnowledge C K1ᵢ).rightEqState S'ᵢ).seq fun S4ᵢ ↦
          (isStateProgr C S4ᵢ).eqStateAction Sᵢ Aᵢ)

def constraintRP (Kᵢ S1ᵢ S'ᵢ K1ᵢ : ℕ) :=
  stateBounds' C S'ᵢ ∧ᶜ
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  (isStateProgr C S1ᵢ).seq fun (Sᵢ, Aᵢ) ↦
    (isStateSubsetKnowledge C K1ᵢ).seq fun (S2ᵢ, S3ᵢ) ↦
      (((isStateRegr C S2ᵢ).rightEqAction Aᵢ).seq fun S4ᵢ ↦
        (isStateNeg C S4ᵢ).eqState S'ᵢ) ∧ᶜ
      (isStateNeg C S3ᵢ).eqState Sᵢ

def constraintCI (Kᵢ K1ᵢ : ℕ) :=
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  (isDeadKnowledge C K1ᵢ).seq fun SIᵢ ↦
    isStateInit C SIᵢ

def constraintCG (Kᵢ K1ᵢ : ℕ) :=
  knowledgeBounds Kᵢ K1ᵢ ∧ᶜ
  (isDeadKnowledge C K1ᵢ).seq fun SGᵢ ↦
    isStateGoal C SGᵢ

def constraintKnowledge {C : Certificate pt} (hC : C.validSets) (Kᵢ : Fin C.knowledge.size) :
  Σ α, Constraint α :=
  match C.knowledge[Kᵢ] with
  | dead Sᵢ K =>
    match K with
    | ED Sᵢ => ⟨_, isStateEmpty C Sᵢ⟩
    | UD Sᵢ K1ᵢ K2ᵢ => ⟨_, constraintUD C Kᵢ Sᵢ K1ᵢ K2ᵢ⟩
    | SD Sᵢ K1ᵢ K2ᵢ => ⟨_, constraintSD C Kᵢ Sᵢ K1ᵢ K2ᵢ⟩
    | PG Sᵢ K1ᵢ K2ᵢ K3ᵢ => ⟨_, constraintPG C Kᵢ Sᵢ K1ᵢ K2ᵢ K3ᵢ⟩
    | PI Sᵢ K1ᵢ K2ᵢ K3ᵢ => ⟨_, constraintPI C Kᵢ Sᵢ K1ᵢ K2ᵢ K3ᵢ⟩
    | RG Sᵢ K1ᵢ K2ᵢ K3ᵢ => ⟨_, constraintRG C Kᵢ Sᵢ K1ᵢ K2ᵢ K3ᵢ⟩
    | RI Sᵢ K1ᵢ K2ᵢ K3ᵢ => ⟨_, constraintRI C Kᵢ Sᵢ K1ᵢ K2ᵢ K3ᵢ⟩
  | actionSubset Aᵢ A'ᵢ K =>
    match K with
    | B5 Aᵢ A'ᵢ => ⟨_, constraintB5 hC Aᵢ A'ᵢ⟩
    | URA Aᵢ A'ᵢ => ⟨_, constraintUR C SetType.Actions Aᵢ A'ᵢ⟩
    | ULA Aᵢ A'ᵢ => ⟨_, constraintUL C SetType.Actions Aᵢ A'ᵢ⟩
    | SUA Aᵢ A'ᵢ K1ᵢ K2ᵢ => ⟨_, constraintSU C SetType.Actions Kᵢ Aᵢ A'ᵢ K1ᵢ K2ᵢ⟩
    | STA Aᵢ A'ᵢ K1ᵢ K2ᵢ => ⟨_, constraintST C SetType.Actions Kᵢ Aᵢ A'ᵢ K1ᵢ K2ᵢ⟩
  | stateSubset Sᵢ S'ᵢ K =>
    match K with
    | B1 Sᵢ S'ᵢ => ⟨_, constraintB1 hC Sᵢ S'ᵢ⟩
    | B2 Sᵢ S'ᵢ => ⟨_, constraintB2 hC Sᵢ S'ᵢ⟩
    | B3 Sᵢ S'ᵢ => ⟨_, constraintB3 hC Sᵢ S'ᵢ⟩
    | B4 Sᵢ S'ᵢ => ⟨_, constraintB4 hC Sᵢ S'ᵢ⟩
    | URS Sᵢ S'ᵢ => ⟨_, constraintUR C SetType.States Sᵢ S'ᵢ⟩
    | ULS Sᵢ S'ᵢ => ⟨_, constraintUL C SetType.States Sᵢ S'ᵢ⟩
    | IRS Sᵢ S'ᵢ => ⟨_, constraintIR C Sᵢ S'ᵢ⟩
    | ILS Sᵢ S'ᵢ => ⟨_, constraintIL C Sᵢ S'ᵢ⟩
    | DIS Sᵢ S'ᵢ => ⟨_, constraintDI C Sᵢ S'ᵢ⟩
    | SUS Sᵢ S'ᵢ K1ᵢ K2ᵢ => ⟨_, constraintSU C SetType.States Kᵢ Sᵢ S'ᵢ K1ᵢ K2ᵢ⟩
    | SIS Sᵢ S'ᵢ K1ᵢ K2ᵢ => ⟨_, constraintSI C Kᵢ Sᵢ S'ᵢ K1ᵢ K2ᵢ⟩
    | STS Sᵢ S'ᵢ K1ᵢ K2ᵢ => ⟨_, constraintST C SetType.States Kᵢ Sᵢ S'ᵢ K1ᵢ K2ᵢ⟩
    | AT Sᵢ S'ᵢ K1ᵢ K2ᵢ => ⟨_, constraintAT C Kᵢ Sᵢ S'ᵢ K1ᵢ K2ᵢ⟩
    | AU Sᵢ S'ᵢ K1ᵢ K2ᵢ => ⟨_, constraintAU C Kᵢ Sᵢ S'ᵢ K1ᵢ K2ᵢ⟩
    | PT Sᵢ S'ᵢ K1ᵢ K2ᵢ => ⟨_, constraintPT C Kᵢ Sᵢ S'ᵢ K1ᵢ K2ᵢ⟩
    | PU Sᵢ S'ᵢ K1ᵢ K2ᵢ => ⟨_, constraintPU C Kᵢ Sᵢ S'ᵢ K1ᵢ K2ᵢ⟩
    | PR Sᵢ S'ᵢ K1ᵢ => ⟨_, constraintPR C Kᵢ Sᵢ S'ᵢ K1ᵢ⟩
    | RP Sᵢ S'ᵢ K1ᵢ => ⟨_, constraintRP C Kᵢ Sᵢ S'ᵢ K1ᵢ⟩
  | unsolvable K =>
    match K with
    | CI K1ᵢ => ⟨_, constraintCI C Kᵢ K1ᵢ⟩
    | CG K1ᵢ => ⟨_, constraintCG C Kᵢ K1ᵢ⟩

def validKnowledge {C : Certificate pt} (hC : C.validSets) (Kᵢ : Fin C.knowledge.size) : Prop :=
  (constraintKnowledge hC Kᵢ).snd.valid

structure valid (C : Certificate pt) extends C.validSets where
  validKnowledge : ∀ Kᵢ, C.validKnowledge tovalidSets Kᵢ

namespace valid

lemma actionUnionBounds {C : Certificate pt} (hC : C.valid) (Aᵢ : Fin C.actions.size)
  {A'ᵢ A''ᵢ} (h : C.actions[Aᵢ]? = ActionSetExpr.union A'ᵢ A''ᵢ) :
  A'ᵢ < C.actions.size ∧ A''ᵢ < C.actions.size :=
  by
    have h' := hC.validActions Aᵢ
    rcases Aᵢ with ⟨Aᵢ, hAᵢ⟩
    simp_all [Certificate.validActionSetExpr]
    omega

lemma stateUnionBounds {C : Certificate pt} (hC : C.valid) (Sᵢ : Fin C.states.size)
  {S'ᵢ S''ᵢ} (h : C.states[Sᵢ]? = some (StateSetExpr.union S'ᵢ S''ᵢ)) :
  S'ᵢ < C.states.size ∧ S''ᵢ < C.states.size :=
  by
    have h' := hC.validStates Sᵢ
    rcases Sᵢ with ⟨Sᵢ, hSᵢ⟩
    simp_all [Certificate.validStateSetExpr]
    omega

lemma stateInterBounds {C : Certificate pt} (hC : C.valid) (Sᵢ : Fin C.states.size)
  {S'ᵢ S''ᵢ} (h : C.states[Sᵢ]? = some (StateSetExpr.inter S'ᵢ S''ᵢ)) :
  S'ᵢ < C.states.size ∧ S''ᵢ < C.states.size :=
  by
    have h' := hC.validStates Sᵢ
    rcases Sᵢ with ⟨Sᵢ, hSᵢ⟩
    simp_all [Certificate.validStateSetExpr]
    omega

lemma stateProgrBounds {C : Certificate pt} (hC : C.valid) (Sᵢ : Fin C.states.size)
  {S'ᵢ Aᵢ} (h : C.states[Sᵢ]? = some (StateSetExpr.progr S'ᵢ Aᵢ)) :
  S'ᵢ < C.states.size ∧ Aᵢ < C.actions.size :=
  by
    have h' := hC.validStates Sᵢ
    rcases Sᵢ with ⟨Sᵢ, hSᵢ⟩
    simp_all [Certificate.validStateSetExpr]
    omega

lemma deadKnowledgeBound {C : Certificate pt} (hC : C.valid) (Kᵢ : Fin C.knowledge.size)
  {Sᵢ} (h : ∃ K, C.knowledge[Kᵢ]? = dead Sᵢ K) :
  Sᵢ < C.states.size :=
  by
    have h' := hC.validKnowledge Kᵢ
    rcases h with ⟨K, heq⟩
    simp_all [Certificate.validKnowledge, constraintKnowledge]
    rw [heq] at h'
    simp at h'
    cases K with
    | ED => simp_all [Constraint.valid]
    | UD => simp [constraintUD] at h'; tauto
    | SD => simp [constraintSD] at h'; exact h'.1
    | PG => simp [constraintPG] at h'; exact h'.1
    | PI => simp [constraintPI] at h'; tauto
    | RG => simp [constraintRG] at h'; tauto
    | RI => simp [constraintRI] at h'; exact h'.1

lemma actionSubsetKnowledgeBounds {C : Certificate pt} (hC : C.valid) (Kᵢ : Fin C.knowledge.size)
  {Aᵢ A'ᵢ} (h : ∃ K, C.knowledge[Kᵢ]? = actionSubset Aᵢ A'ᵢ K) :
  Aᵢ < C.actions.size ∧ A'ᵢ < C.actions.size:=
  by
    have h' := hC.validKnowledge Kᵢ
    rcases h with ⟨K, heq⟩
    simp_all [Certificate.validKnowledge, constraintKnowledge]
    rw [heq] at h'
    simp at h'
    cases K with
    | B5 => simp [constraintB5] at h'; tauto
    | URA => simp [constraintUR] at h'; tauto
    | ULA => simp [constraintUL] at h'; tauto
    | SUA => simp [constraintSU] at h'; tauto
    | STA => simp [constraintST] at h'; tauto

lemma stateSubsetKnowledgeBounds
  {C : Certificate pt} (hC : C.valid) (Kᵢ : Fin C.knowledge.size)
  {Sᵢ S'ᵢ} (h : ∃ K, C.knowledge[Kᵢ]? = stateSubset Sᵢ S'ᵢ K) :
  Sᵢ < C.states.size ∧ S'ᵢ < C.states.size:=
  by
    have h' := hC.validKnowledge Kᵢ
    rcases h with ⟨K, heq⟩
    simp_all [Certificate.validKnowledge, constraintKnowledge]
    rw [heq] at h'
    simp at h'
    cases K with
    | B1 => simp [constraintB1] at h'; tauto
    | B2 => simp [constraintB2] at h'; tauto
    | B3 => simp [constraintB3] at h'; tauto
    | B4 => simp [constraintB4] at h'; tauto
    | URS => simp [constraintUR] at h'; tauto
    | ULS => simp [constraintUL] at h'; tauto
    | IRS => simp [constraintIR] at h'; tauto
    | ILS => simp [constraintIL] at h'; tauto
    | DIS => simp [constraintDI] at h'; tauto
    | SUS => simp [constraintSU] at h'; tauto
    | SIS => simp [constraintSI] at h'; tauto
    | STS => simp [constraintST] at h'; tauto
    | AT => simp [constraintAT] at h'; tauto
    | AU => simp [constraintAU] at h'; tauto
    | PT => simp [constraintPT] at h'; tauto
    | PU => simp [constraintPU] at h'; tauto
    | PR => simp [constraintPR] at h'; tauto
    | RP => simp [constraintRP] at h'; tauto

end valid

-- TODO : improve names
private def verifyAll_aux {k} (h : (j : Fin k) → Σ α, Constraint α) : (i : Fin (k + 1)) →
  Result' (∀ j : Fin k, j.val < i → (h j).snd.valid)
| ⟨0, _⟩ => pure ⟨⟨⟩, by rintro j ⟨⟩⟩
| ⟨n + 1, h1⟩ => do
  let ⟨⟨⟩, h2⟩ ← verifyAll_aux h ⟨n, by omega⟩
  let ⟨a, h3⟩ ← (h ⟨n, by omega⟩).snd.verify
  have h : ∀ j : Fin k, j < n + 1 → (h j).snd.valid := by
    intro j hj
    simp_all [Nat.lt_add_one_iff_lt_or_eq]
    rcases hj with h | ⟨rfl⟩
    · exact h2 j h
    · use a
  return ⟨⟨⟩, h⟩

def verifyAll {k} (h : (j : Fin k) → Σ α, Constraint α) : Result' (∀ j : Fin k, (h j).snd.valid) :=
  do
    let ⟨(), h⟩ ← verifyAll_aux h (Fin.last k)
    return ⟨(), by simp_all⟩

private def verifyAll'_aux {k} {p : Fin k → Prop} (verify : (j : Fin k) → Result' (p j)) :
  (i : Fin (k + 1)) →  Result' (∀ j : Fin k, j.val < i → p j)
| ⟨0, _⟩ => pure ⟨⟨⟩, by rintro j ⟨⟩⟩
| ⟨n + 1, h1⟩ => do
  let ⟨⟨⟩, h2⟩ ← verifyAll'_aux verify ⟨n, by omega⟩
  let ⟨⟨⟩, h3⟩ ← verify ⟨n, by omega⟩
  have h : ∀ j : Fin k, j < n + 1 → p j := by
    intro j hj
    simp_all [Nat.lt_add_one_iff_lt_or_eq]
    rcases hj with h | ⟨rfl⟩
    · exact h2 j h
    · exact h3
  return ⟨⟨⟩, h⟩

def verifyAll' {k} {p : Fin k → Prop} (verify : (i : Fin k) → Result' (p i)) : Result' (∀ i, p i) :=
  do
    let ⟨(), h⟩ ← verifyAll'_aux verify (Fin.last k)
    return ⟨(), by simp_all⟩

abbrev IsUnsolvable : Prop :=
  ∃ Kᵢ : Fin C.knowledge.size, ∃ K, C.knowledge[Kᵢ] = unsolvable K

def verifyIsUnsolvable : optParam (Fin (C.knowledge.size + 1)) (Fin.last C.knowledge.size) →
  Result' (IsUnsolvable C)
| 0 => throwUnvalid "Unsolvability NOT proven"
| ⟨Kᵢ + 1, h⟩ =>
  match heq : C.knowledge[Kᵢ] with
  | unsolvable K => return ⟨(), by use ⟨Kᵢ, by omega⟩, K, heq⟩
  | _ => verifyIsUnsolvable ⟨Kᵢ, by omega⟩

def verify : Result' (C.valid ∧ IsUnsolvable C) :=
  do
    let ⟨(), h1⟩ ← verifyAll' C.verifyActionSetExpr
    let ⟨(), h2⟩ ← verifyAll' C.verifyStateSetExpr
    let hC : C.validSets := ⟨h1, h2⟩
    let ⟨(), h3⟩ ← verifyAll (constraintKnowledge hC)
    let ⟨(), h4⟩ ← verifyIsUnsolvable C
    return ⟨(), ⟨hC, h3⟩, h4⟩

end Validator.Certificate
