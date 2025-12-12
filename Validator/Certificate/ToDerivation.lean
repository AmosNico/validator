import Validator.ProofSystem
import Validator.Certificate.ValidCertificate

namespace Validator.Certificate.valid

variable {n : ℕ} {pt : STRIPS n}
open Knowledge Certificate ProofSystem

def conclusion {C : Certificate pt} {hC : C.valid} (Kᵢ : Fin C.knowledge.size) : Prop :=
  match heq : C.knowledge[Kᵢ] with
  | dead Sᵢ K =>
    have hSᵢ : Sᵢ < C.states.size :=
      hC.deadKnowledgeBound Kᵢ (by use K; simp_all)
    let S := hC.getStates ⟨Sᵢ, hSᵢ⟩
    Dead pt S
  | actionSubset Aᵢ A'ᵢ K =>
    have hᵢ : Aᵢ < C.actions.size ∧ A'ᵢ < C.actions.size :=
      hC.actionSubsetKnowledgeBounds Kᵢ (by use K; simp_all)
    let A := hC.getActions ⟨Aᵢ, hᵢ.1⟩
    let A' := hC.getActions ⟨A'ᵢ, hᵢ.2⟩
    A ⊆ A'
  | stateSubset Sᵢ S'ᵢ K =>
    have hᵢ : Sᵢ < C.states.size ∧ S'ᵢ < C.states.size :=
      hC.stateSubsetKnowledgeBounds Kᵢ (by use K; simp_all)
    let S := hC.getStates ⟨Sᵢ, hᵢ.1⟩
    let S' := hC.getStates ⟨S'ᵢ, hᵢ.2⟩
    S ⊆ S'
  | unsolvable _ => Unsolvable pt

lemma conclusionDead
  {C : Certificate pt} (hC : C.valid)
  (Kᵢ : Fin C.knowledge.size) {Sᵢ : Fin C.states.size}
  (h : ∃ K, C.knowledge[Kᵢ]? = dead Sᵢ K) :
  hC.conclusion Kᵢ ↔ Dead pt (hC.getStates Sᵢ) :=
  by
    simp [conclusion]
    split
    all_goals simp_all

lemma conclusionStateSubset
  {C : Certificate pt} (hC : C.valid)
  (Kᵢ : Fin C.knowledge.size) {Sᵢ S'ᵢ : Fin C.states.size}
  (h : ∃ K, C.knowledge[Kᵢ]? = stateSubset Sᵢ S'ᵢ K) :
  hC.conclusion Kᵢ ↔ hC.getStates Sᵢ ⊆ hC.getStates S'ᵢ :=
  by
    simp [conclusion]
    split
    all_goals simp_all

lemma conclusionActionSubset
  {C : Certificate pt} (hC : C.valid)
  (Kᵢ : Fin C.knowledge.size) {Aᵢ A'ᵢ : Fin C.actions.size}
  (h : ∃ K, C.knowledge[Kᵢ]? = actionSubset Aᵢ A'ᵢ K) :
  hC.conclusion Kᵢ ↔ hC.getActions Aᵢ ⊆ hC.getActions A'ᵢ :=
  by
    simp [conclusion]
    split
    all_goals simp_all

lemma conclusionUnsolvable
  {C : Certificate pt} (hC : C.valid)
  (Kᵢ : Fin C.knowledge.size)
  (h : ∃ K, C.knowledge[Kᵢ] = unsolvable K) :
  hC.conclusion Kᵢ ↔ Unsolvable pt :=
  by
    simp [conclusion]
    split
    all_goals simp_all

-- TODO : check whether Kᵢ : ℕ with Kᵢ < C.knowledge.size works better

set_option maxHeartbeats 400000 in
-- Because the following definition is very large with many cases, we need to increase the number of Heartbeats.
def toDerivation {C : Certificate pt} (hC : C.valid) (Kᵢ : Fin C.knowledge.size) :
  Derivation pt (hC.conclusion Kᵢ) :=
  by
    unfold conclusion
    have h := hC.validKnowledge Kᵢ
    unfold Certificate.validKnowledge constraintKnowledge at h
    rcases Kᵢ with ⟨Kᵢ, hKᵢ⟩
    split -- cases on C.knowledge[Kᵢ]
    -- case dead Sᵢ K
    case h_1 Sᵢ K heq =>
      rw [heq] at h
      simp_all
      cases K with
      | ED =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟩, h', _⟩
        simp at h'
        rcases h' with ⟨hSᵢ, hS⟩
        rw [hC.getStatesEmpty ⟨Sᵢ, hSᵢ⟩ hS]
        exact Derivation.ED
      | UD K1ᵢ K2ᵢ =>
        rename' Sᵢ => S1ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨Sᵢ, S'ᵢ⟩, ⟨⟩, ⟨⟩⟩, ⟨h', _⟩⟩
        simp [constraintUD] at h'
        rcases h' with ⟨hK1ᵢ, hK2ᵢ, ⟨hS1ᵢ, hS1⟩, hK1, hK2⟩
        have ⟨hSᵢ, hS'ᵢ⟩: Sᵢ < C.states.size ∧ S'ᵢ < C.states.size :=
          hC.stateUnionBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1
        rw [hC.getStatesUnion ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS1]
        apply Derivation.UD
        · rw [← hC.conclusionDead ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw [← hC.conclusionDead ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
      | SD K1ᵢ K2ᵢ =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, S'ᵢ, ⟨⟩⟩, ⟨h', _⟩⟩
        simp [constraintSD] at h'
        rcases h' with ⟨hSᵢ, hK1ᵢ, hK2ᵢ, hK1, hK2⟩
        have hS'ᵢ : S'ᵢ < C.states.size :=
          hC.deadKnowledgeBound ⟨K1ᵢ, by omega⟩ hK1
        apply Derivation.SD (hC.getStates ⟨Sᵢ, hSᵢ⟩) (hC.getStates ⟨S'ᵢ, hS'ᵢ⟩)
        · rw [← hC.conclusionDead ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw [← hC.conclusionStateSubset ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
      | PG K1ᵢ K2ᵢ K3ᵢ =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩,⟨⟩, ⟨S1ᵢ, S2ᵢ⟩, ⟨⟨Aᵢ, ⟨⟩⟩, ⟨S'ᵢ, ⟨⟩⟩⟩, S3ᵢ, SGᵢ, ⟨⟩⟩, ⟨h', _⟩⟩
        simp [constraintPG] at h'
        rcases h' with ⟨hSᵢ, hK1ᵢ, hK2ᵢ, hK3ᵢ, hK1, ⟨⟨⟨hS1ᵢ, hS1⟩, hAᵢ, hA⟩, ⟨⟨hS2ᵢ, hS2⟩, hK2⟩⟩,
          hK3, ⟨hS3ᵢ, hS3⟩, hSGᵢ, hSG⟩
        have hS'ᵢ : S'ᵢ < C.states.size :=
          hC.deadKnowledgeBound ⟨K2ᵢ, by omega⟩ hK2
        apply Derivation.PG (hC.getStates ⟨Sᵢ, hSᵢ⟩) (hC.getStates ⟨S'ᵢ, hS'ᵢ⟩)
        · rw [← hC.getStatesUnion ⟨S2ᵢ, hS2ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS2]
          rw [← hC.getActionsAll ⟨Aᵢ, hAᵢ⟩ hA]
          rw [← hC.getStatesProg ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS1]
          rw [← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw [← hC.conclusionDead ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
        · rw [← hC.getStatesGoal ⟨SGᵢ, hSGᵢ⟩ hSG]
          rw [← hC.getStatesInter ⟨S3ᵢ, hS3ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨SGᵢ, hSGᵢ⟩ hS3]
          rw [← hC.conclusionDead ⟨K3ᵢ, by omega⟩ hK3]
          exact hC.toDerivation ⟨K3ᵢ, by omega⟩
      | PI K1ᵢ K2ᵢ K3ᵢ =>
        rename' Sᵢ => S1ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩,⟨⟩, Sᵢ, ⟨⟨S2ᵢ, S3ᵢ⟩, ⟨Aᵢ,⟨⟩⟩, S'ᵢ, ⟨⟩⟩, SIᵢ, ⟨⟩⟩, ⟨h', _⟩⟩
        simp [constraintPI] at h'
        rcases h' with ⟨hK1ᵢ, hK2ᵢ, hK3ᵢ, ⟨hS1ᵢ, hS1⟩,
          ⟨hK1, ⟨⟨hS2ᵢ, hS2⟩, hAᵢ, hA⟩, ⟨hS3ᵢ, hS3⟩, hK2⟩, hK3, hSIᵢ, hSI⟩
        have ⟨hSᵢ, hS'ᵢ⟩ : Sᵢ < C.states.size ∧ S'ᵢ < C.states.size :=
          hC.stateUnionBounds ⟨S3ᵢ, hS3ᵢ⟩ hS3
        rw [hC.getStatesNeg ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ hS1]
        apply Derivation.PI (hC.getStates ⟨Sᵢ, hSᵢ⟩) (hC.getStates ⟨S'ᵢ, hS'ᵢ⟩)
        · rw [← hC.getStatesUnion ⟨S3ᵢ, hS3ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS3]
          rw [← hC.getActionsAll ⟨Aᵢ, hAᵢ⟩ hA]
          rw [← hC.getStatesProg ⟨S2ᵢ, hS2ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS2]
          rw [← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw [← hC.conclusionDead ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
        · rw [← hC.getStatesInit ⟨SIᵢ, hSIᵢ⟩ hSI]
          rw [← hC.conclusionStateSubset ⟨K3ᵢ, by omega⟩ hK3]
          exact hC.toDerivation ⟨K3ᵢ, by omega⟩
      | RG K1ᵢ K2ᵢ K3ᵢ =>
        rename' Sᵢ => S1ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨Sᵢ, ⟨S2ᵢ, S3ᵢ⟩, ⟨Aᵢ,⟨⟩⟩, S'ᵢ, ⟨⟩⟩, S4ᵢ, SGᵢ, ⟨⟩⟩, ⟨h', _⟩⟩
        simp [constraintRG] at h'
        rcases h' with ⟨hK1ᵢ, hK2ᵢ, hK3ᵢ, ⟨⟨hS1ᵢ, hS1⟩, hK1, ⟨⟨hS2ᵢ, hS2⟩, hAᵢ, hA⟩,
          ⟨hS3ᵢ, hS3⟩, hK2⟩, hK3, ⟨hS4ᵢ, hS4⟩, hSGᵢ, hSG⟩
        have ⟨hSᵢ, hS'ᵢ⟩ : Sᵢ < C.states.size ∧ S'ᵢ < C.states.size :=
          hC.stateUnionBounds ⟨S3ᵢ, hS3ᵢ⟩ hS3
        rw [hC.getStatesNeg ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ hS1]
        apply Derivation.RG (hC.getStates ⟨Sᵢ, hSᵢ⟩) (hC.getStates ⟨S'ᵢ, hS'ᵢ⟩)
        · rw [← hC.getStatesUnion ⟨S3ᵢ, hS3ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS3]
          rw [← hC.getActionsAll ⟨Aᵢ, hAᵢ⟩ hA]
          rw [← hC.getStatesRegr ⟨S2ᵢ, hS2ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS2]
          rw [← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw [← hC.conclusionDead ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
        · rw [← hC.getStatesGoal ⟨SGᵢ, hSGᵢ⟩ hSG]
          rw [← hC.getStatesNeg ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ hS1]
          rw [← hC.getStatesInter ⟨S4ᵢ, hS4ᵢ⟩ ⟨S1ᵢ, hS1ᵢ⟩ ⟨SGᵢ, hSGᵢ⟩ hS4]
          rw [← hC.conclusionDead ⟨K3ᵢ, by omega⟩ hK3]
          exact hC.toDerivation ⟨K3ᵢ, by omega⟩
      | RI K1ᵢ K2ᵢ K3ᵢ =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with
          ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨S1ᵢ, S2ᵢ⟩, ⟨Aᵢ,⟨⟩⟩, ⟨S'ᵢ, ⟨⟩⟩, ⟨SIᵢ, S3ᵢ⟩, ⟨⟩, ⟨⟩⟩, ⟨h', _⟩⟩
        simp [constraintRI] at h'
        rcases h' with ⟨hSᵢ, hK1ᵢ, hK2ᵢ, hK3ᵢ, hK1, ⟨⟨hS1ᵢ, hS1⟩, hAᵢ, hA⟩,
          ⟨⟨hS2ᵢ, hS2⟩, hK2⟩, hK3, ⟨hSIᵢ, hSI⟩, hS3ᵢ, hS3⟩
        have hS'ᵢ : S'ᵢ < C.states.size :=
          hC.deadKnowledgeBound ⟨K2ᵢ, by omega⟩ hK2
        apply Derivation.RI (hC.getStates ⟨Sᵢ, hSᵢ⟩) (hC.getStates ⟨S'ᵢ, hS'ᵢ⟩)
        · rw [← hC.getStatesUnion ⟨S2ᵢ, hS2ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS2]
          rw [← hC.getActionsAll ⟨Aᵢ, hAᵢ⟩ hA]
          rw [← hC.getStatesRegr ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS1]
          rw [← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw [← hC.conclusionDead ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
        · rw [← hC.getStatesInit ⟨SIᵢ, hSIᵢ⟩ hSI]
          rw [← hC.getStatesNeg ⟨S3ᵢ, hS3ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ hS3]
          rw [← hC.conclusionStateSubset ⟨K3ᵢ, by omega⟩ hK3]
          exact hC.toDerivation ⟨K3ᵢ, by omega⟩
    -- case subsetAction Aᵢ A'ᵢ K
    case h_2 A1ᵢ A2ᵢ K heq =>
      rw [heq] at h
      simp_all
      cases K with
      | B5 =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨_, h, _⟩
        simp at h
        rcases h with ⟨hA1ᵢ, hA2ᵢ, h'⟩
        simp [hA1ᵢ, hA2ᵢ] at h'
        exact Derivation.B5 _ _ h'
      | URA =>
        rename' A1ᵢ => Aᵢ, A2ᵢ => A1ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, A'ᵢ⟩, h', _⟩
        simp [constraintUR] at h'
        rcases h' with ⟨hAᵢ, hA1ᵢ, hA1⟩
        have hA'ᵢ : A'ᵢ < C.actions.size :=
          (hC.actionUnionBounds ⟨A1ᵢ, hA1ᵢ⟩ hA1).2
        rw [hC.getActionsUnion ⟨A1ᵢ, hA1ᵢ⟩ ⟨Aᵢ, hAᵢ⟩ ⟨A'ᵢ, hA'ᵢ⟩ hA1]
        apply Derivation.UR
      | ULA =>
        rename' A1ᵢ => Aᵢ, A2ᵢ => A1ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, A'ᵢ⟩, h', _⟩
        simp [constraintUL] at h'
        rcases h' with ⟨hAᵢ, hA1ᵢ, hA1⟩
        have hA'ᵢ : A'ᵢ < C.actions.size :=
          (hC.actionUnionBounds ⟨A1ᵢ, hA1ᵢ⟩ hA1).1
        rw [hC.getActionsUnion ⟨A1ᵢ, hA1ᵢ⟩ ⟨A'ᵢ, hA'ᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hA1]
        apply Derivation.UL
      | SUA K1ᵢ K2ᵢ =>
        rename' A2ᵢ => A''ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨Aᵢ, A'ᵢ⟩, ⟨⟩, ⟨⟩⟩, h', _⟩
        simp [constraintSU] at h'
        rcases h' with ⟨hA''ᵢ, hK1ᵢ, hK2ᵢ, ⟨hA1ᵢ, hA1⟩, hK1, hK2⟩
        obtain ⟨hAᵢ, hA'ᵢ⟩ : Aᵢ < C.actions.size ∧ A'ᵢ < C.actions.size :=
          hC.actionUnionBounds ⟨A1ᵢ, hA1ᵢ⟩ hA1
        rw [hC.getActionsUnion ⟨A1ᵢ, hA1ᵢ⟩ ⟨Aᵢ, hAᵢ⟩ ⟨A'ᵢ, hA'ᵢ⟩ hA1]
        apply Derivation.SU (hC.getActions ⟨Aᵢ, hAᵢ⟩)
        · rw[← hC.conclusionActionSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw[← hC.conclusionActionSubset ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
      | STA K1ᵢ K2ᵢ =>
        rename' A1ᵢ => Aᵢ, A2ᵢ => A''ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, A'ᵢ, ⟨⟩⟩, h', _⟩
        simp [constraintST] at h'
        rcases h' with ⟨hAᵢ, hA''ᵢ, hK1ᵢ, hK2ᵢ, hK1, hK2⟩
        have hA'ᵢ : A'ᵢ < C.actions.size :=
          (hC.actionSubsetKnowledgeBounds ⟨K1ᵢ, by omega⟩ hK1).2
        apply Derivation.ST _ (hC.getActions ⟨A'ᵢ, hA'ᵢ⟩)
        · rw[← hC.conclusionActionSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw[← hC.conclusionActionSubset ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
    -- case subsetState Sᵢ S'ᵢ K
    case h_3 S1ᵢ S2ᵢ K heq =>
      rw [heq] at h
      simp_all
      cases K with
      | B1 => -- TODO: this is the same as B2 and B3
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟩, h, _⟩
        simp at h
        rcases h with ⟨hS1ᵢ, hS2ᵢ, h'⟩
        simp [hS1ᵢ, hS2ᵢ] at h'
        rcases h' with ⟨h1, h2, h3⟩
        exact Derivation.B1 _ h1 h2 h3
      | B2 =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟩, h, _⟩
        simp at h
        rcases h with ⟨hS1ᵢ, hS2ᵢ, h'⟩
        simp [hS1ᵢ, hS2ᵢ] at h'
        rcases h' with ⟨h1, h2, h3⟩
        exact Derivation.B2 _ h1 h2 h3
      | B3 =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟩, h, _⟩
        simp at h
        rcases h with ⟨hS1ᵢ, hS2ᵢ, h'⟩
        simp [hS1ᵢ, hS2ᵢ] at h'
        rcases h' with ⟨h1, h2, h3⟩
        exact Derivation.B3 _ h1 h2 h3
      | B4 =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟩, h, _⟩
        simp at h
        rcases h with ⟨hS1ᵢ, hS2ᵢ, h'⟩
        simp [hS1ᵢ, hS2ᵢ] at h'
        rcases h' with ⟨h1, h2, h3⟩
        exact Derivation.B4 _ _ h1 h2 h3
      | URS =>
        rename' S1ᵢ => Sᵢ, S2ᵢ => S1ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, S'ᵢ⟩, h', _⟩
        simp [constraintUR] at h'
        rcases h' with ⟨hSᵢ, hS1ᵢ, hS1⟩
        have hS'ᵢ : S'ᵢ < C.states.size :=
          (hC.stateUnionBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1).2
        rw [hC.getStatesUnion ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS1]
        apply Derivation.UR
      | ULS =>
        rename' S1ᵢ => Sᵢ, S2ᵢ => S1ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, S'ᵢ⟩, h', _⟩
        simp [constraintUL] at h'
        rcases h' with ⟨hSᵢ, hS1ᵢ, hS1⟩
        have hS'ᵢ : S'ᵢ < C.states.size :=
          (hC.stateUnionBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1).1
        rw [hC.getStatesUnion ⟨S1ᵢ, hS1ᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ hS1]
        apply Derivation.UL
      | IRS =>
        rename' S2ᵢ => Sᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, S'ᵢ⟩, h', _⟩
        simp [constraintIR] at h'
        rcases h' with ⟨hSᵢ, hS1ᵢ, hS1⟩
        have hS'ᵢ : S'ᵢ < C.states.size :=
          (hC.stateInterBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1).2
        rw [hC.getStatesInter ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS1]
        apply Derivation.IR
      | ILS =>
        rename' S2ᵢ => Sᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, S'ᵢ⟩, h', _⟩
        simp [constraintIL] at h'
        rcases h' with ⟨hSᵢ, hS1ᵢ, hS1⟩
        have hS'ᵢ : S'ᵢ < C.states.size :=
          (hC.stateInterBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1).1
        rw [hC.getStatesInter ⟨S1ᵢ, hS1ᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ hS1]
        apply Derivation.IL
      | DIS =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨S3ᵢ, S''ᵢ⟩, ⟨Sᵢ, S'ᵢ⟩, ⟨S4ᵢ, S5ᵢ⟩, ⟨⟩,⟨⟩⟩, h', _⟩
        simp [constraintDI] at h'
        rcases h' with ⟨⟨hS1ᵢ, hS1⟩, ⟨hS3ᵢ, hS3⟩, ⟨hS2ᵢ, hS2⟩, ⟨hS4ᵢ, hS4⟩, hS5ᵢ, hS5⟩
        obtain ⟨hSᵢ, hS'ᵢ⟩ : Sᵢ < C.states.size ∧ S'ᵢ < C.states.size :=
          hC.stateUnionBounds ⟨S3ᵢ, hS3ᵢ⟩ hS3
        have hS''ᵢ : S''ᵢ < C.states.size :=
          (hC.stateInterBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1).2
        rw [hC.getStatesInter ⟨S1ᵢ, hS1ᵢ⟩ ⟨S3ᵢ, hS3ᵢ⟩ ⟨S''ᵢ, hS''ᵢ⟩ hS1]
        rw [hC.getStatesUnion ⟨S3ᵢ, hS3ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS3]
        rw [hC.getStatesUnion ⟨S2ᵢ, hS2ᵢ⟩ ⟨S4ᵢ, hS4ᵢ⟩ ⟨S5ᵢ, hS5ᵢ⟩ hS2]
        rw [hC.getStatesInter ⟨S4ᵢ, hS4ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S''ᵢ, hS''ᵢ⟩ hS4]
        rw [hC.getStatesInter ⟨S5ᵢ, hS5ᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ ⟨S''ᵢ, hS''ᵢ⟩ hS5]
        apply Derivation.DI
      | SUS K1ᵢ K2ᵢ =>
        rename' S2ᵢ => S''ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨Sᵢ, S'ᵢ⟩, ⟨⟩, ⟨⟩⟩, h', _⟩
        simp [constraintSU] at h'
        rcases h' with ⟨hS''ᵢ, hK1ᵢ, hK2ᵢ, ⟨hS1ᵢ, hS1⟩, hK1, hK2⟩
        obtain ⟨hSᵢ, hS'ᵢ⟩ : Sᵢ < C.states.size ∧ S'ᵢ < C.states.size :=
          hC.stateUnionBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1
        rw [hC.getStatesUnion ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS1]
        apply Derivation.SU (hC.getStates ⟨Sᵢ, hSᵢ⟩)
        · rw[← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw[← hC.conclusionStateSubset ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
      | SIS K1ᵢ K2ᵢ =>
        rename' S1ᵢ => Sᵢ, S2ᵢ => S1ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨S'ᵢ, S''ᵢ⟩, ⟨⟩, ⟨⟩⟩, h', _⟩
        simp [constraintSI] at h'
        rcases h' with ⟨hSᵢ, hK1ᵢ, hK2ᵢ, ⟨hS1ᵢ, hS1⟩, hK1, hK2⟩
        obtain ⟨hS'ᵢ, hS''ᵢ⟩ : S'ᵢ < C.states.size ∧ S''ᵢ < C.states.size :=
          hC.stateInterBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1
        rw [hC.getStatesInter ⟨S1ᵢ, hS1ᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ ⟨S''ᵢ, hS''ᵢ⟩ hS1]
        apply Derivation.SI (hC.getStates ⟨Sᵢ, hSᵢ⟩)
        · rw[← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw[← hC.conclusionStateSubset ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
      | STS K1ᵢ K2ᵢ =>
        rename' S1ᵢ => Sᵢ, S2ᵢ => S''ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, S'ᵢ, ⟨⟩⟩, h', _⟩
        simp [constraintST] at h'
        rcases h' with ⟨hSᵢ, hS''ᵢ, hK1ᵢ, hK2ᵢ, hK1, hK2⟩
        have hS'ᵢ : S'ᵢ < C.states.size :=
          (hC.stateSubsetKnowledgeBounds ⟨K1ᵢ, by omega⟩ hK1).2
        apply Derivation.ST _ (hC.getStates ⟨S'ᵢ, hS'ᵢ⟩)
        · rw[← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw[← hC.conclusionStateSubset ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
      | AT K1ᵢ K2ᵢ =>
        rename' S2ᵢ => S'ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨Sᵢ, A'ᵢ⟩, S2ᵢ, Aᵢ, ⟨⟩⟩, h', _⟩
        simp [constraintAT] at h'
        rcases h' with ⟨hS'ᵢ, hK1ᵢ, hK2ᵢ, ⟨hS1ᵢ, hS1⟩, hK1, ⟨hS2ᵢ, hS2⟩,hK2⟩
        obtain ⟨hSᵢ, hA'ᵢ⟩ : Sᵢ < C.states.size ∧ A'ᵢ < C.actions.size :=
          hC.stateProgrBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1
        have hAᵢ : Aᵢ < C.actions.size :=
          (hC.stateProgrBounds ⟨S2ᵢ, hS2ᵢ⟩ hS2).2
        rw[hC.getStatesProg ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨A'ᵢ, hA'ᵢ⟩ hS1]
        apply Derivation.AT
        · rw[← hC.getStatesProg ⟨S2ᵢ, hS2ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS2]
          rw[← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw[← hC.conclusionActionSubset ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
      | AU K1ᵢ K2ᵢ =>
        rename' S2ᵢ => S'ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨Sᵢ, A1ᵢ⟩, ⟨Aᵢ, A'ᵢ⟩, ⟨S2ᵢ, ⟨⟩⟩, S3ᵢ, ⟨⟩⟩, h', _⟩
        simp [constraintAU] at h'
        rcases h' with ⟨hS'ᵢ, hK1ᵢ, hK2ᵢ, ⟨hS1ᵢ, hS1⟩, ⟨hA1ᵢ, hA1⟩, ⟨hK1, hS2ᵢ, hS2⟩,
          hK2, hS3ᵢ, hS3⟩
        obtain ⟨hSᵢ, hAᵢ⟩ : Sᵢ < C.states.size ∧ Aᵢ < C.actions.size :=
          hC.stateProgrBounds ⟨S2ᵢ, hS2ᵢ⟩ hS2
        have hA'ᵢ : A'ᵢ < C.actions.size :=
          (hC.stateProgrBounds ⟨S3ᵢ, hS3ᵢ⟩ hS3).2
        rw[hC.getStatesProg ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨A1ᵢ, hA1ᵢ⟩ hS1]
        rw[hC.getActionsUnion ⟨A1ᵢ, hA1ᵢ⟩ ⟨Aᵢ, hAᵢ⟩ ⟨A'ᵢ, hA'ᵢ⟩ hA1]
        apply Derivation.AU
        · rw[← hC.getStatesProg ⟨S2ᵢ, hS2ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS2]
          rw[← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw[← hC.getStatesProg ⟨S3ᵢ, hS3ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨A'ᵢ, hA'ᵢ⟩ hS3]
          rw[← hC.conclusionStateSubset ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
      | PT K1ᵢ K2ᵢ =>
        rename' S2ᵢ => S''ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨S'ᵢ, Aᵢ⟩, S2ᵢ, Sᵢ, ⟨⟩⟩, h', _⟩
        simp [constraintPT] at h'
        rcases h' with ⟨hS''ᵢ, hK1ᵢ, hK2ᵢ, ⟨hS1ᵢ, hS1⟩, hK1, ⟨hS2ᵢ, hS2⟩,hK2⟩
        obtain ⟨hS'ᵢ, hAᵢ⟩ : S'ᵢ < C.states.size ∧ Aᵢ < C.actions.size :=
          hC.stateProgrBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1
        have hSᵢ : Sᵢ < C.states.size :=
          (hC.stateProgrBounds ⟨S2ᵢ, hS2ᵢ⟩ hS2).1
        rw[hC.getStatesProg ⟨S1ᵢ, hS1ᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS1]
        apply Derivation.PT
        · rw[← hC.getStatesProg ⟨S2ᵢ, hS2ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS2]
          rw[← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw[← hC.conclusionStateSubset ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
      | PU K1ᵢ K2ᵢ =>
        rename' S2ᵢ => S''ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨S2ᵢ, Aᵢ⟩, ⟨Sᵢ, S'ᵢ⟩, ⟨S3ᵢ, ⟨⟩⟩, S4ᵢ, ⟨⟩⟩, h', _⟩
        simp [constraintPU] at h'
        rcases h' with ⟨hS''ᵢ, hK1ᵢ, hK2ᵢ, ⟨hS1ᵢ, hS1⟩, ⟨hS2ᵢ, hS2⟩,
          ⟨hK1, hS3ᵢ, hS3⟩, hK2, hS4ᵢ, hS4⟩
        obtain hAᵢ : Aᵢ < C.actions.size :=
          (hC.stateProgrBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1).2
        obtain ⟨hSᵢ, hS'ᵢ⟩ : Sᵢ < C.states.size ∧ S'ᵢ < C.states.size :=
          hC.stateUnionBounds ⟨S2ᵢ, hS2ᵢ⟩ hS2
        rw[hC.getStatesProg ⟨S1ᵢ, hS1ᵢ⟩ ⟨S2ᵢ, hS2ᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS1]
        rw[hC.getStatesUnion ⟨S2ᵢ, hS2ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS2]
        apply Derivation.PU
        · rw[← hC.getStatesProg ⟨S3ᵢ, hS3ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS3]
          rw[← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
        · rw[← hC.getStatesProg ⟨S4ᵢ, hS4ᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS4]
          rw[← hC.conclusionStateSubset ⟨K2ᵢ, by omega⟩ hK2]
          exact hC.toDerivation ⟨K2ᵢ, by omega⟩
      | PR K1ᵢ =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨S3ᵢ, Aᵢ⟩, S'ᵢ, Sᵢ, S4ᵢ, ⟨⟩⟩, h', _⟩
        simp [constraintPR] at h'
        rcases h' with ⟨hK1ᵢ, ⟨hS1ᵢ, hS1⟩, ⟨hS3ᵢ, hS3⟩, ⟨hS2ᵢ, hS2⟩,
           hK1, hS4ᵢ, hS4⟩
        obtain ⟨hSᵢ, hAᵢ⟩ : Sᵢ < C.states.size ∧ Aᵢ < C.actions.size :=
          hC.stateProgrBounds ⟨S4ᵢ, hS4ᵢ⟩ hS4
        obtain hS'ᵢ : S'ᵢ < C.states.size :=
          (hC.stateSubsetKnowledgeBounds ⟨K1ᵢ, by omega⟩ hK1).2
        rw[hC.getStatesRegr ⟨S1ᵢ, hS1ᵢ⟩ ⟨S3ᵢ, hS3ᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS1]
        rw [hC.getStatesNeg ⟨S2ᵢ, hS2ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ hS2]
        rw [hC.getStatesNeg ⟨S3ᵢ, hS3ᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS3]
        apply Derivation.PR
        · rw[← hC.getStatesProg ⟨S4ᵢ, hS4ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS4]
          rw[← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
      | RP K1ᵢ =>
        rename' S2ᵢ => S'ᵢ
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, ⟨⟩, ⟨Sᵢ, Aᵢ⟩, ⟨S2ᵢ, S3ᵢ⟩, ⟨S4ᵢ, ⟨⟩⟩, ⟨⟩⟩, h', _⟩
        simp [constraintRP] at h'
        rcases h' with ⟨hS'ᵢ, hK1ᵢ, ⟨hS1ᵢ, hS1⟩,
          hK1, ⟨⟨hS2ᵢ, hS2⟩, hS4ᵢ, hS4⟩, hS3ᵢ, hS3⟩
        obtain ⟨hSᵢ, hAᵢ⟩ : Sᵢ < C.states.size ∧ Aᵢ < C.actions.size :=
          hC.stateProgrBounds ⟨S1ᵢ, hS1ᵢ⟩ hS1
        rw[hC.getStatesProg ⟨S1ᵢ, hS1ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS1]
        apply Derivation.RP
        · rw [← hC.getStatesNeg ⟨S3ᵢ, hS3ᵢ⟩ ⟨Sᵢ, hSᵢ⟩ hS3]
          rw [← hC.getStatesNeg ⟨S4ᵢ, hS4ᵢ⟩ ⟨S'ᵢ, hS'ᵢ⟩ hS4]
          rw[← hC.getStatesRegr ⟨S2ᵢ, hS2ᵢ⟩ ⟨S4ᵢ, hS4ᵢ⟩ ⟨Aᵢ, hAᵢ⟩ hS2]
          rw[← hC.conclusionStateSubset ⟨K1ᵢ, by omega⟩ hK1]
          exact hC.toDerivation ⟨K1ᵢ, by omega⟩
    -- case unsolvable K
    case h_4 K heq =>
      rw [heq] at h
      simp_all
      cases K with
      | CI K1ᵢ =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, SIᵢ, ⟨⟩⟩, h', _⟩
        simp [constraintCI] at h'
        rcases h' with ⟨hK1ᵢ, hK1, hSIᵢ, hSI⟩
        apply Derivation.CI
        rw [← hC.getStatesInit ⟨SIᵢ, hSIᵢ⟩ hSI]
        rw [← hC.conclusionDead ⟨K1ᵢ, by omega⟩ hK1]
        exact hC.toDerivation ⟨K1ᵢ, by omega⟩
      | CG K1ᵢ =>
        simp only at h
        apply Constraint.elim_exists at h
        rcases h with ⟨⟨⟨⟩, SGᵢ, ⟨⟩⟩, h', _⟩
        simp [constraintCG] at h'
        rcases h' with ⟨hK1ᵢ, hK1, hSGᵢ, hSG⟩
        apply Derivation.CG
        rw [← hC.getStatesGoal ⟨SGᵢ, hSGᵢ⟩ hSG]
        rw [← hC.conclusionDead ⟨K1ᵢ, by omega⟩ hK1]
        exact hC.toDerivation ⟨K1ᵢ, by omega⟩
  termination_by Kᵢ

theorem soundness' {C : Certificate pt} (hC : C.valid) (Kᵢ : Fin C.knowledge.size) :
  hC.conclusion Kᵢ :=
  Derivation.soundness (hC.toDerivation Kᵢ)

theorem soundness {C : Certificate pt} (hC : C.valid) (h : C.IsUnsolvable) : Unsolvable pt :=
  by
    rcases h with ⟨Kᵢ, hK⟩
    rw [← hC.conclusionUnsolvable Kᵢ hK]
    exact hC.soundness' Kᵢ

end Validator.Certificate.valid
