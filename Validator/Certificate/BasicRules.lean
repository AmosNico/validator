module

public import Validator.Certificate.Constraint
public import Validator.Certificate.SetExpr
import Validator.StateSetFormalism.StateSetFormalism

namespace Validator

set_option backward.do.legacy true

open STRIPS
open Constraint Certificate.validSets
open ActionSubsetKnowledge StateSubsetKnowledge
open Formalism StateSetFormalism
open Formula (Model)

variable {n : ℕ} {pt : PlanningTask n} {C : Certificate pt}

namespace Certificate.validSets
open StateSetFormalism

/-- Returns none if the formula is constant -/
def getFormalism' (hC : C.validSets) (Sᵢ : Fin C.states.size) : Option StateSetFormalism :=
  match  heq : C.states[Sᵢ] with
  | .empty => none
  | .init => none
  | .goal => none
  | .bdd _ => bdd
  | .horn _ => horn
  | .mods _ => mods
  | .neg S'ᵢ =>
    have : S'ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    hC.getFormalism' ⟨S'ᵢ, by omega⟩
  | .inter S'ᵢ S''ᵢ =>
    have : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    match hC.getFormalism' ⟨S'ᵢ, by omega⟩ with
    | none => hC.getFormalism' ⟨S''ᵢ, by omega⟩
    | R => R
  | .union S'ᵢ S''ᵢ =>
    have : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    match hC.getFormalism' ⟨S'ᵢ, by omega⟩ with
    | none => hC.getFormalism' ⟨S''ᵢ, by omega⟩
    | R => R
  | .progr S'ᵢ _ =>
    have : S'ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    hC.getFormalism' ⟨S'ᵢ, by omega⟩
  | .regr S'ᵢ _ =>
    have : S'ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    hC.getFormalism' ⟨S'ᵢ, by omega⟩

public def getFormalism (hC : C.validSets) : List (Fin C.states.size) → StateSetFormalism
  | [] => mods -- Fallback if all sets are constant
  | Sᵢ :: tail =>
    match hC.getFormalism' Sᵢ with
    | none => hC.getFormalism tail
    | some F => F

def throwIncompatibleFormalism {α : outParam Type} {p} (R R' : StateSetFormalism) (Sᵢ : ℕ) :
    Result α p :=
  throw <| .unexpected .StateSet Sᵢ s!"a {R} formula" s!"a {R'} formula"

def get_variable (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
    Result (UnprimedVariable' pt R) fun x ↦
      hC.getStates Sᵢ = x.val.toStates ∧ IsVariable pt (R.type pt) (hC.getStates Sᵢ) :=
  match heq : C.states[Sᵢ] with
  | .empty =>
    have h1 : hC.getStates Sᵢ = ∅ :=
      hC.getStatesEmpty Sᵢ (by simp_all)
    have h2 : IsVariable pt (type pt R) (hC.getStates Sᵢ) := by
      rw [h1]
      exact IsVariable.empty
    return ⟨R.mkEmpty pt, by simp [h1], h2⟩
  | .init =>
    have h1 : hC.getStates Sᵢ = {pt.init} :=
      hC.getStatesInit Sᵢ (by simp_all)
    have h2 : IsVariable pt (type pt R) (hC.getStates Sᵢ) := by
      rw [h1]
      exact IsVariable.init
    return ⟨R.mkInit pt, by simp [h1], h2⟩
  | .goal =>
    have h1 : hC.getStates Sᵢ = pt.goalStates :=
      hC.getStatesGoal Sᵢ (by simp_all)
    have h2 : IsVariable pt (type pt R) (hC.getStates Sᵢ) := by
      rw [h1]
      exact IsVariable.goal
    return ⟨R.mkGoal pt, by simp [h1], h2⟩
  | .bdd φ =>
    if heq' : R = bdd then by
      subst heq'
      have h1 : hC.getStates Sᵢ = φ.val.toStates :=
        hC.getStatesBdd Sᵢ (by simp_all)
      have h2 : IsVariable pt (type pt bdd) (hC.getStates Sᵢ) := by
        rw [h1]
        exact IsVariable.explicit φ.val
      exact return ⟨φ, h1, h2⟩
    else
      throwIncompatibleFormalism bdd R Sᵢ
  | .horn φ =>
    if heq' : R = horn then by
      subst heq'
      have h1 : hC.getStates Sᵢ = φ.val.toStates :=
        hC.getStatesHorn Sᵢ (by simp_all)
      have h2 : IsVariable pt (type pt horn) (hC.getStates Sᵢ) := by
        rw [h1]
        exact IsVariable.explicit φ.val
      exact return ⟨φ, h1, h2⟩
    else
      throwIncompatibleFormalism horn R Sᵢ
  | .mods φ =>
    if heq' : R = mods then by
      subst heq'
      have h1 : hC.getStates Sᵢ = φ.val.toStates :=
        hC.getStatesMods Sᵢ (by simp_all)
      have h2 : IsVariable pt (type pt mods) (hC.getStates Sᵢ) := by
        rw [h1]
        exact IsVariable.explicit φ.val
      exact return ⟨φ, h1, h2⟩
    else
      throwIncompatibleFormalism mods R Sᵢ
  | S =>
    throw <| .unexpected .StateSet Sᵢ s!"a constant state set or an atomic {R} formula" (toString S)

def get_literal (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
    Result (UnprimedLiteral' pt R) fun l ↦
      hC.getStates Sᵢ = l.val.toStates ∧ IsLiteral pt (R.type pt) (hC.getStates Sᵢ) :=
  withErrorMessage s!"Verifying that the state set #{Sᵢ} is a {R} literal" <|
  match heq : C.states[Sᵢ] with
  | .neg S'ᵢ => do
    have : S'ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    let ⟨x, h1, h2⟩ ← hC.get_variable R ⟨S'ᵢ, by omega⟩
    let l : UnprimedLiteral' pt R := .neg x
    have h3 : hC.getStates Sᵢ = l.val.toStates := by
      simp only [UnprimedLiteral.val_neg, Literal.toStates_neg, l]
      rw [← h1]
      exact hC.getStatesNeg Sᵢ ⟨S'ᵢ, by omega⟩ (by simp_all)
    have h4 : IsLiteral pt (type pt R) (hC.getStates Sᵢ) := by
      simp_all only [UnprimedLiteral.val_neg, Literal.toStates_neg, l]
      exact IsLiteral.neg h2
    return ⟨l, h3, h4⟩
  | _ => do
    let ⟨x, h1, h2⟩ ← hC.get_variable R ⟨Sᵢ, by omega⟩
    let l : UnprimedLiteral' pt R := .pos x
    have h3 : hC.getStates Sᵢ = l.val.toStates := by
      simp_all only [UnprimedLiteral.val_pos, Literal.toStates_pos, l]
    have h4 : IsLiteral pt (type pt R) (hC.getStates Sᵢ) := by
      rw [h3] at ⊢ h2
      exact IsLiteral.pos h2
    return ⟨l, h3, h4⟩

def get_union_literals (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
    Result (UnprimedLiterals' pt R)
      fun L ↦ hC.getStates Sᵢ = L.val.union ∧ IsLiteralUnion pt (R.type pt) (hC.getStates Sᵢ) :=
  withErrorMessage s!"Verifying that the state set #{Sᵢ} is a union of {R} literals" <|
  match heq : C.states[Sᵢ] with
  | .union S'ᵢ S''ᵢ => do
    have ⟨hS'ᵢ, hS''ᵢ⟩ : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    let ⟨L1, h1, h2⟩ ← hC.get_union_literals R ⟨S'ᵢ, by omega⟩
    let ⟨L2, h3, h4⟩ ← hC.get_union_literals R ⟨S''ᵢ, by omega⟩
    have h5 : hC.getStates Sᵢ = (L1 ++ L2).val.union := by
      simp only [UnprimedLiterals.val_append, Literals.union_append]
      rw [← h1, ← h3]
      exact hC.getStatesUnion Sᵢ ⟨S'ᵢ, by omega⟩ ⟨S''ᵢ, by omega⟩ (by simp_all)
    have h6 : IsLiteralUnion pt (type pt R) (hC.getStates Sᵢ) := by
      simp_all only [UnprimedLiterals.val_append, Literals.union_append]
      exact IsLiteralUnion.union h2 h4
    return ⟨L1 ++ L2, h5, h6⟩
  | _ => do
    let ⟨l, h1, h2⟩ ← hC.get_literal R ⟨Sᵢ, by omega⟩
    return ⟨UnprimedLiterals.single l, by
      simp_all only [Fin.getElem_fin, Fin.eta, UnprimedLiterals.union_single, true_and]
      exact IsLiteralUnion.single h2⟩

def get_inter_literals (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
    Result (UnprimedLiterals' pt R)
      fun L ↦ hC.getStates Sᵢ = L.val.inter ∧ IsLiteralInter pt (R.type pt) (hC.getStates Sᵢ) :=
  withErrorMessage s!"Verifying that the state set #{Sᵢ} is an intersection of {R} literals" <|
  match heq : C.states[Sᵢ] with
  | .inter S'ᵢ S''ᵢ => do
    have ⟨hS'ᵢ, hS''ᵢ⟩ : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    let ⟨L1, h1, h2⟩ ← hC.get_inter_literals R ⟨S'ᵢ, by omega⟩
    let ⟨L2, h3, h4⟩ ← hC.get_inter_literals R ⟨S''ᵢ, by omega⟩
    have h5 : hC.getStates Sᵢ = (L1 ++ L2).val.inter := by
      simp only [UnprimedLiterals.val_append, UnprimedLiterals.inter_append]
      rw [← h1, ← h3]
      exact hC.getStatesInter Sᵢ ⟨S'ᵢ, by omega⟩ ⟨S''ᵢ, by omega⟩ (by simp_all)
    have h6 : IsLiteralInter pt (type pt R) (hC.getStates Sᵢ) := by
      simp_all only [Fin.getElem_fin, UnprimedLiterals.inter_val, UnprimedLiterals.val_append,
        UnprimedLiterals.inter_append]
      exact IsLiteralInter.inter h2 h4
    return ⟨(L1 ++ L2), h5, h6⟩
  | _ => do
    let ⟨l, h1, h2⟩ ← hC.get_literal R ⟨Sᵢ, by omega⟩
    return ⟨UnprimedLiterals.single l, by
      simp_all only [Fin.getElem_fin, Fin.eta, UnprimedLiterals.inter_single, true_and]
      exact IsLiteralInter.single h2⟩

def get_inter_variables (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
    Result (UnprimedVariables' pt R)
      fun X ↦ hC.getStates Sᵢ = X.val.inter ∧ IsVariableInter pt (R.type pt) (hC.getStates Sᵢ) :=
  withErrorMessage
    s!"Verifying that the state set #{Sᵢ} is an intersection of atomic {R} formulas" <|
  match heq : C.states[Sᵢ] with
  | .inter S'ᵢ S''ᵢ => do
    have ⟨hS'ᵢ, hS''ᵢ⟩ : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    let ⟨X1, h1, h2⟩ ← hC.get_inter_variables R ⟨S'ᵢ, by omega⟩
    let ⟨X2, h3, h4⟩ ← hC.get_inter_variables R ⟨S''ᵢ, by omega⟩
    have h5 : hC.getStates Sᵢ = (X1 ++ X2).val.inter := by
      simp only [UnprimedVariables.inter_append]
      rw [← h1, ← h3]
      exact hC.getStatesInter Sᵢ ⟨S'ᵢ, by omega⟩ ⟨S''ᵢ, by omega⟩ (by simp_all)
    have h6 : IsVariableInter pt (type pt R) (hC.getStates Sᵢ) := by
      simp_all only [UnprimedVariables.inter_append]
      exact IsVariableInter.inter h2 h4
    return ⟨(X1 ++ X2), h5, h6⟩
  | _ => do
    let ⟨x, h1, h2⟩ ← hC.get_variable R ⟨Sᵢ, by omega⟩
    return ⟨UnprimedVariables.single x, by
      simp_all only [Fin.getElem_fin, Fin.eta, UnprimedVariables.val_single, Variables.inter_single,
        true_and]
      exact IsVariableInter.single h2⟩

def get_progression_variables (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
    Result (UnprimedVariables' pt R × ActionIds pt)
      fun (X, A) ↦ hC.getStates Sᵢ = progression X.val.inter A.toActions ∧
        IsVariableInter pt (R.type pt) X.val.inter :=
  withErrorMessage s!"Verifying that the state set #{Sᵢ} is the progression \
    of an intersection of atomic {R} formulas" do
  let ⟨(S'ᵢ, Aᵢ), h⟩ ← (Constraint.isStateProgr C Sᵢ).verify
  have ⟨hS'ᵢ, hAᵢ⟩ : S'ᵢ < Sᵢ ∧ Aᵢ < C.actions.size := by
    have := hC.validStates Sᵢ
    simp_all [Certificate.validStateSetExpr]
  let ⟨X, h1, h2⟩ ← hC.get_inter_variables R ⟨S'ᵢ, by omega⟩
  let A := hC.getActionIds ⟨Aᵢ, by omega⟩
  have h3 : hC.getStates Sᵢ = progression X.val.inter A.toActions := by
    rw[ hC.getStatesProg Sᵢ ⟨S'ᵢ, by omega⟩ ⟨Aᵢ, by omega⟩ (by simp_all)]
    simp only [h1, getActions_eq, A]
  return ⟨(X, A), h3, by simp_all only⟩

def get_progression_inter (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
    Result (UnprimedVariables' pt R × ActionIds pt × UnprimedLiterals' pt R)
      fun (X, A, L) ↦ hC.getStates Sᵢ = progression X.val.inter A.toActions ∩ L.val.inter ∧
        IsProgrInter pt (R.type pt) (hC.getStates Sᵢ) :=
  withErrorMessage s!"Verifying that the state set #{Sᵢ} is the intersection of the progression \
    of an intersection of atomic {R} formulas and the intersection of {R} literals" <|
  match heq : C.states[Sᵢ] with
  | .inter S'ᵢ S''ᵢ => do
    have ⟨hS'ᵢ, hS''ᵢ⟩ : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    let ⟨(X, A), h1, h2⟩ ← hC.get_progression_variables R ⟨S'ᵢ, by omega⟩
    let ⟨L, h3, h4⟩ ← hC.get_inter_literals R ⟨S''ᵢ, by omega⟩
    have h5 : hC.getStates Sᵢ = progression X.val.inter A.toActions ∩ L.val.inter  := by
      rw [← h1, ← h3]
      exact hC.getStatesInter Sᵢ ⟨S'ᵢ, by omega⟩ ⟨S''ᵢ, by omega⟩ (by simp_all)
    have h6 : IsProgrInter pt (R.type pt) (hC.getStates Sᵢ) := by
      simp_all only [UnprimedLiterals.inter_val]
      exact IsProgrInter.inter h2 h4
    return ⟨(X, A, L), h5, h6⟩
  | .progr S'ᵢ Aᵢ => do
    let ⟨(X, A), h1, h2⟩ ← hC.get_progression_variables R Sᵢ
    let L := UnprimedLiterals.empty
    have h3 : hC.getStates Sᵢ = progression X.val.inter A.toActions ∩ L.val.inter := by
      simp_all [L, UnprimedVariables.val]
    have h4 : IsProgrInter pt (type pt R) (hC.getStates Sᵢ) := by
      simp_all only [Fin.getElem_fin, UnprimedVariables.val,
        UnprimedLiterals.empty, UnprimedLiterals.inter_val, L]
      exact IsProgrInter.empty h2
    return ⟨(X, A, L), h3, h4⟩
  | S => throw <| .unexpected .StateSet Sᵢ "an intersection or progression" (toString S)

def get_regression_variables (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
    Result (UnprimedVariables' pt R × ActionIds pt)
      fun (X, A) ↦ hC.getStates Sᵢ = regression X.val.inter A.toActions ∧
        IsVariableInter pt (R.type pt) X.val.inter :=
  withErrorMessage s!"Verifying that the state set #{Sᵢ} is the regression \
    of an intersection of atomic {R} formulas" do
  let ⟨(S'ᵢ, Aᵢ), h⟩ ← (Constraint.isStateRegr C Sᵢ).verify
  have ⟨hS'ᵢ, hAᵢ⟩ : S'ᵢ < Sᵢ ∧ Aᵢ < C.actions.size := by
    have := hC.validStates Sᵢ
    simp_all [Certificate.validStateSetExpr]
  let ⟨X, h1, h2⟩ ← hC.get_inter_variables R ⟨S'ᵢ, by omega⟩
  let A := hC.getActionIds ⟨Aᵢ, by omega⟩
  have h3 : hC.getStates Sᵢ = regression X.val.inter A.toActions := by
    rw [hC.getStatesRegr Sᵢ ⟨S'ᵢ, by omega⟩ ⟨Aᵢ, by omega⟩ (by simp_all)]
    simp only [h1, getActions_eq, A]
  return ⟨(X, A), h3, by simp_all⟩

-- TODO : catch errors
def get_regression_inter (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
    Result (UnprimedVariables' pt R × ActionIds pt × UnprimedLiterals' pt R)
      fun (X, A, L) ↦ hC.getStates Sᵢ = regression X.val.inter A.toActions ∩ L.val.inter ∧
        IsRegrInter pt (R.type pt) (hC.getStates Sᵢ) :=
  withErrorMessage s!"Verifying that the state set #{Sᵢ} is the intersection of the regression \
    of an intersection of atomic {R} formulas and the intersection of {R} literals" <|
  match heq : C.states[Sᵢ] with
  | .inter S'ᵢ S''ᵢ => do
    have ⟨hS'ᵢ, hS''ᵢ⟩ : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    let ⟨(X, A), h1, h2⟩ ← hC.get_regression_variables R ⟨S'ᵢ, by omega⟩
    let ⟨L, h3, h4⟩ ← hC.get_inter_literals R ⟨S''ᵢ, by omega⟩
    have h5 : hC.getStates Sᵢ = regression X.val.inter A.toActions ∩ L.val.inter  := by
      rw [← h1, ← h3]
      exact hC.getStatesInter Sᵢ ⟨S'ᵢ, by omega⟩ ⟨S''ᵢ, by omega⟩ (by simp_all)
    have h6 : IsRegrInter pt (R.type pt) (hC.getStates Sᵢ) := by
      simp_all only
      exact IsRegrInter.inter h2 h4
    return ⟨(X, A, L), h5, h6⟩
  | .regr S'ᵢ Aᵢ => do
    let ⟨(X, A), h1, h2⟩ ← hC.get_regression_variables R Sᵢ
    let L := UnprimedLiterals.empty
    have h3 : hC.getStates Sᵢ = regression X.val.inter A.toActions ∩ L.val.inter := by
      simp_all [L, UnprimedVariables.val]
    have h4 : IsRegrInter pt (type pt R) (hC.getStates Sᵢ) := by
      simp_all only [Fin.getElem_fin, UnprimedVariables.val,
        UnprimedLiterals.empty, UnprimedLiterals.inter_val, L]
      exact IsRegrInter.empty h2
    return ⟨(X, A, L), h3, h4⟩
  | S => throw <| .unexpected .StateSet Sᵢ "an intersection or regression" (toString S)

end Certificate.validSets

namespace Formalism
open Formula Variables

-- TODO : combine verification and correctness as done for check_variable_subset/checkB4?

def check_variables_subset1 {R} [F : Formalism pt R]
    [h1 : SententialEntailment (2 * n) R]
    [h2 : BoundedConjuction (2 * n) R] [Top (2 * n) R]
    [h3 : BoundedDisjunction (2 * n) R] [Bot (2 * n) R]
    (X1 : Variables pt R) (X2 : UnprimedVariables pt R) : Bool :=
  h1.entails (h2.andList X1) (h3.orList X2)

lemma check_variables_subset1_correct {R} [F : Formalism pt R]
    [h1 : SententialEntailment (2 * n) R]
    [h2 : BoundedConjuction (2 * n) R] [Top (2 * n) R]
    [h3 : BoundedDisjunction (2 * n) R] [Bot (2 * n) R]
    (X1 : Variables pt R) (X2 : UnprimedVariables pt R) :
    check_variables_subset1 X1 X2 ↔ X1.inter ⊆ X2.val.union := by
  rw [UnprimedVariables.inter_subset_union_iff_models]
  simp [check_variables_subset1, Variable.models,
    h1.entails_iff, h2.models_andList, h3.models_orList]

def check_variables_subset2 {R} [F : Formalism pt R]
    [h1 : ClausalEntailment (2 * n) R]
    [h2 : BoundedConjuction (2 * n) R] [Top (2 * n) R]
    [h3 : ToCNF (2 * n) R]
    (X1 : Variables pt R) (X2 : UnprimedVariables pt R) : Bool :=
  let x1 := h2.andList X1
  let φ := h3.disjunctionToCNF X2
  φ.all (fun γ ↦ h1.entails x1 γ)

lemma check_variables_subset2_correct {R} [F : Formalism pt R]
    [h1 : ClausalEntailment (2 * n) R]
    [h2 : BoundedConjuction (2 * n) R] [Top (2 * n) R]
    [h3 : ToCNF (2 * n) R]
    (X1 : Variables pt R) (X2 : UnprimedVariables pt R) :
    check_variables_subset2 X1 X2 ↔ X1.inter ⊆ X2.val.union := by
  rw [UnprimedVariables.inter_subset_union_iff_models]
  simp [check_variables_subset2, Variable.models,
    h1.entails_iff, h2.models_andList, h3.models_disjunctionToCNF]

def check_variables_subset3 {R} [F : Formalism pt R]
    [h1 : Implicant (2 * n) R]
    [h2 : BoundedDisjunction (2 * n) R] [Bot (2 * n) R]
    [h3 : ToDNF (2 * n) R]
    (X1 : Variables pt R) (X2 : UnprimedVariables pt R) : Bool :=
  let x2 := h2.orList X2
  let φ := h3.conjunctionToDNF X1
  φ.all (fun δ ↦ h1.entails δ x2)

lemma check_variables_subset3_correct {R} [F : Formalism pt R]
    [h1 : Implicant (2 * n) R]
    [h2 : BoundedDisjunction (2 * n) R] [Bot (2 * n) R]
    [h3 : ToDNF (2 * n) R]
    (X1 : Variables pt R) (X2 : UnprimedVariables pt R) :
    check_variables_subset3 X1 X2 ↔ X1.inter ⊆ X2.val.union := by
  rw [UnprimedVariables.inter_subset_union_iff_models]
  simp [check_variables_subset3, Variable.models,
    h1.entails_iff, h2.models_orList, h3.models_conjunctionToDnF]

def check_variable_subset_pos_pos_1 {R1 R2} [Formalism pt R1] [Formalism pt R2]
    [h1 : ToDNF (2 * n) R1]
    [h2 : Implicant (2 * n) R2]
    (x1 : UnprimedVariable pt R1) (x2 : UnprimedVariable pt R2) (e : Error) :
    ResultProp (x1.val.toStates ⊆ x2.val.toStates) :=
  if h : (h1.toDNF x1).all fun δ ↦ h2.entails δ x2 then
    have h' : x1.val.toStates ⊆ x2.val.toStates := by
      have h3 := UnprimedLiteral.subset_states_iff_subset_models (.pos x1) (.pos x2)
      simp at h3
      simp_all only [List.all_eq_true, h2.entails_iff, DNF.exists_iff_models_subset,
        h1.models_toDNF, Variable.models]
    return ⟨(), h'⟩
  else
    throw e

def check_variable_subset_pos_pos_2 {R1 R2} [Formalism pt R1] [Formalism pt R2]
    [h1 : ClausalEntailment (2 * n) R1]
    [h2 : ToCNF (2 * n) R2]
    (x1 : UnprimedVariable pt R1) (x2 : UnprimedVariable pt R2) (e : Error) :
    ResultProp (x1.val.toStates ⊆ x2.val.toStates) :=
  if h : (h2.toCNF x2).all fun γ ↦ h1.entails x1 γ then
    have h' : x1.val.toStates ⊆ x2.val.toStates := by
      have h3 := UnprimedLiteral.subset_states_iff_subset_models (.pos x1) (.pos x2)
      simp at h3
      simp_all [h1.entails_iff, h2.models_toCNF, Variable.models]
    return ⟨(), h'⟩
  else
    throw e

def check_variable_subset_pos_neg_1 {R1 R2} [Formalism pt R1] [Formalism pt R2]
    [h1 : ToDNF (2 * n) R1]
    [h2 : ClausalEntailment (2 * n) R2]
    (x1 : UnprimedVariable pt R1) (x2 : UnprimedVariable pt R2) (e : Error) :
    ResultProp (x1.val.toStates ⊆ x2.val.toStatesᶜ) :=
  if h : (h1.negToCNF x1).all fun γ ↦ h2.entails x2 γ then
    have h' : x1.val.toStates ⊆ x2.val.toStatesᶜ := by
      have h3 := UnprimedLiteral.subset_states_iff_subset_models (.pos x1) (.neg x2)
      simp at h3
      simp_all only [List.all_eq_true, h2.entails_iff, CNF.forall_iff_subset_models,
        h1.models_negToCNF, Variable.models]
      grind only [= Set.subset_def, = Set.mem_compl_iff]
    return ⟨(), h'⟩
  else
    throw e

def check_variable_subset_pos_neg_2 {R1 R2} [Formalism pt R1] [Formalism pt R2]
    [h1 : ClausalEntailment (2 * n) R1]
    [h2 : ToDNF (2 * n) R2]
    (x1 : UnprimedVariable pt R1) (x2 : UnprimedVariable pt R2) (e : Error) :
    ResultProp (x1.val.toStates ⊆ x2.val.toStatesᶜ) := do
  let ⟨(), h⟩ ← check_variable_subset_pos_neg_1 x2 x1 e
  return ⟨(), by grind⟩

def check_variable_subset_neg_pos_1 {R1 R2} [Formalism pt R1] [Formalism pt R2]
    [h1 : ToCNF (2 * n) R1]
    [h2 : Implicant (2 * n) R2]
    (x1 : UnprimedVariable pt R1) (x2 : UnprimedVariable pt R2) (e : Error) :
    ResultProp (x1.val.toStatesᶜ ⊆ x2.val.toStates) :=
  if h : (h1.negToDNF x1).all fun δ ↦ h2.entails δ x2 then
    have h' : x1.val.toStatesᶜ ⊆ x2.val.toStates := by
      have h3 := UnprimedLiteral.subset_states_iff_subset_models (.neg x1) (.pos x2)
      simp at h3
      simp_all [Variable.models, h2.entails_iff, h1.models_negToDNF]
    return ⟨(), h'⟩
  else
    throw e

def check_variable_subset_neg_pos_2 {R1 R2} [Formalism pt R1] [Formalism pt R2]
    [h1 : Implicant (2 * n) R1]
    [h2 : ToCNF (2 * n) R2]
    (x1 : UnprimedVariable pt R1) (x2 : UnprimedVariable pt R2) (e : Error) :
    ResultProp (x1.val.toStatesᶜ ⊆ x2.val.toStates) := do
  let ⟨(), h⟩ ← check_variable_subset_neg_pos_1 x2 x1 e
  return ⟨(), by grind⟩

end Formalism

namespace StateSetFormalism

def check_variables_subset (R : StateSetFormalism)
    (X1 : Variables' pt R) (X2 : UnprimedVariables' pt R) : Bool :=
  match R with
  | .bdd => check_variables_subset1 X1 X2
  | .horn => check_variables_subset2 X1 X2
  | .mods => check_variables_subset2 X1 X2

lemma check_variables_subset_correct (R : StateSetFormalism)
    (X1 : Variables' pt R) (X2 : UnprimedVariables' pt R) :
    check_variables_subset R X1 X2 ↔ X1.inter ⊆ X2.val.union :=
  match R with
  | .bdd => check_variables_subset1_correct X1 X2
  | .horn => check_variables_subset2_correct X1 X2
  | .mods => check_variables_subset2_correct X1 X2

def checkB1 R (L1 L2 : UnprimedLiterals' pt R) : Bool :=
  R.check_variables_subset (L1.1 ++ L2.2).val (L2.1 ++ L1.2)

lemma checkB1_correct R {L1 L2 : UnprimedLiterals' pt R} :
    checkB1 R L1 L2 ↔ L1.val.inter ⊆ L2.val.union := by
  simp [checkB1, check_variables_subset_correct, Set.inter_compl_subset_union_compl]

def preVariable R (aᵢ : Fin pt.actions'.length) : UnprimedVariable' pt R :=
  UnprimedVariable.ofVarSet (R.type pt) pt.actions'[aᵢ].pre

@[simp]
lemma mem_toStates_preVariable {R} {aᵢ : Fin pt.actions'.length} {s} :
    s ∈ (preVariable R aᵢ).val.toStates ↔ ∀ i ∈ pt.actions'[aᵢ].pre, i ∈ s  := by
  obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
  grind only [Variable.toStates_eq, preVariable, Set.mem_image,
    UnprimedVariable.mem_models_ofVarSet]

def addVariable R (aᵢ : Fin pt.actions'.length) : UnprimedVariable' pt R :=
  UnprimedVariable.ofVarSet (R.type pt) pt.actions'[aᵢ].add

@[simp]
lemma mem_toStates_addVariable {R} {aᵢ : Fin pt.actions'.length} {s} :
    s ∈ (addVariable R aᵢ).val.toStates ↔ ∀ i ∈ pt.actions'[aᵢ].add, i ∈ s := by
  obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
  grind only [Variable.toStates_eq, addVariable, = Set.mem_image,
    UnprimedVariable.mem_models_ofVarSet]

-- Only return deleting effects that are not adding effects
def delVariable R (aᵢ : Fin pt.actions'.length) : UnprimedVariable' pt R :=
  let vars := pt.actions'[aᵢ].del \ pt.actions'[aᵢ].add
  UnprimedVariable.ofVarSet (R.type pt) vars false

@[simp]
lemma mem_toStates_delVariable {R} {aᵢ : Fin pt.actions'.length} {s} :
    s ∈ (delVariable R aᵢ).val.toStates ↔
    ∀ i ∈ pt.actions'[aᵢ].del, i ∈ pt.actions'[aᵢ].add ∨ i ∉ s := by
  obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
  grind only [delVariable, Variable.toStates_eq, Set.mem_image,
    UnprimedVariable.mem_models_ofVarSet, VarSet.mem_diff]

def preVariables R (aᵢ : Fin pt.actions'.length) : UnprimedVariables' pt R :=
  [preVariable R aᵢ]

@[simp]
lemma mem_preVariables {R} {aᵢ : Fin pt.actions'.length} {x} :
    x ∈ (preVariables R aᵢ) ↔ x = preVariable R aᵢ := by
  simp only [preVariables, List.mem_cons, List.not_mem_nil, or_false]

def effectVariables R (aᵢ : Fin pt.actions'.length) : UnprimedVariables' pt R :=
  [addVariable R aᵢ, delVariable R aᵢ]

@[simp]
lemma mem_effectVariables {R} {aᵢ : Fin pt.actions'.length} {x} :
    x ∈ (effectVariables R aᵢ) ↔ x = addVariable R aᵢ ∨ x = delVariable R aᵢ := by
  simp only [effectVariables, List.mem_cons, List.not_mem_nil, or_false]

def effectVarSet (aᵢ : Fin pt.actions'.length) : VarSet n :=
  pt.actions'[aᵢ].add ∪ pt.actions'[aᵢ].del

@[simp]
lemma mem_effectVarSet {aᵢ : Fin pt.actions'.length} {i} :
    i ∈ effectVarSet aᵢ ↔ i ∈ pt.actions'[aᵢ].add ∨ i ∈ pt.actions'[aᵢ].del := by
  simp [effectVarSet, VarSet.mem_union]

def checkB2' R (aᵢ : Fin pt.actions'.length) (X0 X1 X2 : UnprimedVariables' pt R) : Bool :=
  let X0' := UnprimedVariables.toPrimed (preVariables R aᵢ ++ X0) (effectVarSet aᵢ)
  let X1' := X0' ++ (effectVariables R aᵢ ++ X1).val
  R.check_variables_subset X1' X2

lemma checkB2'_correct {R aᵢ} {X0 X1 X2 : UnprimedVariables' pt R} :
    checkB2' R aᵢ X0 X1 X2 ↔
    progression' X0.val.inter pt.actions'[aᵢ] ∩ X1.val.inter ⊆ X2.val.union := by
  let X0' := UnprimedVariables.toPrimed (preVariables R aᵢ ++ X0) (effectVarSet aᵢ)
  let X := X0' ++ (effectVariables R aᵢ).val
  suffices h : X.inter = progression' X0.val.inter pt.actions'[aᵢ] by
    simp [X, X0'] at h
    simp [checkB2', check_variables_subset_correct, ← Set.inter_assoc, h]
  ext s
  simp only [Fin.getElem_fin, mem_progression', UnprimedVariables.mem_inter, Successor,
    Applicable, Set.subset_def, SetLike.mem_coe, Set.ext_iff, Set.mem_union, Set.mem_sdiff]
  simp only [UnprimedVariables.inter_variables_append, Set.mem_inter_iff,
    UnprimedVariables.mem_inter_toPrimed, UnprimedVariables.inter_append,
    UnprimedVariables.mem_inter, mem_preVariables, forall_eq, mem_toStates_preVariable,
    mem_effectVarSet, not_or, and_imp, mem_effectVariables, forall_eq_or_imp,
    mem_toStates_addVariable, mem_toStates_delVariable, X, X0', Fin.getElem_fin]
  constructor
  · rintro ⟨⟨s', ⟨h1, h2⟩, h3⟩, h4, h5⟩
    use s'
    grind only
  · rintro ⟨s', h1, h2, h3⟩
    constructor
    · use s'
      grind only [usr Fin.isLt]
    · grind only [usr Fin.isLt]

def checkB2 R
    (X : UnprimedVariables' pt R) (A : ActionIds pt) (L1 L2 : UnprimedLiterals' pt R) : Bool :=
  A.all (fun aᵢ ↦ checkB2' R aᵢ X (L1.1 ++ L2.2) (L2.1 ++ L1.2))

lemma checkB2_correct {R X A} {L1 L2 : UnprimedLiterals' pt R} :
    checkB2 R X A L1 L2 ↔ progression X.val.inter A.toActions ∩ L1.val.inter ⊆ L2.val.union := by
  simp [checkB2, checkB2'_correct, ← Set.inter_assoc]
  simp [progression]
  grind

def checkB3' R (aᵢ : Fin pt.actions'.length) (X0 X1 X2 : UnprimedVariables' pt R) : Bool :=
  let X0' := UnprimedVariables.toPrimed ( effectVariables R aᵢ ++ X0) (effectVarSet aᵢ)
  let X1' := X0' ++ (preVariables R aᵢ ++ X1).val
  R.check_variables_subset X1' X2

lemma checkB3'_correct {R aᵢ} {X0 X1 X2 : UnprimedVariables' pt R} :
    checkB3' R aᵢ X0 X1 X2 ↔
    regression' X0.val.inter pt.actions'[aᵢ] ∩ X1.val.inter ⊆ X2.val.union := by
  let X0' := UnprimedVariables.toPrimed ( effectVariables R aᵢ ++ X0) (effectVarSet aᵢ)
  let X := X0' ++ (preVariables R aᵢ).val
  suffices h : X.inter = regression' X0.val.inter pt.actions'[aᵢ] by
    simp [X, X0'] at h
    simp [checkB3', check_variables_subset_correct, ← Set.inter_assoc, h]
  ext s
  simp only [Fin.getElem_fin, mem_regression', UnprimedVariables.mem_inter, Successor,
    Applicable, Set.subset_def, SetLike.mem_coe, Set.ext_iff, Set.mem_union, Set.mem_sdiff]
  simp only [UnprimedVariables.inter_variables_append, Set.mem_inter_iff,
    UnprimedVariables.mem_inter_toPrimed, UnprimedVariables.inter_append,
    UnprimedVariables.mem_inter, mem_effectVariables, forall_eq_or_imp, mem_toStates_addVariable,
    Fin.getElem_fin, forall_eq, mem_toStates_delVariable, mem_effectVarSet, not_or, and_imp,
    mem_preVariables, mem_toStates_preVariable, X, X0']
  constructor
  · rintro ⟨⟨s', h1⟩, h2⟩
    use s'
    grind only
  · rintro ⟨s', h1⟩
    constructor
    · use s'
      grind only
    · grind only

def checkB3 R
    (X : UnprimedVariables' pt R) (A : ActionIds pt) (L1 L2 : UnprimedLiterals' pt R) : Bool :=
  A.all (fun aᵢ ↦ checkB3' R aᵢ X (L1.1 ++ L2.2) (L2.1 ++ L1.2))

lemma checkB3_correct {R X A} {L1 L2 : UnprimedLiterals' pt R} :
    checkB3 R X A L1 L2 ↔ regression X.val.inter A.toActions ∩ L1.val.inter ⊆ L2.val.union := by
  simp [checkB3, checkB3'_correct, regression, ← Set.inter_assoc]
  grind

/--
Check whether the stateset corresponding to `l1` is a subset of the stateset corresponding to`l2`.
`e` is the error that should be thrown if `l1` is not a subset of `l2`.
-/
def checkB4 R1 R2 (l1 : UnprimedLiteral' pt R1) (l2 : UnprimedLiteral' pt R2) (e : Error):
    ResultProp (l1.val.toStates ⊆ l2.val.toStates) :=
  if h1 : R1 == R2 then
    if h2 : checkB1 R1 (.single l1) (.single (beq_iff_eq.1 h1 ▸ l2)) then
      return ⟨(), by simp_all [checkB1_correct]; grind only⟩
    else throw e
  else
    match l1, l2 with
    | .pos v1, .pos v2 =>
      match R1, R2 with
      | mods, _ => check_variable_subset_pos_pos_1 v1 v2 e
      | _, mods => check_variable_subset_pos_pos_2 v1 v2 e
      | bdd, horn => check_variable_subset_pos_pos_2 v1 v2 e
      | _, _ => throw <| .unsupportedB4 R1 R2
    | .pos v1, .neg v2 =>
      match R1, R2 with
      | mods, _ => check_variable_subset_pos_neg_1 v1 v2 e
      | _, mods => check_variable_subset_pos_neg_2 v1 v2 e
      | _, _ => throw <| .unsupportedB4 R1 R2
    | .neg v1, .pos v2 =>
      match R1, R2 with
      | mods, _ => check_variable_subset_neg_pos_1 v1 v2 e
      | _, mods => check_variable_subset_neg_pos_2 v1 v2 e
      | bdd, horn => check_variable_subset_neg_pos_2 v1 v2 e
      | horn, bdd => check_variable_subset_neg_pos_1 v1 v2 e
      | _, _ => throw <| .unsupportedB4 R1 R2
    | .neg v1, .neg v2 => do
      let ⟨(), h2⟩ ← checkB4 R2 R1 (.pos v2) (.pos v1) e
      return ⟨(), by simp_all [UnprimedLiteral.val, Literal.toStates_neg]⟩
    termination_by
      match l1, l2 with
      | .neg x1, .neg x2 => 1
      | _, _ => 0

end StateSetFormalism

-- TODO : Combine B1 - B3?
public def constraintB1 (hC : C.validSets) (S1ᵢ S2ᵢ : ℕ) : Constraint Unit where

  prop := fun _ ↦ ∃ hS1ᵢ hS2ᵢ,
    have R := hC.getFormalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
    IsLiteralInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩

  verify' :=
    do
      let ⟨⟨⟩, hS1ᵢ⟩ ← (stateBounds' C S1ᵢ).verify
      let ⟨⟨⟩, hS2ᵢ⟩ ← (stateBounds' C S2ᵢ).verify
      let S1ᵢ : Fin C.states.size := ⟨S1ᵢ, by simp_all only [stateBounds'.prop_eq]⟩
      let S2ᵢ : Fin C.states.size := ⟨S2ᵢ, by simp_all only [stateBounds'.prop_eq]⟩
      let R := hC.getFormalism [S1ᵢ, S2ᵢ]
      let ⟨L1, h1, h2⟩ ← hC.get_inter_literals R S1ᵢ
      let ⟨L2, h3, h4⟩ ← hC.get_union_literals R S2ᵢ
      if h5 : R.checkB1 L1 L2 then
        have h6 : hC.getStates S1ᵢ ⊆ hC.getStates S2ᵢ := by
          simp_all only [checkB1_correct]
        return ⟨(), by use S1ᵢ.prop, S2ᵢ.prop, h2, h4, h6⟩
      else
        throw <| .notSubset .StateSet S1ᵢ S2ᵢ

  elimExists := elimExists0

@[simp]
public lemma constraintB1.prop_eq {C : Certificate pt} {hC : C.validSets} {S1ᵢ S2ᵢ : ℕ} {a} :
    (constraintB1 hC S1ᵢ S2ᵢ).prop a ↔
      S1ᵢ < C.states.size ∧ S2ᵢ < C.states.size ∧ ∃ hS1ᵢ hS2ᵢ,
      have R := hC.getFormalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
      IsLiteralInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
      IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
      hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ := by
  simp [constraintB1]
  tauto

public def constraintB2 (hC : C.validSets) (S1ᵢ S2ᵢ : ℕ) : Constraint Unit where

  prop := fun () ↦ ∃ hS1ᵢ hS2ᵢ,
    have R := hC.getFormalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
    IsProgrInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩

  verify' := do
    let ⟨⟨⟩, hS1ᵢ⟩ ← (stateBounds' C S1ᵢ).verify
    let ⟨⟨⟩, hS2ᵢ⟩ ← (stateBounds' C S2ᵢ).verify
    let S1ᵢ : Fin C.states.size := ⟨S1ᵢ, by simp_all only [stateBounds'.prop_eq]⟩
    let S2ᵢ : Fin C.states.size := ⟨S2ᵢ, by simp_all only [stateBounds'.prop_eq]⟩
    let R := hC.getFormalism [S1ᵢ, S2ᵢ]
    let ⟨(X, A, L1), h1, h2⟩ ← hC.get_progression_inter R S1ᵢ
    let ⟨L2, h3, h4⟩ ← hC.get_union_literals R S2ᵢ
    if h5 : R.checkB2 X A L1 L2 then
      have h6 : hC.getStates S1ᵢ ⊆ hC.getStates S2ᵢ := by
        simp_all only [checkB2_correct]
      return ⟨(), by use S1ᵢ.prop, S2ᵢ.prop, h2, h4, h6⟩
    else
      throw <| .notSubset .StateSet S1ᵢ S2ᵢ

  elimExists := elimExists0

@[simp]
public lemma constraintB2.prop_eq {C : Certificate pt} {hC : C.validSets} {S1ᵢ S2ᵢ : ℕ} {a} :
  (constraintB2 hC S1ᵢ S2ᵢ).prop a ↔
    S1ᵢ < C.states.size ∧ S2ᵢ < C.states.size ∧ ∃ hS1ᵢ hS2ᵢ,
    have R := hC.getFormalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
    IsProgrInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ := by
  simp [constraintB2]
  tauto

public def constraintB3 (hC : C.validSets) (S1ᵢ S2ᵢ : ℕ) : Constraint Unit where
  prop := fun () ↦ ∃ hS1ᵢ hS2ᵢ,
    have R := hC.getFormalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
    IsRegrInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩

  verify' := do
    let ⟨⟨⟩, hS1ᵢ⟩ ← (stateBounds' C S1ᵢ).verify
    let ⟨⟨⟩, hS2ᵢ⟩ ← (stateBounds' C S2ᵢ).verify
    let S1ᵢ : Fin C.states.size := ⟨S1ᵢ, by simp_all only [stateBounds'.prop_eq]⟩
    let S2ᵢ : Fin C.states.size := ⟨S2ᵢ, by simp_all only [stateBounds'.prop_eq]⟩
    let R := hC.getFormalism [S1ᵢ, S2ᵢ]
    let ⟨(X, A, L1), h1, h2⟩ ← hC.get_regression_inter R S1ᵢ
    let ⟨L2, h3, h4⟩ ← hC.get_union_literals R S2ᵢ
    if h5 : R.checkB3 X A L1 L2 then
      have h6 : hC.getStates S1ᵢ ⊆ hC.getStates S2ᵢ := by
        simp_all only [checkB3_correct]
      return ⟨(), by use S1ᵢ.prop, S2ᵢ.prop, h2, h4, h6⟩
    else
      throw <| .notSubset .StateSet S1ᵢ S2ᵢ

  elimExists := elimExists0

@[simp]
public lemma constraintB3.prop_eq {C : Certificate pt} {hC : C.validSets} {S1ᵢ S2ᵢ : ℕ} {a} :
    (constraintB3 hC S1ᵢ S2ᵢ).prop a ↔
      S1ᵢ < C.states.size ∧ S2ᵢ < C.states.size ∧ ∃ hS1ᵢ hS2ᵢ,
      have R := hC.getFormalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
      IsRegrInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
      IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
      hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ := by
  simp [constraintB3]
  tauto

public def constraintB4 (hC : C.validSets) (S1ᵢ S2ᵢ : ℕ) : Constraint Unit where
  prop := fun () ↦ ∃ hS1ᵢ hS2ᵢ,
    have R1 := hC.getFormalism [⟨S1ᵢ, hS1ᵢ⟩]
    have R2 := hC.getFormalism [⟨S2ᵢ, hS2ᵢ⟩]
    IsLiteral pt (R1.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteral pt (R2.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩

  verify' := do
    let ⟨⟨⟩, hS1ᵢ⟩ ← (stateBounds' C S1ᵢ).verify
    let ⟨⟨⟩, hS2ᵢ⟩ ← (stateBounds' C S2ᵢ).verify
    let S1ᵢ : Fin C.states.size := ⟨S1ᵢ, by simp_all only [stateBounds'.prop_eq]⟩
    let S2ᵢ : Fin C.states.size := ⟨S2ᵢ, by simp_all only [stateBounds'.prop_eq]⟩
    let R1 := hC.getFormalism [S1ᵢ]
    let R2 := hC.getFormalism [S2ᵢ]
    let ⟨l1, h1, h2⟩ ← hC.get_literal R1 S1ᵢ
    let ⟨l2, h3, h4⟩ ← hC.get_literal R2 S2ᵢ
    let ⟨(), h6⟩ ← R1.checkB4 R2 l1 l2 (.notSubset .StateSet S1ᵢ S2ᵢ)
    return ⟨(), by use S1ᵢ.prop, S2ᵢ.prop, h2, h4; simp_all only [S1ᵢ, S2ᵢ]⟩

  elimExists := elimExists0

@[simp]
public lemma constraintB4.prop_eq {C : Certificate pt} {hC : C.validSets} {S1ᵢ S2ᵢ : ℕ} {a} :
    (constraintB4 hC S1ᵢ S2ᵢ).prop a ↔
      S1ᵢ < C.states.size ∧ S2ᵢ < C.states.size ∧ ∃ hS1ᵢ hS2ᵢ,
      have R1 := hC.getFormalism [⟨S1ᵢ, hS1ᵢ⟩]
      have R2 := hC.getFormalism [⟨S2ᵢ, hS2ᵢ⟩]
      IsLiteral pt (R1.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
      IsLiteral pt (R2.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
      hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ := by
  simp [constraintB4]
  tauto

-- TODO : make more efficient?
public def constraintB5 {C : Certificate pt} (hC : C.validSets) (A1ᵢ A2ᵢ : ℕ) :
    Constraint Unit where
  prop := fun () ↦ ∃ hA1ᵢ hA2ᵢ, hC.getActions ⟨A1ᵢ, hA1ᵢ⟩ ⊆ hC.getActions ⟨A2ᵢ, hA2ᵢ⟩

  verify' := do
    let ⟨⟨⟩, hA1ᵢ⟩ ← (actionBounds' C A1ᵢ).verify
    let ⟨⟨⟩, hA2ᵢ⟩ ← (actionBounds' C A2ᵢ).verify
    let A1ᵢ : Fin C.actions.size := ⟨A1ᵢ, by simp_all only [actionBounds'.prop_eq]⟩
    let A2ᵢ : Fin C.actions.size := ⟨A2ᵢ, by simp_all only [actionBounds'.prop_eq]⟩
    if h : hC.getActionIds A1ᵢ ⊆ hC.getActionIds A2ᵢ then
      return ⟨(), by
        simp only [getActions_eq, Set.subset_def, ActionIds.mem_toActions, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂]
        use A1ᵢ.prop, A2ᵢ.prop
        grind⟩
    else
      throw <| .notSubset .ActionSet A1ᵢ A2ᵢ

  elimExists := elimExists0

@[simp]
public lemma constraintB5.prop_eq {C : Certificate pt} {hC : C.validSets} {A1ᵢ A2ᵢ : ℕ} {u} :
    (constraintB5 hC A1ᵢ A2ᵢ).prop u ↔ A1ᵢ < C.actions.size ∧ A2ᵢ < C.actions.size ∧
      ∃ hA1ᵢ hA2ᵢ, hC.getActions ⟨A1ᵢ, hA1ᵢ⟩ ⊆ hC.getActions ⟨A2ᵢ, hA2ᵢ⟩ := by
  simp [constraintB5]
  tauto

end Validator
