import Validator.Certificate.Constraint

namespace Validator
variable {n : ℕ} {pt : STRIPS n} {C : Certificate pt}
open Constraint Certificate.validSets
open ActionSubsetKnowledge StateSubsetKnowledge
open Formalism StateSetFormalism
open Formula (Model)

namespace Formalism
open Formula Variables

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
  check_variables_subset1 X1 X2 ↔ X1.inter ⊆ X2.val.union :=
  by
    rw [UnprimedVariables.inter_subset_union_iff_models]
    simp [check_variables_subset1, Variable.models,
      h1.entails_correct, h2.andList_correct, h3.orList_correct]

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
  check_variables_subset2 X1 X2 ↔ X1.inter ⊆ X2.val.union :=
  by
    rw [UnprimedVariables.inter_subset_union_iff_models]
    simp [check_variables_subset2, Variable.models,
      h1.entails_correct, h2.andList_correct, h3.disjunctionToCNF_correct]

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
  check_variables_subset3 X1 X2 ↔ X1.inter ⊆ X2.val.union :=
  by
    rw [UnprimedVariables.inter_subset_union_iff_models]
    simp [check_variables_subset3, Variable.models,
      h1.entails_correct, h2.orList_correct, h3.conjunctionToDnF_correct]

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

def checkB1_correct R {L1 L2 : UnprimedLiterals' pt R} :
  checkB1 R L1 L2 ↔ L1.val.inter ⊆ L2.val.union :=
  by
    simp [checkB1, check_variables_subset_correct, Set.inter_compl_subset_union_compl]

def preVariable R (a : Fin pt.actions'.length) : UnprimedVariable' pt R :=
  UnprimedVariable.ofVarset' (R.type pt) pt.actions'[a].pre'

@[simp]
lemma mem_models_preVariable {R} {a : Fin pt.actions'.length} {M} :
  M ∈ (preVariable R a).val.models ↔ pt.actions'[a].pre ⊆ M.unprimedState :=
  by
    simp [preVariable, UnprimedVariable.mem_models_ofVarSet']
    simp [Action.pre, convertVarSet, Set.subset_def]

@[simp]
lemma mem_toStates_preVariable {R} {a : Fin pt.actions'.length} {s} :
  s ∈ (preVariable R a).val.toStates ↔ pt.actions'[a].pre ⊆ s :=
  by
    obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
    simp [Variable.toStates_eq]
    grind

def addVariable R (a : Fin pt.actions'.length) : UnprimedVariable' pt R :=
  UnprimedVariable.ofVarset' (R.type pt) pt.actions'[a].add'

@[simp]
lemma mem_models_addVariable {R} {a : Fin pt.actions'.length} {M} :
  M ∈ (addVariable R a).val.models ↔ pt.actions'[a].add ⊆ M.unprimedState :=
  by
    simp [addVariable, UnprimedVariable.mem_models_ofVarSet']
    simp [Action.add, convertVarSet, Set.subset_def]

@[simp]
lemma mem_toStates_addVariable {R} {a : Fin pt.actions'.length} {s} :
  s ∈ (addVariable R a).val.toStates ↔ pt.actions'[a].add ⊆ s :=
  by
    obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
    simp [Variable.toStates_eq]
    grind

-- Only return deleting effects that are not adding effects
def delVariable R (a : Fin pt.actions'.length) : UnprimedVariable' pt R :=
  let vars := List.diff' pt.actions'[a].del'.val pt.actions'[a].add'.val
  have h : vars.Sorted (· < ·) := by
    apply List.diff'_sorted
    · exact pt.actions'[a].del'.prop
    · exact pt.actions'[a].add'.prop
  UnprimedVariable.ofVarset' (R.type pt) ⟨vars, h⟩ false

@[simp]
lemma mem_models_delVariable {R} {a : Fin pt.actions'.length} {M} :
  M ∈ (delVariable R a).val.models ↔ pt.actions'[a].del \ pt.actions'[a].add ⊆ M.unprimedStateᶜ :=
  by
    rcases a with ⟨a, ha⟩
    simp [delVariable, UnprimedVariable.mem_models_ofVarSet']
    simp [Action.del, Action.add, convertVarSet, Set.subset_def]
    simp [List.mem_diff' pt.actions'[a].del'.prop pt.actions'[a].add'.prop]

@[simp]
lemma mem_toStates_delVariable {R} {a : Fin pt.actions'.length} {s} :
  s ∈ (delVariable R a).val.toStates ↔ pt.actions'[a].del \ pt.actions'[a].add ⊆ sᶜ :=
  by
    obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
    simp [Variable.toStates_eq]
    grind

def preVariables R (a : Fin pt.actions'.length) : UnprimedVariables' pt R :=
  [preVariable R a]

@[simp]
lemma mem_preVariables {R} {a : Fin pt.actions'.length} {x} :
  x ∈ (preVariables R a) ↔ x = preVariable R a:=
  by
    simp [preVariables]

def effectVariables R (a : Fin pt.actions'.length) : UnprimedVariables' pt R :=
  [addVariable R a, delVariable R a]

@[simp]
lemma mem_effectVariables {R} {a : Fin pt.actions'.length} {x} :
  x ∈ (effectVariables R a) ↔ x = addVariable R a ∨ x = delVariable R a :=
  by
    simp [effectVariables]

def effectVarSet' (a : Fin pt.actions'.length) : VarSet' n :=
  VarSet'.union pt.actions'[a].add' pt.actions'[a].del'

@[simp]
lemma mem_effectVarSet' {a : Fin pt.actions'.length} {i} :
  i ∈ (effectVarSet' a).val ↔ i ∈ pt.actions'[a].add ∨ i ∈ pt.actions'[a].del :=
  by
    simp [effectVarSet', VarSet'.union, List.mem_mergeDedup]
    simp [Action.add, Action.del, convertVarSet]

def checkB2' R (a : Fin pt.actions'.length) (X0 X1 X2 : UnprimedVariables' pt R) : Bool :=
  let X0' := UnprimedVariables.toPrimed (preVariables R a ++ X0) (effectVarSet' a)
  let X1' := X0' ++ (effectVariables R a ++ X1).val
  R.check_variables_subset X1' X2

lemma checkB2'_correct {R a} {X0 X1 X2 : UnprimedVariables' pt R} :
  checkB2' R a X0 X1 X2 ↔
    pt.progression' X0.val.inter pt.actions'[a] ∩ X1.val.inter ⊆ X2.val.union :=
  by
    let X0' := UnprimedVariables.toPrimed (preVariables R a ++ X0) (effectVarSet' a)
    let X := X0' ++ (effectVariables R a).val
    suffices h : X.inter = pt.progression' X0.val.inter pt.actions'[a] by
      simp [X, X0'] at h
      simp [checkB2', check_variables_subset_correct, ← Set.inter_assoc, h]
    ext s
    simp [STRIPS.progression', Successor, Applicable]
    simp [X, X0', UnprimedVariables.mem_inter_toPrimed]
    constructor
    · rintro ⟨⟨s', ⟨h1, h2⟩, h3⟩, h4, h5⟩
      have : s = s' \ pt.actions'[a].del ∪ pt.actions'[a].add := by
        simp [Set.subset_compl_iff_disjoint_left] at h5
        have h6 := Disjoint.notMem_of_mem_left h5
        grind
      grind
    · grind

def checkB2 R
  (X : UnprimedVariables' pt R) (A : ActionIds pt) (L1 L2 : UnprimedLiterals' pt R) : Bool :=
    A.all (fun a ↦ checkB2' R a X (L1.1 ++ L2.2) (L2.1 ++ L1.2))

def checkB2_correct {R X A} {L1 L2 : UnprimedLiterals' pt R} :
 checkB2 R X A L1 L2 ↔ pt.progression X.val.inter A.toActions ∩ L1.val.inter ⊆ L2.val.union :=
  by
    simp [checkB2, checkB2'_correct, STRIPS.progression, ← Set.inter_assoc]
    grind

def checkB3' R (a : Fin pt.actions'.length) (X0 X1 X2 : UnprimedVariables' pt R) : Bool :=
  let X0' := UnprimedVariables.toPrimed ( effectVariables R a ++ X0) (effectVarSet' a)
  let X1' := X0' ++ (preVariables R a ++ X1).val
  R.check_variables_subset X1' X2

lemma checkB3'_correct {R a} {X0 X1 X2 : UnprimedVariables' pt R} :
  checkB3' R a X0 X1 X2 ↔
    pt.regression' X0.val.inter pt.actions'[a] ∩ X1.val.inter ⊆ X2.val.union :=
  by
    let X0' := UnprimedVariables.toPrimed ( effectVariables R a ++ X0) (effectVarSet' a)
    let X := X0' ++ (preVariables R a).val
    suffices h : X.inter = pt.regression' X0.val.inter pt.actions'[a] by
      simp [X, X0'] at h
      simp [checkB3', check_variables_subset_correct, ← Set.inter_assoc, h]
    ext s
    simp [STRIPS.regression', Successor, Applicable]
    simp [X, X0', UnprimedVariables.mem_inter_toPrimed]
    intro h1
    constructor
    · rintro ⟨s', ⟨h2, h3⟩, h4⟩ x h5 h6
      have : s' = s \ pt.actions'[a].del ∪ pt.actions'[a].add := by
        simp [Set.subset_compl_iff_disjoint_left] at h2
        have h7 := Disjoint.notMem_of_mem_left h2.2
        grind
      grind
    · intro h1
      use s \ pt.actions'[a].del ∪ pt.actions'[a].add
      simp [Set.compl_diff]
      grind

def checkB3 R
  (X : UnprimedVariables' pt R) (A : ActionIds pt) (L1 L2 : UnprimedLiterals' pt R) : Bool :=
    A.all (fun a ↦ checkB3' R a X (L1.1 ++ L2.2) (L2.1 ++ L1.2))

def checkB3_correct {R X A} {L1 L2 : UnprimedLiterals' pt R} :
 checkB3 R X A L1 L2 ↔ pt.regression X.val.inter A.toActions ∩ L1.val.inter ⊆ L2.val.union :=
  by
    simp [checkB3, checkB3'_correct, STRIPS.regression, ← Set.inter_assoc]
    grind

def checkB4 R1 R2 (l1 : UnprimedLiteral' pt R1) (l2 : UnprimedLiteral' pt R2) : Bool :=
    sorry

def checkB4_correct {R1 R2} {l1 : UnprimedLiteral' pt R1} {l2 : UnprimedLiteral' pt R2} :
 checkB4 R1 R2 l1 l2 ↔ l1.val.toStates ⊆ l2.val.toStates :=
  by
    sorry

end StateSetFormalism

namespace Certificate.validSets
open StateSetFormalism

/-- Returns none if the formula is constant -/
def get_formalism' (hC : C.validSets) (Sᵢ : Fin C.states.size) : Option StateSetFormalism :=
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
    hC.get_formalism' ⟨S'ᵢ, by omega⟩
  | .inter S'ᵢ S''ᵢ =>
    have : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    match hC.get_formalism' ⟨S'ᵢ, by omega⟩ with
    | none => hC.get_formalism' ⟨S''ᵢ, by omega⟩
    | R => R
  | .union S'ᵢ S''ᵢ =>
    have : S'ᵢ < Sᵢ ∧ S''ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    match hC.get_formalism' ⟨S'ᵢ, by omega⟩ with
    | none => hC.get_formalism' ⟨S''ᵢ, by omega⟩
    | R => R
  | .progr S'ᵢ _ =>
    have : S'ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    hC.get_formalism' ⟨S'ᵢ, by omega⟩
  | .regr S'ᵢ _ =>
    have : S'ᵢ < Sᵢ := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    hC.get_formalism' ⟨S'ᵢ, by omega⟩


def get_formalism (hC : C.validSets) : List (Fin C.states.size) → StateSetFormalism
| [] => mods -- Fallback if all sets are constant
| Sᵢ :: tail =>
  match hC.get_formalism' Sᵢ with
  | none => hC.get_formalism tail
  | some F => F

def throwIncompatibleFormalism {α : outParam Type} {p}
  (R R' : StateSetFormalism) (Sᵢ : ℕ) : Result α p :=
  throwUnvalid s!"The state set expression #{Sᵢ} is expected \
   to be a {R} formula, but it is a {R'} formula"

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
    have h1 : hC.getStates Sᵢ = pt.goal_states :=
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
    throwUnvalid s!"Expected the state set #{Sᵢ} to be a constant state set or \
      an atomic {R} formula, but it is {S}."

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
    let l : UnprimedLiteral' pt R := (x, false)
    have h3 : hC.getStates Sᵢ = l.val.toStates := by
      simp [l, UnprimedLiteral.val, Literal.toStates]
      rw [← h1]
      exact hC.getStatesNeg Sᵢ ⟨S'ᵢ, by omega⟩ (by simp_all)
    have h4 : IsLiteral pt (type pt R) (hC.getStates Sᵢ) := by
      simp_all only
      exact IsLiteral.neg h2
    return ⟨l, h3, h4⟩
  | _ => do
    let ⟨x, h1, h2⟩ ← hC.get_variable R ⟨Sᵢ, by omega⟩
    have h3 : hC.getStates Sᵢ = x.val.toStates := by
      simp_all
    have h4 : IsLiteral pt (type pt R) (hC.getStates Sᵢ) := by
      rw [h3] at ⊢ h2
      exact IsLiteral.pos h2
    return ⟨(x, true), h3, h4⟩

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
    return ⟨UnprimedLiterals.single l, by simp_all; exact IsLiteralUnion.single h2⟩

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
      simp_all [-Finset.inter_assoc]
      exact IsLiteralInter.inter h2 h4
    return ⟨(L1 ++ L2), h5, h6⟩
  | _ => do
    let ⟨l, h1, h2⟩ ← hC.get_literal R ⟨Sᵢ, by omega⟩
    return ⟨UnprimedLiterals.single l, by simp_all; exact IsLiteralInter.single h2⟩

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
    return ⟨UnprimedVariables.single x, by simp_all; exact IsVariableInter.single h2⟩

def get_progression_variables (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
  Result (UnprimedVariables' pt R × ActionIds pt)
    fun (X, A) ↦ hC.getStates Sᵢ = pt.progression X.val.inter A.toActions ∧
      IsVariableInter pt (R.type pt) X.val.inter :=
  withErrorMessage s!"Verifying that the state set #{Sᵢ} is the progression \
    of an intersection of atomic {R} formulas"
  do
    let ⟨(S'ᵢ, Aᵢ), h⟩ ← (Constraint.isStateProgr C Sᵢ).verify
    have ⟨hS'ᵢ, hAᵢ⟩ : S'ᵢ < Sᵢ ∧ Aᵢ < C.actions.size := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    let ⟨X, h1, h2⟩ ← hC.get_inter_variables R ⟨S'ᵢ, by omega⟩
    let A := hC.getActions' ⟨Aᵢ, by omega⟩
    have h3 : hC.getStates Sᵢ = pt.progression X.val.inter A.toActions := by
      rw [← h1]
      exact hC.getStatesProg Sᵢ ⟨S'ᵢ, by omega⟩ ⟨Aᵢ, by omega⟩ (by simp_all)
    return ⟨(X, A), h3, by simp_all⟩

def get_progression_inter (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
  Result (UnprimedVariables' pt R × ActionIds pt × UnprimedLiterals' pt R)
    fun (X, A, L) ↦ hC.getStates Sᵢ = pt.progression X.val.inter A.toActions ∩ L.val.inter ∧
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
    have h5 : hC.getStates Sᵢ = pt.progression X.val.inter A.toActions ∩ L.val.inter  := by
      rw [← h1, ← h3]
      exact hC.getStatesInter Sᵢ ⟨S'ᵢ, by omega⟩ ⟨S''ᵢ, by omega⟩ (by simp_all)
    have h6 : IsProgrInter pt (R.type pt) (hC.getStates Sᵢ) := by
      simp_all only [Literals.inter]
      exact IsProgrInter.inter h2 h4
    return ⟨(X, A, L), h5, h6⟩
  | .progr S'ᵢ Aᵢ => do
    let ⟨(X, A), h1, h2⟩ ← hC.get_progression_variables R Sᵢ
    let L := UnprimedLiterals.empty
    have h3 : hC.getStates Sᵢ = pt.progression X.val.inter A.toActions ∩ L.val.inter := by
      simp_all [L, UnprimedVariables.val]
    have h4 : IsProgrInter pt (type pt R) (hC.getStates Sᵢ) := by
      simp_all [UnprimedVariables.val, L]
      exact IsProgrInter.empty h2
    return ⟨(X, A, L), h3, h4⟩
  | _ => Validator.throwUnvalid s!"The state set #{Sᵢ} is not an intersection or progression"

-- TODO : make variables primed
def get_regression_variables (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
  Result (UnprimedVariables' pt R × ActionIds pt)
    fun (X, A) ↦ hC.getStates Sᵢ = pt.regression X.val.inter A.toActions ∧
      IsVariableInter pt (R.type pt) X.val.inter :=
   withErrorMessage s!"Verifying that the state set #{Sᵢ} is the regression \
    of an intersection of atomic {R} formulas"
  do
    let ⟨(S'ᵢ, Aᵢ), h⟩ ← (Constraint.isStateRegr C Sᵢ).verify
    have ⟨hS'ᵢ, hAᵢ⟩ : S'ᵢ < Sᵢ ∧ Aᵢ < C.actions.size := by
      have := hC.validStates Sᵢ
      simp_all [Certificate.validStateSetExpr]
    let ⟨X, h1, h2⟩ ← hC.get_inter_variables R ⟨S'ᵢ, by omega⟩
    let A := hC.getActions' ⟨Aᵢ, by omega⟩
    have h3 : hC.getStates Sᵢ = pt.regression X.val.inter A.toActions := by
      rw [← h1]
      exact hC.getStatesRegr Sᵢ ⟨S'ᵢ, by omega⟩ ⟨Aᵢ, by omega⟩ (by simp_all)
    return ⟨(X, A), h3, by simp_all⟩

-- TODO : catch errors
def get_regression_inter (hC : C.validSets) (R : StateSetFormalism) (Sᵢ : Fin C.states.size) :
  Result (UnprimedVariables' pt R × ActionIds pt × UnprimedLiterals' pt R)
    fun (X, A, L) ↦ hC.getStates Sᵢ = pt.regression X.val.inter A.toActions ∩ L.val.inter ∧
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
    have h5 : hC.getStates Sᵢ = pt.regression X.val.inter A.toActions ∩ L.val.inter  := by
      simp_all [Literals.inter]
      rw [← h1, ← h3]
      exact hC.getStatesInter Sᵢ ⟨S'ᵢ, by omega⟩ ⟨S''ᵢ, by omega⟩ (by simp_all)
    have h6 : IsRegrInter pt (R.type pt) (hC.getStates Sᵢ) := by
      simp_all [Literals.inter]
      exact IsRegrInter.inter h2 h4
    return ⟨(X, A, L), h5, h6⟩
  | .regr S'ᵢ Aᵢ => do
    let ⟨(X, A), h1, h2⟩ ← hC.get_regression_variables R Sᵢ
    let L := UnprimedLiterals.empty
    have h3 : hC.getStates Sᵢ = pt.regression X.val.inter A.toActions ∩ L.val.inter := by
      simp_all [L, UnprimedVariables.val]
    have h4 : IsRegrInter pt (type pt R) (hC.getStates Sᵢ) := by
      simp_all [L, UnprimedVariables.val]
      exact IsRegrInter.empty h2
    return ⟨(X, A, L), h3, h4⟩
  | _ => Validator.throwUnvalid s!"The state set #{Sᵢ} is not an intersection or regression"

end Certificate.validSets


-- TODO : Combine B1 - B3?
def constraintB1 (hC : C.validSets) (S1ᵢ S2ᵢ : ℕ) : Constraint Unit where

  prop := fun _ ↦ ∃ hS1ᵢ hS2ᵢ,
    have R := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
    IsLiteralInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩

  verify' :=
    do
      let ⟨⟨⟩, hS1ᵢ⟩ ← (stateBounds' C S1ᵢ).verify
      let ⟨⟨⟩, hS2ᵢ⟩ ← (stateBounds' C S2ᵢ).verify
      let R := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
      let ⟨L1, h1, h2⟩ ← hC.get_inter_literals R ⟨S1ᵢ, hS1ᵢ⟩
      let ⟨L2, h3, h4⟩ ← hC.get_union_literals R ⟨S2ᵢ, hS2ᵢ⟩
      if h5 : R.checkB1 L1 L2 then
        have h6 : hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ := by
          simp_all only [checkB1_correct]
        return ⟨(), by use hS1ᵢ, hS2ᵢ, h2, h4, h6⟩
      else
        throwUnvalid s!"The state set #{S1ᵢ} is not a subset of #{S2ᵢ}"

  elim_exists := elim_exists_0

@[simp]
lemma constraintB1.prop_eq {C : Certificate pt} {hC : C.validSets} {S1ᵢ S2ᵢ : ℕ} {a} :
  (constraintB1 hC S1ᵢ S2ᵢ).prop a ↔
    S1ᵢ < C.states.size ∧ S2ᵢ < C.states.size ∧ ∃ hS1ᵢ hS2ᵢ,
    have R := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
    IsLiteralInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ :=
  by
    simp [constraintB1]
    tauto

def constraintB2 (hC : C.validSets) (S1ᵢ S2ᵢ : ℕ) : Constraint Unit where

  prop := fun () ↦ ∃ hS1ᵢ hS2ᵢ,
    have R := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
    IsProgrInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩

  verify' :=
    do
      let ⟨⟨⟩, hS1ᵢ⟩ ← (stateBounds' C S1ᵢ).verify
      let ⟨⟨⟩, hS2ᵢ⟩ ← (stateBounds' C S2ᵢ).verify
      let R := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
      let ⟨(X, A, L1), h1, h2⟩ ← hC.get_progression_inter R ⟨S1ᵢ, hS1ᵢ⟩
      let ⟨L2, h3, h4⟩ ← hC.get_union_literals R ⟨S2ᵢ, hS2ᵢ⟩
      if h5 : R.checkB2 X A L1 L2 then
        have h6 : hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ := by
          simp_all only [checkB2_correct]
        return ⟨(), by use hS1ᵢ, hS2ᵢ, h2, h4, h6⟩
      else
        throwUnvalid s!"The state set #{S1ᵢ} is not a subset of #{S2ᵢ}"

  elim_exists := elim_exists_0

@[simp]
lemma constraintB2.prop_eq {C : Certificate pt} {hC : C.validSets} {S1ᵢ S2ᵢ : ℕ} {a} :
  (constraintB2 hC S1ᵢ S2ᵢ).prop a ↔
    S1ᵢ < C.states.size ∧ S2ᵢ < C.states.size ∧ ∃ hS1ᵢ hS2ᵢ,
    have R := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
    IsProgrInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ :=
  by
    simp [constraintB2]
    tauto

def constraintB3 (hC : C.validSets) (S1ᵢ S2ᵢ : ℕ) : Constraint Unit where

  prop := fun () ↦ ∃ hS1ᵢ hS2ᵢ,
    have R := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
    IsRegrInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩

  verify' :=
    do
      let ⟨⟨⟩, hS1ᵢ⟩ ← (stateBounds' C S1ᵢ).verify
      let ⟨⟨⟩, hS2ᵢ⟩ ← (stateBounds' C S2ᵢ).verify
      let R := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
      let ⟨(X, A, L1), h1, h2⟩ ← hC.get_regression_inter R ⟨S1ᵢ, hS1ᵢ⟩
      let ⟨L2, h3, h4⟩ ← hC.get_union_literals R ⟨S2ᵢ, hS2ᵢ⟩
      if h5 : R.checkB3 X A L1 L2 then
        have h6 : hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ := by
          simp_all only [checkB3_correct]
        return ⟨(), by use hS1ᵢ, hS2ᵢ, h2, h4, h6⟩
      else
        throwUnvalid s!"The state set #{S1ᵢ} is not a subset of #{S2ᵢ}"

  elim_exists := elim_exists_0

@[simp]
lemma constraintB3.prop_eq {C : Certificate pt} {hC : C.validSets} {S1ᵢ S2ᵢ : ℕ} {a} :
  (constraintB3 hC S1ᵢ S2ᵢ).prop a ↔
    S1ᵢ < C.states.size ∧ S2ᵢ < C.states.size ∧ ∃ hS1ᵢ hS2ᵢ,
    have R := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩, ⟨S2ᵢ, hS2ᵢ⟩]
    IsRegrInter pt (R.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteralUnion pt (R.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ :=
  by
    simp [constraintB3]
    tauto

def constraintB4 (hC : C.validSets) (S1ᵢ S2ᵢ : ℕ) : Constraint Unit where

  prop := fun () ↦ ∃ hS1ᵢ hS2ᵢ,
    have R1 := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩]
    have R2 := hC.get_formalism [⟨S2ᵢ, hS2ᵢ⟩]
    IsLiteral pt (R1.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteral pt (R2.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩

  verify' :=
    do
      let ⟨⟨⟩, hS1ᵢ⟩ ← (stateBounds' C S1ᵢ).verify
      let ⟨⟨⟩, hS2ᵢ⟩ ← (stateBounds' C S2ᵢ).verify
      let R1 := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩]
      let R2 := hC.get_formalism [⟨S2ᵢ, hS2ᵢ⟩]
      let ⟨l1, h1, h2⟩ ← hC.get_literal R1 ⟨S1ᵢ, hS1ᵢ⟩
      let ⟨l2, h3, h4⟩ ← hC.get_literal R2 ⟨S2ᵢ, hS2ᵢ⟩
      if h5 : R1.checkB4 R2 l1 l2 then
        have h6 : hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ := by
          simp_all only [checkB4_correct]
        return ⟨(), by use hS1ᵢ, hS2ᵢ, h2, h4, h6⟩
      else
        throwUnvalid s!"The state set #{S1ᵢ} is not a subset of #{S2ᵢ}"

  elim_exists := elim_exists_0

@[simp]
lemma constraintB4.prop_eq {C : Certificate pt} {hC : C.validSets} {S1ᵢ S2ᵢ : ℕ} {a} :
  (constraintB4 hC S1ᵢ S2ᵢ).prop a ↔
    S1ᵢ < C.states.size ∧ S2ᵢ < C.states.size ∧ ∃ hS1ᵢ hS2ᵢ,
    have R1 := hC.get_formalism [⟨S1ᵢ, hS1ᵢ⟩]
    have R2 := hC.get_formalism [⟨S2ᵢ, hS2ᵢ⟩]
    IsLiteral pt (R1.type pt) (hC.getStates ⟨S1ᵢ, hS1ᵢ⟩) ∧
    IsLiteral pt (R2.type pt) (hC.getStates ⟨S2ᵢ, hS2ᵢ⟩) ∧
    hC.getStates ⟨S1ᵢ, hS1ᵢ⟩ ⊆ hC.getStates ⟨S2ᵢ, hS2ᵢ⟩ :=
  by
    simp [constraintB4]
    tauto

-- TODO : make more efficient?
def constraintB5 {C : Certificate pt} (hC : C.validSets) (A1ᵢ A2ᵢ : ℕ) : Constraint Unit where

  prop := fun () ↦ ∃ hA1ᵢ hA2ᵢ, hC.getActions ⟨A1ᵢ, hA1ᵢ⟩ ⊆ hC.getActions ⟨A2ᵢ, hA2ᵢ⟩

  verify' :=
    do
      let ⟨⟨⟩, hA1ᵢ⟩ ← (actionBounds' C A1ᵢ).verify
      let ⟨⟨⟩, hA2ᵢ⟩ ← (actionBounds' C A2ᵢ).verify
      if h : hC.getActions' ⟨A1ᵢ, hA1ᵢ⟩ ⊆ hC.getActions' ⟨A2ᵢ, hA2ᵢ⟩ then
        return ⟨(), by
          simp [getActions]
          use hA1ᵢ, hA2ᵢ
          grind⟩
      else
        throwUnvalid s!"The action set #{A1ᵢ} is not a subset of #{A2ᵢ}"

  elim_exists := elim_exists_0

@[simp]
lemma constraintB5.prop_eq {C : Certificate pt} {hC : C.validSets} {A1ᵢ A2ᵢ : ℕ} {u} :
  (constraintB5 hC A1ᵢ A2ᵢ).prop u ↔ A1ᵢ < C.actions.size ∧ A2ᵢ < C.actions.size ∧
    ∃ hA1ᵢ hA2ᵢ, hC.getActions ⟨A1ᵢ, hA1ᵢ⟩ ⊆ hC.getActions ⟨A2ᵢ, hA2ᵢ⟩ :=
  by
    simp [constraintB5]
    tauto

end Validator
