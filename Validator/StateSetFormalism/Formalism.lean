import Validator.StateSetFormalism.Formula

open Validator.Formula (Model Models Renaming OfPartialModel)

/-!
All variables `i` have a primed and an unprimed version,
represented by `2 * i + 1` and `2 * i` respectively.
-/

-- TODO : check if this makes sense with namespaces
def Fin.toUnprimed {n} : Fin n → Fin (2 * n) :=
  fun i ↦ ⟨2 * i.val, by omega⟩

lemma Fin.toUnprimedStrictMono {n} : StrictMono (@toUnprimed n) :=
  by
    simp [toUnprimed, StrictMono]

def Fin.toPrimed {n} (i : Fin (2 * n)) (h : Even i.val) : Fin (2 * n) :=
  ⟨i.val + 1, by grind⟩

namespace Validator.VarSet'

abbrev IsUnprimed {n} (V : VarSet' (2 * n)) : Prop :=
  ∀ i ∈ V.val, Even i.val

@[simp]
lemma isUnprimed_empty {n} : empty.IsUnprimed (n := n) :=
  by simp [empty, IsUnprimed]

def toUnprimed {n} (V : VarSet' n) : VarSet' (2 * n) :=
  ⟨V.val.map Fin.toUnprimed, by
    rw [StrictMono.sorted_lt_listMap Fin.toUnprimedStrictMono]
    exact V.prop⟩

@[simp]
lemma toUnprimed_mem_toUnprimed_iff {n} {V : VarSet' n} {i : Fin n} :
  i.toUnprimed ∈ V.toUnprimed.val ↔ i ∈ V.val :=
  by
    simp [toUnprimed, Fin.toUnprimed, Fin.val_inj]

lemma isUnprimed_toUnprimed {n} {V : VarSet' n} : IsUnprimed (toUnprimed V) :=
  by simp [toUnprimed, IsUnprimed, Fin.toUnprimed]

def unprimedVars n : VarSet' (2 * n) :=
    let vars := List.ofFn Fin.toUnprimed
    have h : vars.Sorted (· < ·) := by
      simp [vars, List.Sorted, Fin.toUnprimed]
    ⟨vars, h⟩

lemma isUnprimed_unprimedVars {n} : IsUnprimed (unprimedVars n) :=
  by simp [unprimedVars, IsUnprimed, Fin.toUnprimed]

end VarSet'

namespace Formula.Model

def unprimedState {n} (M : Model (2 * n)) : State n :=
  { i | M i.toUnprimed }

/--
Swap the primed and unprimed versions of the variables in V and
replace the other primed variables with their even version.
-/
def toPrimed {n} (V : VarSet' n)
  (M : Model (2 * n)) : Model (2 * n) :=
  fun i ↦
    if h : ¬Even i.val then
      M ⟨i - 1, by omega⟩
    else if ⟨i / 2, by omega⟩ ∈  V.val then
      M ⟨i + 1, by grind⟩
    else
      M i

lemma toPrimed_eq {n} (V : VarSet' n) (M : Model (2 * n)) :
  M.toPrimed V =
  fun i : Fin (2 * n) ↦
    if h : ¬Even i.val then
      M ⟨i - 1, by omega⟩
    else if ⟨i / 2, by omega⟩ ∈  V.val then
      M ⟨i + 1, by grind⟩
    else
      M i := rfl

lemma unprimedState_eq_iff_unprimedVars {n} {M M' : Model (2 * n)} :
  M.unprimedState = M'.unprimedState ↔ ∀ i ∈ (VarSet'.unprimedVars n).val, M i = M' i :=
  by
    simp [Model.unprimedState, VarSet'.unprimedVars, Fin.toUnprimed, Set.ext_iff]

/-
lemma unprimedState_eq_iff_even {n} {M M' : Model (2 * n)} :
  M.unprimedState = M'.unprimedState ↔ ∀ i : Fin (2 * n), Even i.val → M i = M' i :=
  by
    simp [Model.unprimedState, Fin.toUnprimed, Set.ext_iff, even_iff_exists_two_mul]
    constructor
    · rintro h ⟨i, hi⟩ j hj
      specialize h ⟨j, by omega⟩
      grind
    · rintro h ⟨i, hi⟩
      specialize h ⟨2 * i, by omega⟩ i
      grind
-/

lemma exists_model_of_state {n} s : ∃ M : Model (2 * n), s = M.unprimedState :=
  by
    let M : Model (2 * n) := fun i => ⟨i / 2, by omega⟩ ∈ s
    use M
    simp [M, Model.unprimedState, Fin.toUnprimed]

end Formula.Model

open Formula

class Formalism {n} (pt : STRIPS n) R extends Formula (2 * n) R where

  toStates (φ : R) : States n := (Formula.models φ).image Model.unprimedState

  toStates_eq (φ : R) : toStates φ = (Formula.models φ).image Model.unprimedState := by simp

-- TODO : only for completeness, remove?
@[simp]
instance {n} {pt : STRIPS n} : Formalism pt (States n) where

  vars _ := VarSet'.unprimedVars n

  models φ := { M | M.unprimedState ∈ φ }

  models_equiv_right := by
    intro φ M M' h1 h2
    have : M.unprimedState = M'.unprimedState := by
      simp_all [Model.unprimedState_eq_iff_unprimedVars]
    simp_all

  toStates := id

  toStates_eq φ := by
    ext s
    have ⟨M, hM⟩ := Model.exists_model_of_state s
    simp
    grind

namespace Formalism

variable {n} {pt : STRIPS n} {R}

abbrev Variable (pt : STRIPS n) (R : Type) [Formalism pt R] := R

namespace Variable

def models [Formalism pt R] : Variable pt R → Models (2 * n) :=
  Formula.models

abbrev vars [Formalism pt R] : Variable pt R → VarSet' (2 * n) :=
  Formula.vars

def toStates [Formalism pt R] : Variable pt R → States n :=
  Formalism.toStates pt

lemma toStates_eq [Formalism pt R] {x : Variable pt R} :
  x.toStates = x.models.image Model.unprimedState := by
    simp [Variable.toStates, Variable.models, Formalism.toStates_eq]

@[simp]
instance [F : Formalism pt R] : Membership (Fin (2 * n)) (Variable pt R) where

  mem x i := i ∈ x.vars.val

end Variable

abbrev UnprimedVariable (pt : STRIPS n) (R : Type) [F : Formalism pt R] :=
  { x : Variable pt R // x.vars.IsUnprimed }

namespace UnprimedVariable

def ofVarset' R [Formalism pt R] [h : OfPartialModel (2 * n) R]
  (V : VarSet' n) (pos := true) : UnprimedVariable pt R :=
  let x : Variable pt R :=
    h.ofPartialModel V.toUnprimed (BitVec.fill _ pos)
  have hx : x.vars.IsUnprimed := by
    simp [x, h.ofPartialModel_correct]
    exact VarSet'.isUnprimed_toUnprimed
  ⟨x, hx⟩

@[simp]
lemma toUnprimed_mem_vars_ofVarSet' [Formalism pt R] [h : OfPartialModel (2 * n) R]
  {V : VarSet' n} {pos i} : i.toUnprimed ∈ (ofVarset' (h := h) R V pos).val.vars.val ↔ i ∈ V.val :=
  by
    simp [ofVarset', OfPartialModel.ofPartialModel_correct]

@[simp]
lemma mem_models_ofVarSet' [Formalism pt R] [h : OfPartialModel (2 * n) R]
  {V : VarSet' n} {pos M} :
  M ∈ (ofVarset' (h := h) R V pos).val.models ↔ (∀ i ∈ V.val, i ∈ M.unprimedState ↔ pos):=
  by
    simp [ofVarset', Variable.models, OfPartialModel.ofPartialModel_correct]
    simp [Formula.PartialModel.models, VarSet'.toUnprimed, Fin.toUnprimed, Model.unprimedState]
    constructor
    · intro h1 i hi
      obtain ⟨j, h2, rfl⟩ := List.getElem_of_mem hi
      exact h1 ⟨j, by simp [h2]⟩
    · simp_all only [List.getElem_mem, implies_true]

lemma mem_models_of_eq_toState [Formalism pt R]
  {x : UnprimedVariable pt R} {M M' : Model (2 * n)} :
  M.unprimedState = M'.unprimedState → M ∈ x.val.models → M' ∈ x.val.models :=
  by
    rcases x with ⟨x, h1⟩
    intro h2 h3
    have h4 : ∀ i ∈ x, M i = M' i := by
      intro i hi
      simp [VarSet'.IsUnprimed, even_iff_exists_two_mul] at h1
      have ⟨j, hj⟩ := h1 i hi
      simp [Set.ext_iff, Model.unprimedState, Fin.toUnprimed] at h2
      have h5 := @h2 ⟨j, by omega⟩
      simp [← hj] at h5
      simp [h5]
    simp [Variable.models]
    rw [← Formula.models_equiv h4]
    exact h3

lemma mem_models_iff_of_eq_unprimedState [Formalism pt R]
  {x : Variable pt R} {M M' : Model (2 * n)} :
  x.vars.IsUnprimed → M.unprimedState = M'.unprimedState →
  (M ∈ x.models ↔ M' ∈ x.models) :=
  by
    intro h1 h2
    have := mem_models_of_eq_toState h2 (x := ⟨x, h1⟩)
    have := mem_models_of_eq_toState h2.symm (x := ⟨x, h1⟩)
    grind

def toPrimedAux {n} (oldVars : List (Fin (2 * n))) (h : ∀ i ∈ oldVars, Even i.val)
  (toRename : List (Fin n)) : List (Fin (2 * n)) :=
  match oldVars, toRename with
  | [], _ => []
  | oldVars, [] => oldVars
  | i :: oldVars, j :: toRename =>
    match compare i j.toUnprimed with
    | .lt => i :: toPrimedAux oldVars (by simp_all) (j :: toRename)
    | .eq =>
      have hi : i + 1 < 2 * n := by
        simp [even_iff_exists_two_mul] at h
        omega
      ⟨i + 1, hi⟩ :: toPrimedAux oldVars (by simp_all) toRename
    | .gt => toPrimedAux (i :: oldVars) (by simp_all) toRename

private lemma toPrimedAux_eq' {n}
  {oldVars : List (Fin (2 * n))} (h1 : oldVars.Sorted (· < ·)) {h2}
  {toRename} (h3 : toRename.Sorted (· < ·)) :
  toPrimedAux oldVars h2 toRename = oldVars.attach.map (fun ⟨i, hi⟩ ↦
    if i ∈ (VarSet'.toUnprimed ⟨toRename, h3⟩).val then
      i.toPrimed (h2 i hi)
    else i) :=
  by
    unfold toPrimedAux
    simp
    split
    case h_1 => simp
    case h_2 => simp [VarSet'.toUnprimed]
    case h_3 i oldVars j toRename h4 =>
      simp [VarSet'.toUnprimed, Fin.toUnprimed]
      split
      case h_1 heq =>
        rcases i with ⟨i, hi⟩
        have h := @toPrimedAux_eq' _ oldVars (by simp_all) (by grind) (j :: toRename) h3
        simp [VarSet'.toUnprimed, Fin.toUnprimed, h]
        simp [compare_lt_iff_lt] at heq
        simp at h3
        grind
      case h_2 heq =>
        have h := @toPrimedAux_eq' _ oldVars (by simp_all) (by grind) toRename (by simp_all)
        simp at heq h1 h3
        subst heq
        simp [VarSet'.toUnprimed, Fin.toUnprimed, Fin.toPrimed, h]
        rintro i' h5
        split
        · grind
        · grind
      case h_3 heq =>
        have h := @toPrimedAux_eq' _ (i :: oldVars) (by simp_all) (by grind) toRename (by simp_all)
        simp [compare_gt_iff_gt] at heq h3
        simp [VarSet'.toUnprimed, Fin.toUnprimed, h]
        simp [even_iff_exists_two_mul] at h4
        constructor
        · split
          · grind
          · grind
        · intro ⟨i', hi'⟩ h5
          obtain ⟨j', rfl⟩ := h4.2 ⟨i', hi'⟩ h5
          simp at h1
          split
          · grind
          · grind
termination_by oldVars.length + toRename.length

lemma toPrimedAux_eq {n} {oldVars : VarSet' (2 * n)} {h} {toRename : VarSet' n} :
  toPrimedAux oldVars.val h toRename = oldVars.val.attach.map (fun ⟨i, hi⟩ ↦
    if i ∈ toRename.toUnprimed.val then
      have hi : i + 1 < 2 * n := by
        simp [even_iff_exists_two_mul] at h
        have := h i hi
        omega
      ⟨i + 1, hi⟩
    else i) := toPrimedAux_eq' oldVars.prop toRename.prop

/--
Make all unprimed vars in `x` corresponding to the vars in `V` primed.
TODO : clarify the difference between all kinds of variables.
-/
def toPrimed [Formalism pt R] [Renaming (2 * n) R]
  (x : UnprimedVariable pt R) (V : VarSet' n) : Variable pt R :=
  let vars : List (Fin (2 * n)) :=
    toPrimedAux x.val.vars (by grind) V.val
  have hvars : vars.Sorted (· < ·) := by
    have h1 := x.val.vars.prop
    simp_all only [List.Sorted, List.pairwise_iff_getElem, toPrimedAux_eq, List.length_map,
      List.length_attach, List.getElem_map, List.getElem_attach, vars]
    have h2 := x.prop
    simp [VarSet'.IsUnprimed, even_iff_exists_two_mul] at h2
    intro i j hi hj h3
    specialize h1 i j hi hj h3
    obtain ⟨vi, h4⟩ := h2 x.val.vars.val[i] (by simp)
    obtain ⟨vj, h5⟩ := h2 x.val.vars.val[j] (by simp)
    simp_all only [Fin.lt_def, Nat.reduceLT, Nat.mul_lt_mul_left]
    grind
  Renaming.rename x ⟨vars, hvars⟩ (by simp [vars, toPrimedAux_eq])

lemma mem_models_toPrimed_iff [Formalism pt R] [Renaming (2 * n) R]
  {x : UnprimedVariable pt R} {V M} :
  M ∈ (x.toPrimed V).models ↔ M.toPrimed V ∈ x.val.models :=
  by
    simp [Variable.models, toPrimed, toPrimedAux_eq, Variable.models, Renaming.mem_rename_models]
    apply Formula.models_equiv
    simp [Renaming.renameModel, Model.toPrimed_eq, Variable.vars, -Nat.not_even_iff_odd]
    intro i hi
    have h2  := x.prop i hi
    simp [h2]
    split
    case _ => simp_all
    case _ j h3 =>
      simp at h3
      rcases h3 with ⟨rfl, _⟩
      simp_all [VarSet'.toUnprimed, Fin.toUnprimed]
      split
      case _ h4 =>
        have : ⟨(Formula.vars x.val).val[j] / 2, by omega⟩ ∈ V.val := by
          rcases h4 with ⟨i, h3, h4⟩
          simp [← h4]
          exact h3
        simp_all
      case _ h4 =>
        have : ¬⟨(Formula.vars x.val).val[j] / 2, by omega⟩ ∈ V.val := by
          intro h5
          simp_all [even_iff_exists_two_mul]
          rcases h2 with ⟨i, h3⟩
          specialize h4 _ h5
          simp_all
          simp [← h3] at h4
        simp_all

end UnprimedVariable

abbrev Literal (pt : STRIPS n) R [Formalism pt R] := Variable pt R × Bool

def Literal.models [Formalism pt R] : Literal pt R → Models (2 * n)
| (X, true) => X.models
| (X, false) => X.modelsᶜ

def Literal.toStates [Formalism pt R] : Literal pt R → States n
| (X, true) => X.toStates
| (X, false) => X.toStatesᶜ

abbrev UnprimedLiteral (pt : STRIPS n) R [Formalism pt R] := UnprimedVariable pt R × Bool

def UnprimedLiteral.val [Formalism pt R] :
  UnprimedLiteral pt R → Literal pt R :=
  fun (x, b) ↦ (x, b)

lemma UnprimedLiteral.toStates_eq [Formalism pt R] : {l : UnprimedLiteral pt R} →
  l.val.toStates = l.val.models.image Model.unprimedState
| (X, true) => by
  simp [Literal.toStates, Variable.toStates_eq, Literal.models, UnprimedLiteral.val]
| (X, false) => by
  simp [Literal.toStates, Variable.toStates_eq, Literal.models, UnprimedLiteral.val]
  ext s
  simp
  constructor
  · have ⟨M, h⟩ := Model.exists_model_of_state s
    grind
  · rintro ⟨M, h1, rfl⟩ M' h2 h3
    rw [UnprimedVariable.mem_models_iff_of_eq_unprimedState X.prop h3] at h2
    contradiction

abbrev Variables (pt : STRIPS n) R [Formalism pt R] := List (Variable pt R)

namespace Variables

-- TODO : Remove?
def single [Formalism pt R] : Variable pt R → Variables pt R :=
  List.singleton

-- First take the intersection of all models, and then map to models to the states
def inter [F : Formalism pt R] (X : Variables pt R) : States n :=
  { s | ∃ M : Model (2 * n), M.unprimedState = s ∧ ∀ x ∈ X, M ∈ x.models }

lemma mem_inter [Formalism pt R] {X : Variables pt R} :
  ∀ s, s ∈ X.inter ↔ ∃ M : Model (2 * n), M.unprimedState = s ∧ ∀ x ∈ X, M ∈ x.models  :=
  by simp [inter]

@[simp]
lemma inter_empty [F : Formalism pt R] : inter (F := F) [] = Set.univ :=
  by
    ext s
    obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
    simp [inter]

@[simp]
lemma inter_single [Formalism pt R] {x : Variable pt R} :
  (single x).inter = x.toStates :=
  by
    ext s
    simp [List.singleton, single, Variable.toStates, mem_inter, toStates_eq, Variable.models]
    tauto

def union [F : Formalism pt R] (X : Variables pt R) : States n :=
  { s | ∃ M, M.unprimedState = s ∧ ∃ x ∈ X, M ∈ x.models }

lemma mem_union [Formalism pt R] {X : Variables pt R} :
  ∀ s, s ∈ X.union ↔ ∃ M, M.unprimedState = s ∧ ∃ x ∈ X, M ∈ x.models :=
  by simp [union]

@[simp]
lemma union_empty [F : Formalism pt R] : union (F := F) [] = ∅ :=
  by
    ext s
    simp [union]

@[simp]
lemma union_single [Formalism pt R] {x : Variable pt R} :
  (single x).union = x.toStates :=
  by
    ext s
    simp [List.singleton ,single, Variable.toStates, mem_union, toStates_eq, Variable.models]
    tauto

end Variables

abbrev UnprimedVariables (pt : STRIPS n) R [Formalism pt R] := List (UnprimedVariable pt R)

namespace UnprimedVariables

def val [Formalism pt R] :
  UnprimedVariables pt R → Variables pt R := fun X ↦ X

def single [Formalism pt R] : UnprimedVariable pt R → UnprimedVariables pt R :=
  List.singleton

@[simp]
lemma val_single [Formalism pt R] {x : UnprimedVariable pt R} :
  (single x).val = Variables.single x.val :=
  by
    simp [single, Variables.single, val, List.singleton]

lemma val_append [Formalism pt R] {L1 L2 : UnprimedVariables pt R} :
  (L1 ++ L2).val = L1.val ++ L2.val :=
  by simp [val]

@[simp]
lemma union_append [Formalism pt R] {X1 X2 : UnprimedVariables pt R} :
  (X1 ++ X2).val.union = X1.val.union ∪ X2.val.union :=
  by
    ext s
    simp [val, Variables.mem_union]
    grind

@[simp low]
lemma mem_inter [F : Formalism pt R] {X : UnprimedVariables pt R} {s} :
  s ∈ X.val.inter ↔ ∀ x ∈ X, s ∈ x.val.toStates :=
  by
    simp [Variables.mem_inter, val, Variable.toStates_eq]
    constructor
    · rintro ⟨M, rfl, h1⟩ x h2 h3
      use M
      grind
    · intro h1
      obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
      use M, rfl
      intro x h2 h3
      specialize h1 x h2 h3
      rcases h1 with ⟨M', h1, h4⟩
      rw [← UnprimedVariable.mem_models_iff_of_eq_unprimedState h2 h4]
      exact h1

@[simp]
lemma inter_variables_append [Formalism pt R]
  {X1 : Variables pt R} {X2 : UnprimedVariables pt R} :
  (X1 ++ X2.val).inter = X1.inter ∩ X2.val.inter :=
  by
    ext s
    simp [Variables.mem_inter, val]
    constructor
    · grind
    · rintro ⟨⟨M1, rfl, h1⟩, M2, h2, h3⟩
      use M1, rfl
      intro x hx
      rcases hx with hx | ⟨hx, h4⟩
      · exact h1 x hx
      · rw [← UnprimedVariable.mem_models_iff_of_eq_unprimedState hx h2]
        exact h3 x hx h4

@[simp]
lemma inter_append [Formalism pt R] {X1 X2 : UnprimedVariables pt R} :
  (X1 ++ X2).val.inter = X1.val.inter ∩ X2.val.inter :=
  by
    simp [val_append]

lemma inter_subset_union_iff_models [F : Formalism pt R]
  (X1 : Variables pt R) (X2 : UnprimedVariables pt R) :
  X1.inter ⊆ X2.val.union ↔ (∀ M, (∀ x ∈ X1, M ∈ F.models x) → ∃ x ∈ X2, M ∈ x.val.models) :=
  by
    simp [Set.subset_def, UnprimedVariables.val,
      Variables.mem_inter, Variables.mem_union]
    constructor
    · intro h1 M hM
      specialize @h1 M.unprimedState M rfl hM
      rcases h1 with ⟨M', h1, x, hx, h2⟩
      use x, hx
      rcases hx with ⟨h3, hx⟩
      simp_all [← UnprimedVariable.mem_models_iff_of_eq_unprimedState h3 h1]
    · rintro h1 s M rfl h2
      specialize @h1 M h2
      grind

def toPrimed [F : Formalism pt R] [Renaming (2 * n) R]
  (X : UnprimedVariables pt R) (V : VarSet' n) : Variables pt R :=
  X.map (UnprimedVariable.toPrimed · V)

lemma mem_inter_toPrimed [F : Formalism pt R] [Renaming (2 * n) R]
  {X : UnprimedVariables pt R} {V s} :
  s ∈ (toPrimed X V).inter ↔ ∃ s' ∈ (UnprimedVariables.val X).inter, ∀ i ∉ V.val, i ∈ s' ↔ i ∈ s :=
  by
    simp [Variables.inter, toPrimed, UnprimedVariables.val]
    constructor
    · rintro ⟨M, rfl, h1⟩
      use Model.toPrimed V M
      constructor
      · intro x h2 h3
        specialize h1 (UnprimedVariable.toPrimed ⟨x, h2⟩ V) x h2 h3 rfl
        simp [UnprimedVariable.mem_models_toPrimed_iff] at h1
        exact h1
      · simp [Model.toPrimed_eq, Model.unprimedState, Fin.toUnprimed]
        grind
    · rintro ⟨M, h1, h2⟩
      -- Take unprimed variables from `s` and primed variables from `M.unprimedState`
      use fun i ↦
        if Even i.val then
          ⟨i / 2, by omega⟩ ∈ s
        else
          ⟨i / 2, by omega⟩ ∈ M.unprimedState
      simp [Model.unprimedState, Fin.toUnprimed]
      intro _ x h3 h4 rfl
      simp [UnprimedVariable.mem_models_toPrimed_iff]
      specialize h1 x h3 h4
      refine Formula.models_equiv_right _ _ _ ?_ h1
      intro ⟨i, hi⟩ h5
      have h6 := h3 ⟨i, hi⟩ h5
      simp [Model.toPrimed_eq, h6, Nat.even_add_one]
      simp [even_iff_exists_two_mul] at h6
      rcases h6 with ⟨j, rfl⟩
      simp_all [Model.unprimedState, Fin.toUnprimed]
      grind

end UnprimedVariables

-- TODO : check if needed, or if everything can be done in terms of `UnprimedLiterals`
abbrev Literals (pt : STRIPS n) R [Formalism pt R] :=
  Variables pt R × Variables pt R

-- TODO : write in terms of `Variables`?
namespace Literals

def pos [Formalism pt R] (X : Variables pt R) : Literals pt R :=
  (X, [])

instance [Formalism pt R] : Append (Literals pt R) where
  append L1 L2 := (L1.1 ++ L2.1, L1.2 ++ L2.2)

@[simp]
lemma append_pos [Formalism pt R] {L1 L2 : Literals pt R} : (L1 ++ L2).1 = L1.1 ++ L2.1 :=
  by simp [instHAppendOfAppend, instAppend]

@[simp]
lemma append_neg [Formalism pt R] {L1 L2 : Literals pt R} : (L1 ++ L2).2 = L1.2 ++ L2.2 :=
  by simp [instHAppendOfAppend, instAppend]

def union [Formalism pt R] (L : Literals pt R) : States n :=
  { s | ∃ M : Model (2 * n), M.unprimedState = s ∧
    ((∃ x ∈ L.1, M ∈ x.models) ∨ (∃ x ∈ L.2, M ∉ x.models)) }

@[simp]
lemma mem_union [Formalism pt R] {ls : Literals pt R} {s} :
  s ∈ ls.union ↔ ∃ M : Model (2 * n), M.unprimedState = s ∧
  ((∃ x ∈ ls.1, M ∈ x.models) ∨ (∃ x ∈ ls.2, M ∉ x.models)) :=
  by
    simp [union]

@[simp]
lemma union_append [Formalism pt R] {L1 L2 : Literals pt R} :
  (L1 ++ L2).union = L1.union ∪ L2.union :=
  by
    ext s
    simp
    grind

def inter [Formalism pt R] (L : Literals pt R) : States n :=
  { s | ∃ M : Model (2 * n), M.unprimedState = s ∧
    (∀ x ∈ L.1, M ∈ x.models) ∧ (∀ x ∈ L.2, M ∉ x.models) }

@[simp]
lemma mem_inter [Formalism pt R] {L : Literals pt R} {s} :
  s ∈ L.inter ↔ ∃ M : Model (2 * n), M.unprimedState = s ∧
  (∀ x ∈ L.1, M ∈ x.models) ∧ (∀ x ∈ L.2, M ∉ x.models) :=
  by
    simp [inter]

end Literals

abbrev UnprimedLiterals (pt : STRIPS n) R [Formalism pt R] :=
  UnprimedVariables pt R × UnprimedVariables pt R

namespace UnprimedLiterals

def val [Formalism pt R] :
  UnprimedLiterals pt R → Literals pt R := fun (X, X') ↦ (X, X')

@[simp]
abbrev empty [Formalism pt R] :  UnprimedLiterals pt R := ([], [])

def single [Formalism pt R] : UnprimedLiteral pt R → UnprimedLiterals pt R
| (X, true) => ([X], [])
| (X, false) => ([], [X])

@[simp]
lemma union_single [Formalism pt R] {l : UnprimedLiteral pt R} :
  (single l).val.union = l.val.toStates :=
  by
    simp [single, UnprimedLiteral.toStates_eq]
    split
    all_goals
      ext s
      simp [UnprimedLiterals.val, Literal.models, UnprimedLiteral.val]
      grind

@[simp]
lemma inter_single [Formalism pt R] {l : UnprimedLiteral pt R} :
  (single l).val.inter = l.val.toStates :=
  by
    simp [single, UnprimedLiteral.toStates_eq]
    split
    all_goals
      ext s
      simp [UnprimedLiterals.val, Literal.models, UnprimedLiteral.val]
      grind

instance [Formalism pt R] : Append (UnprimedLiterals pt R) where
  append L1 L2 := (L1.1 ++ L2.1, L1.2 ++ L2.2)

@[simp low]
lemma val_append [Formalism pt R] {L1 L2 : UnprimedLiterals pt R} :
  (L1 ++ L2).val = L1.val ++ L2.val :=
  by
    simp [val]
    rfl

open UnprimedVariable (mem_models_iff_of_eq_unprimedState)

@[simp low]
lemma union_val [Formalism pt R] {L : UnprimedLiterals pt R} :
  L.val.union = L.1.val.union ∪ L.2.val.interᶜ :=
  by
    ext s
    simp [Variables.mem_inter, Variables.mem_union, Variable.models, val, UnprimedVariables.val]
    constructor
    · rintro ⟨M, rfl, h1⟩
      rcases h1 with ⟨x, ⟨h1, h2⟩, h3⟩ | ⟨x, ⟨h1, h2⟩, h3⟩
      · grind
      · apply Or.inr
        intro M' h4
        have := mem_models_iff_of_eq_unprimedState h1 h4
        grind
    · intro h
      rcases h with h | h
      · grind
      · obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
        grind

@[simp low]
lemma inter_val [Formalism pt R] {L : UnprimedLiterals pt R} :
  L.val.inter = L.1.val.inter ∩ L.2.val.unionᶜ :=
  by
    ext s
    simp [Variables.mem_inter, Variables.mem_union, val, UnprimedVariables.val]
    constructor
    · rintro ⟨M, rfl, h1, h2⟩
      constructor
      · use M, rfl
      · intro M' h3 x h4 h5 h6
        rw [mem_models_iff_of_eq_unprimedState h4 h3] at h6
        exact h2 x h4 h5 h6
    · grind

/-- Note that this is not true for primed variables -/
@[simp]
lemma inter_append [Formalism pt R] {L1 L2 : UnprimedLiterals pt R} :
  (L1.val ++ L2.val).inter = L1.val.inter ∩ L2.val.inter :=
  by
    ext s
    simp [UnprimedLiterals.val]
    constructor
    · grind
    · rintro ⟨⟨M1, rfl, h1, h2⟩, M2, h3, h4, h5⟩
      use M1, rfl
      constructor
      · intro x hx
        rcases hx with ⟨hx, h6⟩ | ⟨hx, h6⟩
        · exact h1 x hx h6
        · rw [← mem_models_iff_of_eq_unprimedState hx h3]
          exact h4 x hx h6
      · intro x hx
        rcases hx with ⟨hx, h6⟩ | ⟨hx, h6⟩
        · exact h2 x hx h6
        · rw [← mem_models_iff_of_eq_unprimedState hx h3]
          exact h5 x hx h6

end UnprimedLiterals

inductive IsVariable {n} (pt : STRIPS n) R [Formalism pt R] : States n → Prop
| empty : IsVariable pt R ∅
| init : IsVariable pt R {pt.init}
| goal : IsVariable pt R pt.goal_states
| explicit (φ : R) : IsVariable pt R (Formalism.toStates pt φ)

inductive IsLiteral {n} (pt : STRIPS n) R [Formalism pt R] : States n → Prop
| pos {S} : IsVariable pt R S → IsLiteral pt R S
| neg {S} : IsVariable pt R S → IsLiteral pt R (Sᶜ)

inductive IsLiteralUnion {n} (pt : STRIPS n) R [Formalism pt R] : States n → Prop
| single {S} : IsLiteral pt R S → IsLiteralUnion pt R S
| union {S S'} : IsLiteralUnion pt R S → IsLiteralUnion pt R S' → IsLiteralUnion pt R (S ∪ S')

inductive IsVariableInter {n} (pt : STRIPS n) R [Formalism pt R] : States n → Prop
| single {S} : IsVariable pt R S → IsVariableInter pt R S
| inter {S S'} : IsVariableInter pt R S → IsVariableInter pt R S' → IsVariableInter pt R (S ∩ S')

inductive IsLiteralInter {n} (pt : STRIPS n) R [Formalism pt R] : States n → Prop
| single {S} : IsLiteral pt R S → IsLiteralInter pt R S
| inter {S S'} : IsLiteralInter pt R S → IsLiteralInter pt R S' → IsLiteralInter pt R (S ∩ S')

-- TODO : check whether it should be enforced that A ⊆ pt.actions
inductive IsProgrInter {n} (pt : STRIPS n) R [Formalism pt R] : States n → Prop
| empty {S A} : IsVariableInter pt R S → IsProgrInter pt R (pt.progression S A)
| inter {S S' A} :
  IsVariableInter pt R S → IsLiteralInter pt R S' →
  IsProgrInter pt R (pt.progression S A ∩ S')

-- TODO : check whether it should be enforced that A ⊆ pt.actions
inductive IsRegrInter {n} (pt : STRIPS n) R [Formalism pt R] : States n → Prop
| empty {S A} : IsVariableInter pt R S → IsRegrInter pt R (pt.regression S A)
| inter {S S' A} :
  IsVariableInter pt R S → IsLiteralInter pt R S' →
  IsRegrInter pt R (pt.regression S A ∩ S')

end Validator.Formalism
