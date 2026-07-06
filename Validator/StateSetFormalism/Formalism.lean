module

public import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.Monotone.Defs


public import Validator.StateSetFormalism.Formula


open Validator.Formula (Model Models Renaming OfPartialModel)
open STRIPS

public section

/-!
All variables `i` have a primed and an unprimed version,
represented by `2 * i + 1` and `2 * i` respectively.
-/

-- TODO : check if this makes sense with namespaces
@[expose]
def Fin.toUnprimed {n} : Fin n → Fin (2 * n) :=
  fun i ↦ ⟨2 * i.val, by omega⟩

@[expose]
def Fin.divNat' {n m} (i : Fin (m * n)) : Fin n :=
  ⟨i / m, Nat.div_lt_of_lt_mul <| i.is_lt⟩

lemma Fin.toUnprimedStrictMono {n} : StrictMono (@toUnprimed n) := by
  simp [toUnprimed, StrictMono]

def Fin.toPrimed {n} (i : Fin (2 * n)) (h : Even i.val) : Fin (2 * n) :=
  ⟨i.val + 1, by grind⟩

namespace STRIPS.VarSet

abbrev IsUnprimed {n} (V : VarSet (2 * n)) : Prop :=
  ∀ i ∈ V, Even i.val

@[simp]
lemma isUnprimed_empty {n} : (∅ : VarSet (2 * n)).IsUnprimed := by
  simp [mem_empty, IsUnprimed]

@[simp]
lemma isUnprimed_union {n} {V V' : VarSet (2 * n)} :
    (V ∪ V').IsUnprimed ↔ V.IsUnprimed ∧ V'.IsUnprimed := by
  grind only [mem_union]

def toUnprimed {n} (V : VarSet n) : VarSet (2 * n) :=
  VarSet.ofFn fun i ↦ Even i.val ∧ i.divNat' ∈ V

lemma mem_toUnprimed {n} {V : VarSet n} {i} :
    i ∈ V.toUnprimed ↔ Even i.val ∧ i.divNat' ∈ V := by
  simp only [toUnprimed, Bool.decide_and, mem_ofFn, Bool.and_eq_true, decide_eq_true_eq]

@[simp]
lemma toUnprimed_mem_toUnprimed_iff {n} {V : VarSet n} {i : Fin n} :
    i.toUnprimed ∈ V.toUnprimed ↔ i ∈ V := by
  simp [mem_toUnprimed, Fin.toUnprimed, Fin.divNat']

lemma isUnprimed_toUnprimed {n} {V : VarSet n} : IsUnprimed (toUnprimed V) := by
  simp [mem_toUnprimed, IsUnprimed]
  grind

def unprimedVars n : VarSet (2 * n) :=
  VarSet.ofFn fun i ↦ Even i.val

lemma mem_unprimedVars {n i} : i ∈ (unprimedVars n) ↔ Even i.val := by
  simp only [unprimedVars, mem_ofFn, decide_eq_true_eq]

lemma isUnprimed_unprimedVars {n} : IsUnprimed (unprimedVars n) := by
  simp [mem_unprimedVars, IsUnprimed]

end STRIPS.VarSet

namespace Validator.Formula.Model

@[expose]
def unprimedState {n} (M : Model (2 * n)) : State n :=
  { i | M i.toUnprimed }

/--
Swap the primed and unprimed versions of the variables in V and
replace the other primed variables with their even version.
-/
def toPrimed {n} (V : VarSet n) (M : Model (2 * n)) : Model (2 * n) :=
  fun i ↦
    if h : ¬Even i.val then
      M ⟨i - 1, by omega⟩
    else if i.divNat' ∈  V then
      M ⟨i + 1, by grind⟩
    else
      M i

lemma toPrimed_eq {n} (V : VarSet n) (M : Model (2 * n)) : M.toPrimed V =
  fun i : Fin (2 * n) ↦
    if h : ¬Even i.val then
      M ⟨i - 1, by omega⟩
    else if i.divNat' ∈  V then
      M ⟨i + 1, by grind⟩
    else
      M i := (rfl)

lemma unprimedState_eq_iff_unprimedVars {n} {M M' : Model (2 * n)} :
    M.unprimedState = M'.unprimedState ↔ ∀ i ∈ (VarSet.unprimedVars n), M i = M' i := by
  simp only [unprimedState, Fin.toUnprimed, Set.ext_iff, Set.mem_setOf_eq,
    VarSet.mem_unprimedVars, eq_iff_iff]
  constructor
  · intro h1 i h2
    specialize h1 i.divNat'
    grind only [Fin.divNat', = Nat.even_iff]
  · grind

lemma exists_model_of_state {n} s : ∃ M : Model (2 * n), s = M.unprimedState := by
  use fun i => ⟨i / 2, by omega⟩ ∈ s
  simp [Model.unprimedState, Fin.toUnprimed]

end Formula.Model

open Formula

class Formalism {n} (pt : PlanningTask n) R extends Formula (2 * n) R where

  toStates (φ : R) : States n := (Formula.models φ).image Model.unprimedState

  toStates_eq (φ : R) : toStates φ = (Formula.models φ).image Model.unprimedState := by simp

-- TODO : only for completeness, remove?
@[simp]
instance {n} {pt : PlanningTask n} : Formalism pt (States n) where

  vars _ := VarSet.unprimedVars n

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

variable {n} {pt : PlanningTask n} {R}

abbrev Variable (pt : PlanningTask n) (R : Type) [Formalism pt R] := R

namespace Variable

@[expose]
def models [Formalism pt R] : Variable pt R → Models (2 * n) :=
  Formula.models

abbrev vars [Formalism pt R] : Variable pt R → VarSet (2 * n) :=
  Formula.vars

@[expose]
def toStates [Formalism pt R] : Variable pt R → States n :=
  Formalism.toStates pt

lemma toStates_eq [Formalism pt R] {x : Variable pt R} :
    x.toStates = x.models.image Model.unprimedState := by
  simp [Variable.toStates, Variable.models, Formalism.toStates_eq]

@[simp]
instance [F : Formalism pt R] : Membership (Fin (2 * n)) (Variable pt R) where

  mem x i := i ∈ x.vars

end Variable

abbrev UnprimedVariable (pt : PlanningTask n) (R : Type) [F : Formalism pt R] :=
  { x : Variable pt R // x.vars.IsUnprimed }

namespace UnprimedVariable

def ofVarSet R [Formalism pt R] [h : OfPartialModel (2 * n) R]
    (V : VarSet n) (pos := true) : UnprimedVariable pt R :=
  let M : PartialModel (2 * n) :=
    if pos then
      ⟨V.toUnprimed, ∅, by simp⟩
    else
      ⟨∅, V.toUnprimed, by simp⟩
  let x : Variable pt R := h.ofPartialModel M
  have hx : x.vars.IsUnprimed := by
    simp only [h.vars_ofPartialModel, x, PartialModel.vars_eq, M]
    split
    all_goals
      simp only [VarSet.IsUnprimed, VarSet.mem_union, VarSet.mem_empty, or_false, false_or]
      exact VarSet.isUnprimed_toUnprimed
  ⟨x, hx⟩

@[simp]
lemma mem_vars_ofVarSet [Formalism pt R] [h : OfPartialModel (2 * n) R] {V pos i} :
    i ∈ (ofVarSet (h := h) R V pos).val.vars ↔ Even i.val ∧ i.divNat' ∈ V := by
  simp [ofVarSet, OfPartialModel.vars_ofPartialModel, PartialModel.vars_eq]
  split
  all_goals simp [VarSet.mem_toUnprimed]

@[simp]
lemma mem_models_ofVarSet [Formalism pt R] [h : OfPartialModel (2 * n) R] {V : VarSet n} {pos M} :
    M ∈ (ofVarSet (h := h) R V pos).val.models ↔ (∀ i ∈ V, i ∈ M.unprimedState ↔ pos):= by
  simp only [Variable.models, ofVarSet, OfPartialModel.models_ofPartialModel,
    PartialModel.mem_models']
  split
  all_goals
    simp_all [Model.unprimedState, VarSet.mem_toUnprimed, Fin.divNat', Fin.toUnprimed]
    grind

lemma mem_models_of_eq_toState [Formalism pt R] {x : UnprimedVariable pt R} {M M' : Model (2 * n)} :
    M.unprimedState = M'.unprimedState → M ∈ x.val.models → M' ∈ x.val.models := by
  rcases x with ⟨x, h1⟩
  intro h2 h3
  have h4 : ∀ i ∈ x, M i = M' i := by
    intro i hi
    simp only [VarSet.IsUnprimed, even_iff_exists_two_mul] at h1
    have ⟨j, hj⟩ := h1 i hi
    simp only [Model.unprimedState, Fin.toUnprimed, Set.ext_iff, Set.mem_setOf_eq] at h2
    have h5 := @h2 ⟨j, by omega⟩
    simp [← hj] at h5
    simp [h5]
  simp only [Variable.models]
  rw [← Formula.models_equiv h4]
  exact h3

lemma mem_models_iff_of_eq_unprimedState [Formalism pt R]
    {x : Variable pt R} {M M' : Model (2 * n)} :
    x.vars.IsUnprimed → M.unprimedState = M'.unprimedState → (M ∈ x.models ↔ M' ∈ x.models) := by
  intro h1 h2
  have := mem_models_of_eq_toState h2 (x := ⟨x, h1⟩)
  have := mem_models_of_eq_toState h2.symm (x := ⟨x, h1⟩)
  grind

def toPrimed [Formalism pt R] [Rename (2 * n) R]
    (x : UnprimedVariable pt R) (V : VarSet n) : Variable pt R :=
  let f := fun i ↦
    if h : Even i.val ∧ i.divNat' ∈ V then
      i.toPrimed h.1
    else
      i
  let dom := VarSet.unprimedVars n
  have h1 : StrictMonoOn f dom := by
    simp only [StrictMonoOn, SetLike.mem_coe, VarSet.mem_unprimedVars, dom]
    simp only [Fin.toPrimed, f, Fin.divNat', ← Fin.val_fin_lt]
    grind
  have h2 : x.val.vars ⊆ dom := by
    intro i hi
    have h1 := x.prop i hi
    simp only [VarSet.mem_unprimedVars, h1, dom]
  Rename.rename x ⟨f, h1⟩ h2

lemma mem_models_toPrimed_iff [Formalism pt R] [Rename (2 * n) R]
    {x : UnprimedVariable pt R} {V M} :
    M ∈ (x.toPrimed V).models ↔ M.toPrimed V ∈ x.val.models := by
  simp only [Variable.models, toPrimed, Rename.mem_rename_models]
  apply Formula.models_equiv
  simp only [Variable.vars, Model.rename, Model.toPrimed_eq, Nat.not_even_iff_odd,
    eq_iff_iff]
  intro i hi
  have h2  := x.prop i hi
  simp only [h2, true_and]
  split
  case _ => simp_all [Fin.toPrimed]
  case _ j h3 => grind

end UnprimedVariable

inductive Literal (pt : PlanningTask n) R [Formalism pt R]
  | pos : Variable pt R → Literal pt R
  | neg : Variable pt R → Literal pt R

namespace Literal

def models [Formalism pt R] : Literal pt R → Models (2 * n)
  | pos X => X.models
  | neg X => X.modelsᶜ

@[expose]
def toStates [Formalism pt R] : Literal pt R → States n
  | pos X => X.toStates
  | neg X => X.toStatesᶜ

@[simp]
lemma models_pos [Formalism pt R] {x : Variable pt R} : (pos x).models = x.models := (rfl)

@[simp]
lemma models_neg [Formalism pt R] {x : Variable pt R} : (neg x).models = x.modelsᶜ := (rfl)

@[simp]
lemma toStates_pos [Formalism pt R] {X : Variable pt R} : (pos X).toStates = X.toStates := (rfl)

@[simp]
lemma toStates_neg [Formalism pt R] {X : Variable pt R} : (neg X).toStates = X.toStatesᶜ := (rfl)

end Literal

inductive UnprimedLiteral (pt : PlanningTask n) R [Formalism pt R]
  | pos : UnprimedVariable pt R → UnprimedLiteral pt R
  | neg : UnprimedVariable pt R → UnprimedLiteral pt R


namespace UnprimedLiteral

@[expose]
def val [Formalism pt R] : UnprimedLiteral pt R → Literal pt R
  | pos x => .pos x.val
  | neg x => .neg x.val

@[simp]
lemma val_pos [Formalism pt R] {x : UnprimedVariable pt R} : (pos x).val = .pos x.val := (rfl)

@[simp]
lemma val_neg [Formalism pt R] {x : UnprimedVariable pt R} : (neg x).val = .neg x.val := (rfl)

lemma toStates_eq [Formalism pt R] : {l : UnprimedLiteral pt R} →
    l.val.toStates = l.val.models.image Model.unprimedState
  | pos x => by
    simp only [Literal.toStates, val_pos, Variable.toStates_eq, Literal.models]
  | neg x => by
    simp only [Literal.toStates, val_neg, Variable.toStates_eq, Literal.models]
    ext s
    simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · have ⟨M, h⟩ := Model.exists_model_of_state s
      grind
    · rintro ⟨M, h1, rfl⟩ M' h2 h3
      rw [UnprimedVariable.mem_models_iff_of_eq_unprimedState x.prop h3] at h2
      contradiction

lemma subset_states_iff_subset_models {R1 R2} [Formalism pt R1] [Formalism pt R2]
    (l1 : UnprimedLiteral pt R1) (l2 : UnprimedLiteral pt R2) :
    l1.val.toStates ⊆ l2.val.toStates ↔ l1.val.models ⊆ l2.val.models := by
  simp only [toStates_eq, Set.image_subset_iff]
  suffices h : Model.unprimedState ⁻¹' (Model.unprimedState '' l2.val.models) = l2.val.models by
    rw [h]
  ext M
  constructor
  · rintro ⟨M', h1, h2⟩
    match l2 with
    | pos x2 =>
      simp only [Literal.models] at h1 ⊢
      exact UnprimedVariable.mem_models_of_eq_toState h2 h1
    | neg x2 =>
      simp only [Literal.models] at h1 ⊢
      intro h3
      apply h1
      exact UnprimedVariable.mem_models_of_eq_toState h2.symm h3
  · grind
end UnprimedLiteral

abbrev Variables (pt : PlanningTask n) R [Formalism pt R] := List (Variable pt R)

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
lemma inter_empty [F : Formalism pt R] : inter (F := F) [] = Set.univ := by
  ext s
  obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
  simp [inter]

@[simp]
lemma inter_single [Formalism pt R] {x : Variable pt R} : (single x).inter = x.toStates := by
  ext s
  simp [List.singleton, single, Variable.toStates, mem_inter, toStates_eq, Variable.models]
  tauto

def union [F : Formalism pt R] (X : Variables pt R) : States n :=
  { s | ∃ M, M.unprimedState = s ∧ ∃ x ∈ X, M ∈ x.models }

lemma mem_union [Formalism pt R] {X : Variables pt R} :
    ∀ s, s ∈ X.union ↔ ∃ M, M.unprimedState = s ∧ ∃ x ∈ X, M ∈ x.models := by
  simp [union]

@[simp]
lemma union_empty [F : Formalism pt R] : union (F := F) [] = ∅ := by
  ext s
  simp [union]

@[simp]
lemma union_single [Formalism pt R] {x : Variable pt R} : (single x).union = x.toStates := by
  ext s
  simp [List.singleton ,single, Variable.toStates, mem_union, toStates_eq, Variable.models]
  tauto

end Variables

abbrev UnprimedVariables (pt : PlanningTask n) R [Formalism pt R] := List (UnprimedVariable pt R)

namespace UnprimedVariables

@[expose]
def val [Formalism pt R] :
  UnprimedVariables pt R → Variables pt R := fun X ↦ X

def single [Formalism pt R] : UnprimedVariable pt R → UnprimedVariables pt R :=
  List.singleton

@[simp]
lemma val_single [Formalism pt R] {x : UnprimedVariable pt R} :
    (single x).val = Variables.single x.val := by
  simp [single, Variables.single, val, List.singleton]

lemma val_append [Formalism pt R] {L1 L2 : UnprimedVariables pt R} :
    (L1 ++ L2).val = L1.val ++ L2.val := by
  simp [val]

@[simp]
lemma union_append [Formalism pt R] {X1 X2 : UnprimedVariables pt R} :
    (X1 ++ X2).val.union = X1.val.union ∪ X2.val.union := by
  ext s
  simp [val, Variables.mem_union]
  grind

@[simp low]
lemma mem_inter [F : Formalism pt R] {X : UnprimedVariables pt R} {s} :
    s ∈ X.val.inter ↔ ∀ x ∈ X, s ∈ x.val.toStates := by
  simp only [val, List.pure_def, List.bind_eq_flatMap, List.flatMap_subtype,
    List.flatMap_singleton', Variables.mem_inter, List.mem_unattach, forall_exists_index,
    Variable.toStates_eq, Subtype.forall]
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
lemma inter_variables_append [Formalism pt R] {X1 : Variables pt R} {X2 : UnprimedVariables pt R} :
    (X1 ++ X2.val).inter = X1.inter ∩ X2.val.inter := by
  ext s
  simp only [val, List.pure_def, List.bind_eq_flatMap, List.flatMap_subtype,
    List.flatMap_singleton', Variables.mem_inter, List.mem_append, List.mem_unattach,
    Set.mem_inter_iff, forall_exists_index]
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
    (X1 ++ X2).val.inter = X1.val.inter ∩ X2.val.inter := by
  simp [val_append]

lemma inter_subset_union_iff_models [F : Formalism pt R]
    (X1 : Variables pt R) (X2 : UnprimedVariables pt R) :
    X1.inter ⊆ X2.val.union ↔ (∀ M, (∀ x ∈ X1, M ∈ F.models x) → ∃ x ∈ X2, M ∈ x.val.models) := by
  simp only [val, List.pure_def, List.bind_eq_flatMap, List.flatMap_subtype,
    List.flatMap_singleton', Set.subset_def, Variables.mem_inter, Variables.mem_union,
    List.mem_unattach, forall_exists_index, and_imp, Subtype.exists, exists_and_right]
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

def toPrimed [F : Formalism pt R] [Rename (2 * n) R]
    (X : UnprimedVariables pt R) (V : VarSet n) : Variables pt R :=
  X.map (UnprimedVariable.toPrimed · V)

lemma mem_inter_toPrimed [F : Formalism pt R] [Rename (2 * n) R]
    {X : UnprimedVariables pt R} {V s} :
    s ∈ (toPrimed X V).inter ↔ ∃ s' ∈ X.val.inter, ∀ i ∉ V, i ∈ s' ↔ i ∈ s := by
  simp only [Variables.inter, toPrimed, List.mem_map, Subtype.exists, forall_exists_index,
    and_imp, Set.mem_setOf_eq, val, List.pure_def, List.bind_eq_flatMap, List.flatMap_subtype,
    List.flatMap_singleton', List.mem_unattach, ↓existsAndEq, true_and]
  constructor
  · rintro ⟨M, rfl, h1⟩
    use Model.toPrimed V M
    constructor
    · intro x h2 h3
      specialize h1 (UnprimedVariable.toPrimed ⟨x, h2⟩ V) x h2 h3 rfl
      simp only [UnprimedVariable.mem_models_toPrimed_iff] at h1
      exact h1
    · simp [Model.toPrimed_eq, Model.unprimedState, Fin.toUnprimed, Fin.divNat']
      grind
  · rintro ⟨M, h1, h2⟩
    -- Take unprimed variables from `s` and primed variables from `M.unprimedState`
    use fun i ↦
      if Even i.val then
        ⟨i / 2, by omega⟩ ∈ s
      else
        ⟨i / 2, by omega⟩ ∈ M.unprimedState
    simp only [Model.unprimedState, Fin.toUnprimed, even_two, Even.mul_right, ↓reduceIte, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, Fin.eta, Set.setOf_mem_eq,
      Set.mem_setOf_eq, true_and]
    intro _ x h3 h4 rfl
    simp only [UnprimedVariable.mem_models_toPrimed_iff]
    specialize h1 x h3 h4
    refine Formula.models_equiv_right _ _ _ ?_ h1
    intro ⟨i, hi⟩ h5
    have h6 := h3 ⟨i, hi⟩ h5
    simp [Model.toPrimed_eq, h6, Nat.even_add_one]
    simp only [even_iff_exists_two_mul] at h6
    rcases h6 with ⟨j, rfl⟩
    simp_all [Model.unprimedState, Fin.toUnprimed, Fin.divNat']
    grind

end UnprimedVariables

-- TODO : check if needed, or if everything can be done in terms of `UnprimedLiterals`
abbrev Literals (pt : PlanningTask n) R [Formalism pt R] :=
  Variables pt R × Variables pt R

-- TODO : write in terms of `Variables`?
namespace Literals

def pos [Formalism pt R] (X : Variables pt R) : Literals pt R :=
  (X, [])

@[simps]
instance [Formalism pt R] : Append (Literals pt R) where
  append L1 L2 := (L1.1 ++ L2.1, L1.2 ++ L2.2)

@[simp]
lemma append_pos [Formalism pt R] {L1 L2 : Literals pt R} : (L1 ++ L2).1 = L1.1 ++ L2.1 := by
  simp only [append_def]

@[simp]
lemma append_neg [Formalism pt R] {L1 L2 : Literals pt R} : (L1 ++ L2).2 = L1.2 ++ L2.2 := by
  simp only [append_def]

def union [Formalism pt R] (L : Literals pt R) : States n :=
  { s | ∃ M : Model (2 * n), M.unprimedState = s ∧
    ((∃ x ∈ L.1, M ∈ x.models) ∨ (∃ x ∈ L.2, M ∉ x.models)) }

@[simp]
lemma mem_union [Formalism pt R] {ls : Literals pt R} {s} :
    s ∈ ls.union ↔ ∃ M : Model (2 * n), M.unprimedState = s ∧
    ((∃ x ∈ ls.1, M ∈ x.models) ∨ (∃ x ∈ ls.2, M ∉ x.models)) := by
  simp only [union, Set.mem_setOf_eq]

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
    (∀ x ∈ L.1, M ∈ x.models) ∧ (∀ x ∈ L.2, M ∉ x.models) := by
  simp only [inter, Set.mem_setOf_eq]

end Literals

abbrev UnprimedLiterals (pt : PlanningTask n) R [Formalism pt R] :=
  UnprimedVariables pt R × UnprimedVariables pt R

namespace UnprimedLiterals

def val [Formalism pt R] :
  UnprimedLiterals pt R → Literals pt R := fun (X, X') ↦ (X, X')

@[simp]
abbrev empty [Formalism pt R] :  UnprimedLiterals pt R := ([], [])

def single [Formalism pt R] : UnprimedLiteral pt R → UnprimedLiterals pt R
  | .pos x => ([x], [])
  | .neg x => ([], [x])

@[simp]
lemma union_single [Formalism pt R] {l : UnprimedLiteral pt R} :
    (single l).val.union = l.val.toStates := by
  simp only [single, UnprimedLiteral.toStates_eq]
  split
  all_goals
    ext s
    simp [UnprimedLiterals.val, Literal.models]
    grind

@[simp]
lemma inter_single [Formalism pt R] {l : UnprimedLiteral pt R} :
    (single l).val.inter = l.val.toStates := by
  simp only [single, UnprimedLiteral.toStates_eq]
  split
  all_goals
    ext s
    simp [UnprimedLiterals.val, Literal.models]
    grind

@[simps]
instance [Formalism pt R] : Append (UnprimedLiterals pt R) where
  append L1 L2 := (L1.1 ++ L2.1, L1.2 ++ L2.2)

@[simp low]
lemma val_append [Formalism pt R] {L1 L2 : UnprimedLiterals pt R} :
    (L1 ++ L2).val = L1.val ++ L2.val := by
  simp [val]

open UnprimedVariable (mem_models_iff_of_eq_unprimedState)

@[simp low]
lemma union_val [Formalism pt R] {L : UnprimedLiterals pt R} :
    L.val.union = L.1.val.union ∪ L.2.val.interᶜ := by
  ext s
  simp only [val, List.pure_def, List.bind_eq_flatMap, List.flatMap_subtype,
    List.flatMap_singleton', Literals.mem_union, List.mem_unattach, Variable.models,
    UnprimedVariables.val, Set.mem_union, Variables.mem_union, Set.mem_compl_iff,
    Variables.mem_inter, forall_exists_index, not_exists, not_and, not_forall]
  constructor
  · rintro ⟨M, rfl, h1⟩
    rcases h1 with ⟨x, ⟨h1, h2⟩, h3⟩ | ⟨x, ⟨h1, h2⟩, h3⟩
    · grind
    · apply Or.inr
      intro M' h4
      have h5:= mem_models_iff_of_eq_unprimedState h1 h4
      simp only [Variable.models] at h5
      grind
  · intro h
    rcases h with h | h
    · grind
    · obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
      grind

@[simp low]
lemma inter_val [Formalism pt R] {L : UnprimedLiterals pt R} :
    L.val.inter = L.1.val.inter ∩ L.2.val.unionᶜ := by
  ext s
  simp only [val, List.pure_def, List.bind_eq_flatMap, List.flatMap_subtype,
    List.flatMap_singleton', Literals.mem_inter, List.mem_unattach, forall_exists_index,
    UnprimedVariables.val, Set.mem_inter_iff, Variables.mem_inter, Set.mem_compl_iff,
    Variables.mem_union, not_exists, not_and]
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
    (L1.val ++ L2.val).inter = L1.val.inter ∩ L2.val.inter := by
  ext s
  simp only [val, List.pure_def, List.bind_eq_flatMap, List.flatMap_subtype,
    List.flatMap_singleton', Literals.mem_inter, Literals.append_pos, List.mem_append,
    List.mem_unattach, Literals.append_neg, Set.mem_inter_iff, forall_exists_index]
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

inductive IsVariable {n} (pt : PlanningTask n) R [Formalism pt R] : States n → Prop
  | empty : IsVariable pt R ∅
  | init : IsVariable pt R {pt.init}
  | goal : IsVariable pt R pt.goal_states
  | explicit (φ : R) : IsVariable pt R (Formalism.toStates pt φ)

inductive IsLiteral {n} (pt : PlanningTask n) R [Formalism pt R] : States n → Prop
  | pos {S} : IsVariable pt R S → IsLiteral pt R S
  | neg {S} : IsVariable pt R S → IsLiteral pt R (Sᶜ)

inductive IsLiteralUnion {n} (pt : PlanningTask n) R [Formalism pt R] : States n → Prop
  | single {S} : IsLiteral pt R S → IsLiteralUnion pt R S
  | union {S S'} : IsLiteralUnion pt R S → IsLiteralUnion pt R S' → IsLiteralUnion pt R (S ∪ S')

inductive IsVariableInter {n} (pt : PlanningTask n) R [Formalism pt R] : States n → Prop
  | single {S} : IsVariable pt R S → IsVariableInter pt R S
  | inter {S S'} : IsVariableInter pt R S → IsVariableInter pt R S' → IsVariableInter pt R (S ∩ S')

inductive IsLiteralInter {n} (pt : PlanningTask n) R [Formalism pt R] : States n → Prop
  | single {S} : IsLiteral pt R S → IsLiteralInter pt R S
  | inter {S S'} : IsLiteralInter pt R S → IsLiteralInter pt R S' → IsLiteralInter pt R (S ∩ S')

-- TODO : check whether it should be enforced that A ⊆ pt.actions
inductive IsProgrInter {n} (pt : PlanningTask n) R [Formalism pt R] : States n → Prop
  | empty {S A} : IsVariableInter pt R S → IsProgrInter pt R (pt.progression S A)
  | inter {S S' A} :
    IsVariableInter pt R S → IsLiteralInter pt R S' →
    IsProgrInter pt R (pt.progression S A ∩ S')

-- TODO : check whether it should be enforced that A ⊆ pt.actions
inductive IsRegrInter {n} (pt : PlanningTask n) R [Formalism pt R] : States n → Prop
  | empty {S A} : IsVariableInter pt R S → IsRegrInter pt R (pt.regression S A)
  | inter {S S' A} :
    IsVariableInter pt R S → IsLiteralInter pt R S' →
    IsRegrInter pt R (pt.regression S A ∩ S')

end Validator.Formalism
