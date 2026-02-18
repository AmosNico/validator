import Validator.StateSetFormalism.Formalism
import Validator.StateSetFormalism.Bdd
import Validator.StateSetFormalism.Horn
import Validator.StateSetFormalism.Mods

namespace Validator
open Formula
open Formalism (UnprimedVariable)

inductive StateSetFormalism
| bdd
| horn
| mods
  deriving DecidableEq

namespace StateSetFormalism

instance : ToString StateSetFormalism where

  toString
  | bdd => "BDD"
  | horn => "Horn"
  | mods => "MODS"

abbrev type {n} (_ : STRIPS n) : StateSetFormalism → Type
| bdd => BDD (2 * n)
| horn => Horn (2 * n)
| mods => MODS (2 * n)

instance BDD.instFormalism {n} {pt : STRIPS n} : Formalism pt (BDD (2 * n)) where

instance Horn.instFormalism {n} {pt : STRIPS n} : Formalism pt (Horn (2 * n)) where

instance MODS.instFormalism {n} {pt : STRIPS n} : Formalism pt (MODS (2 * n)) where

instance {n} {pt : STRIPS n} : {R : StateSetFormalism} → Formalism pt (R.type pt)
| bdd => BDD.instFormalism
| horn => Horn.instFormalism
| mods => MODS.instFormalism

instance {n} {pt : STRIPS n} : {R : StateSetFormalism} → Formula.Bot (2 * n) (R.type pt)
| bdd => BDD.instBot
| horn => Horn.instBot
| mods => MODS.instBot

instance {n} {pt : STRIPS n} :
  {R : StateSetFormalism} → Formula.ClausalEntailment (2 * n) (R.type pt)
| bdd => BDD.instClausalEntailment
| horn => Horn.instClausalEntailment
| mods => MODS.instClausalEntailment

instance {n} {pt : STRIPS n} : {R : StateSetFormalism} → Formula.Implicant (2 * n) (R.type pt)
| bdd => BDD.instImplicant
| horn => Horn.instImplicant
| mods => MODS.instImplicant

-- TODO : remove?
instance {n} {pt : STRIPS n} :
  {R : StateSetFormalism} → Formula.SententialEntailment (2 * n) (R.type pt)
| bdd => BDD.instSententialEntailment
| horn => Horn.instSententialEntailment
| mods => MODS.instSententialEntailment

instance {n} {pt : STRIPS n} : {R : StateSetFormalism} → Formula.OfPartialModel (2 * n) (R.type pt)
| bdd => BDD.instOfPartialModel
| horn => Horn.instOfPartialModel
| mods => MODS.instOfPartialModel

instance {n} {pt : STRIPS n} : {R : StateSetFormalism} → Formula.Rename (2 * n) (R.type pt)
| bdd => BDD.instRename
| horn => Horn.instRename
| mods => MODS.instRename

open Formalism Formula.Bot Formula.OfPartialModel
variable {n} (pt : STRIPS n) (R : StateSetFormalism)

abbrev UnprimedVariable' := UnprimedVariable pt (R.type pt)
abbrev UnprimedLiteral' := UnprimedLiteral pt (R.type pt)
abbrev Variables' := Variables pt (R.type pt)
abbrev UnprimedVariables' := UnprimedVariables pt (R.type pt)
abbrev UnprimedLiterals' := UnprimedLiterals pt (R.type pt)

def mkEmpty : UnprimedVariable' pt R :=
  ⟨bot (2 * n), by simp only [bot_correct]; exact VarSet.isUnprimed_empty⟩

@[simp]
lemma toStates_mkEmpty : (mkEmpty pt R).val.toStates = ∅ :=
  by
    simp [mkEmpty, Variable.toStates_eq, Variable.models,  bot_correct]

def mkInit : UnprimedVariable' pt R :=
  let M : PartialModel (2 * n) := {
    pos := VarSet.toUnprimed pt.init'
    neg := VarSet.toUnprimed pt.init'ᶜ
    disjoint := by
      grind only [VarSet.inter_eq_empty_iff, VarSet.mem_toUnprimed, VarSet.mem_compl]
  }
  ⟨
    ofPartialModel M,
    by
      grind only [!ofPartialModel_correct, PartialModel.vars, VarSet.mem_union,
        VarSet.mem_toUnprimed];
  ⟩

@[simp]
lemma toStates_mkInit : (mkInit pt R).val.toStates = {pt.init} :=
  by
    ext s
    simp only [mkInit, Variable.toStates_eq, Variable.models, ofPartialModel_correct,
      PartialModel.models, Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    simp only [VarSet.mem_toUnprimed, Fin.divNat', and_imp, VarSet.mem_compl, Model.unprimedState,
      Fin.toUnprimed]
    simp only [STRIPS.init]
    constructor
    · rintro ⟨M, ⟨h1, h2⟩, rfl⟩
      ext i
      specialize h1 ⟨2 * i, by omega⟩ (by simp)
      specialize h2 ⟨2 * i, by omega⟩ (by simp)
      simp at *
      grind
    · intro rfl
      obtain ⟨M, h⟩ := Model.exists_model_of_state pt.init
      use M
      simp [STRIPS.init, Model.unprimedState, Fin.toUnprimed, Set.ext_iff] at h
      simp only [Set.ext_iff, Set.mem_setOf_eq, SetLike.mem_coe]
      grind only [= Nat.even_iff]

def mkGoal : UnprimedVariable' pt R :=
  UnprimedVariable.ofVarSet (R.type pt) pt.goal'

@[simp]
lemma toStates_mkGoal : (mkGoal pt R).val.toStates = pt.goal_states :=
  by
    ext s
    simp only [mkGoal, Variable.toStates_eq, Set.mem_image, UnprimedVariable.mem_models_ofVarSet,
      iff_true, Model.unprimedState, Fin.toUnprimed, Set.mem_setOf_eq]
    simp only [STRIPS.goal_states, STRIPS.GoalState, Set.subset_def, SetLike.mem_coe,
      Set.mem_setOf_eq]
    constructor
    · grind only [usr Set.mem_setOf_eq]
    · intro h
      obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
      use M
      grind only [Model.unprimedState, usr Set.mem_setOf_eq]

end Validator.StateSetFormalism
