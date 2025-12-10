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
  | bdd => "bdd"
  | horn => "horn"
  | mods => "mods"

abbrev type {n} (_ : STRIPS n) : StateSetFormalism → Type
| bdd => BDD (2 * n)
| horn => Horn (2 * n)
| mods => MODS (2 * n)

instance Horn.instFormalism {n} {pt : STRIPS n} : Formalism pt (Horn (2 * n)) where

instance MODS.instFormalism {n} {pt : STRIPS n} : Formalism pt (MODS (2 * n)) where

instance BDD.instFormalism {n} {pt : STRIPS n} : Formalism pt (BDD (2 * n)) where

--TODO
def mkUnprimed {n} (pt : STRIPS n) : UnprimedVariable pt (BDD (2 * n)) :=
  ⟨BDD.mk (VarSet'.unprimedVars n), VarSet'.isUnprimed_unprimedVars⟩


instance {n} {pt : STRIPS n} : {R : StateSetFormalism} → Formalism pt (R.type pt)
| bdd => BDD.instFormalism
| horn => Horn.instFormalism
| mods => MODS.instFormalism

instance {n} {pt : STRIPS n} : {R : StateSetFormalism} → Formula.Bot (2 * n) (R.type pt)
| bdd => BDD.instBot
| horn => Horn.instBot
| mods => MODS.instBot

instance {n} {pt : STRIPS n} : {R : StateSetFormalism} → Formula.OfPartialModel (2 * n) (R.type pt)
| bdd => BDD.instOfPartialModel
| horn => Horn.instOfPartialModel
| mods => MODS.instOfPartialModel

instance {n} {pt : STRIPS n} : {R : StateSetFormalism} → Formula.Renaming (2 * n) (R.type pt)
| bdd => BDD.instRenaming
| horn => Horn.instRenaming
| mods => MODS.instRenaming

open Formalism Formula.Bot Formula.OfPartialModel
variable {n} (pt : STRIPS n) (R : StateSetFormalism)

abbrev Variable' := Variable pt (R.type pt)
abbrev UnprimedVariable' := UnprimedVariable pt (R.type pt)
abbrev Literal' := Literal pt (R.type pt)
abbrev UnprimedLiteral' := UnprimedLiteral pt (R.type pt)
abbrev Variables' := Variables pt (R.type pt)
abbrev UnprimedVariables' := UnprimedVariables pt (R.type pt)
abbrev Literals' := Literals pt (R.type pt)
abbrev UnprimedLiterals' := UnprimedLiterals pt (R.type pt)

def mkEmpty : UnprimedVariable' pt R :=
  ⟨bot (2 * n), by simp [bot_correct]; exact VarSet'.isUnprimed_empty⟩

@[simp]
lemma toStates_mkEmpty : (mkEmpty pt R).val.toStates = ∅ :=
  by
    simp [mkEmpty, Variable.toStates_eq, Variable.models,  bot_correct]

def mkInit : UnprimedVariable' pt R :=
  ⟨
    ofPartialModel (VarSet'.unprimedVars n) (pt.init'.cast (by simp [VarSet'.unprimedVars])),
    by simp [ofPartialModel_correct]; exact VarSet'.isUnprimed_unprimedVars
  ⟩

@[simp]
lemma toStates_mkInit : (mkInit pt R).val.toStates = {pt.init} :=
  by
    ext s
    simp only [mkInit, Variable.toStates_eq, Variable.models, ofPartialModel_correct]
    simp [PartialModel.models, Model.unprimedState, VarSet'.unprimedVars, Fin.toUnprimed]
    simp [STRIPS.init, convertState]
    constructor
    · grind
    · intro rfl
      obtain ⟨M, h⟩ := Model.exists_model_of_state pt.init
      use M
      simp [STRIPS.init, convertState, Model.unprimedState, Fin.toUnprimed, Set.ext_iff] at h
      grind

def mkGoal : UnprimedVariable' pt R :=
  ⟨
    ofPartialModel pt.goal'.toUnprimed (BitVec.allOnes _),
    by simp [ofPartialModel_correct]; exact VarSet'.isUnprimed_toUnprimed
  ⟩

@[simp]
lemma toStates_mkGoal : (mkGoal pt R).val.toStates = pt.goal_states :=
  by
    ext s
    simp only [mkGoal, Variable.toStates_eq, Variable.models, ofPartialModel_correct]
    simp [PartialModel.models, Model.unprimedState, VarSet'.toUnprimed, Fin.toUnprimed]
    simp [STRIPS.goal_states, STRIPS.GoalState, convertVarSet]
    constructor
    · rintro ⟨M, h, rfl⟩
      simp []
      intro i hi
      obtain ⟨j, h2, rfl⟩ := List.getElem_of_mem hi
      exact h ⟨j, by simp [h2]⟩
    · intro h
      obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
      use M
      simp [Model.unprimedState, Fin.toUnprimed] at h
      grind

end Validator.StateSetFormalism
