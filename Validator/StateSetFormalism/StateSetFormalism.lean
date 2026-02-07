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

--TODO
def mkBDD {n} (pt : STRIPS n) : UnprimedVariable pt (BDD (2 * n)) :=
  ⟨BDD.mk (VarSet'.unprimedVars n), VarSet'.isUnprimed_unprimedVars⟩

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
  ⟨bot (2 * n), by simp only [bot_correct]; exact VarSet'.isUnprimed_empty⟩

@[simp]
lemma toStates_mkEmpty : (mkEmpty pt R).val.toStates = ∅ :=
  by
    simp [mkEmpty, Variable.toStates_eq, Variable.models,  bot_correct]

def mkInit : UnprimedVariable' pt R :=
  let M : PartialModel (2 * n) := {
    pos := VarSet'.toUnprimed pt.init'
    neg := VarSet'.toUnprimed (~~~pt.init')
    disjoint := by
      simp only [VarSet'.Disjoint_iff, VarSet'.instMembershipFin, VarSet'.toUnprimed]
      grind
  }
  ⟨
    ofPartialModel M,
    by
      simp only [VarSet'.IsUnprimed, VarSet'.instMembershipFin, VarSet'.toUnprimed, Bool.decide_and,
        Bool.decide_eq_true, ofPartialModel_correct, PartialModel.vars', VarSet'.mem_union, M];
      grind
  ⟩

@[simp]
lemma toStates_mkInit : (mkInit pt R).val.toStates = {pt.init} :=
  by
    ext s
    simp only [mkInit, Variable.toStates_eq, Variable.models, ofPartialModel_correct,
      PartialModel.models, Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    simp only [VarSet'.instMembershipFin, Fin.getElem_fin, VarSet'.mem_toUnprimed, Fin.divNat',
      and_imp, BitVec.getElem_not, Bool.not_eq_eq_eq_not, Bool.not_true, Model.unprimedState,
      Fin.toUnprimed]
    simp only [STRIPS.init, convertState]
    constructor
    · rintro ⟨M, ⟨h1, h2⟩, rfl⟩
      ext i
      specialize h1 ⟨2 * i, by omega⟩ (by simp)
      specialize h2 ⟨2 * i, by omega⟩ (by simp)
      grind
    · intro rfl
      obtain ⟨M, h⟩ := Model.exists_model_of_state pt.init
      use M
      simp [STRIPS.init, convertState, Model.unprimedState, Fin.toUnprimed, Set.ext_iff] at h
      split_ands
      · grind
      · grind
      · grind

def mkGoal : UnprimedVariable' pt R :=
  UnprimedVariable.ofVarset' (R.type pt) pt.goal'

@[simp]
lemma toStates_mkGoal : (mkGoal pt R).val.toStates = pt.goal_states :=
  by
    ext s
    simp only [mkGoal, Variable.toStates_eq, Set.mem_image, UnprimedVariable.mem_models_ofVarSet',
      iff_true, Model.unprimedState, Fin.toUnprimed, Set.mem_setOf_eq]
    simp only [STRIPS.goal_states, STRIPS.GoalState, VarSet'.toVarSet, Set.mem_setOf_eq]
    constructor
    · grind
    · intro h
      obtain ⟨M, rfl⟩ := Model.exists_model_of_state s
      use M
      simp [Model.unprimedState, Fin.toUnprimed] at h
      grind

end Validator.StateSetFormalism
