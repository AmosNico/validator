import Validator.StateSetFormalism.Formula

namespace Validator
open Formula

structure BDD n where
  vars : VarSet' n
  -- TODO
  deriving DecidableEq, Repr

namespace BDD

def models {n} (φ : BDD n) : Models n := sorry

instance {n} : Formula n (BDD n) where

  vars φ := φ.vars

  models := models

  models_equiv_right := sorry

instance {n} : Top n (BDD n) where

  top := sorry

  top_correct := sorry

instance {n} : Bot n (BDD n) where

  bot := sorry

  bot_correct := sorry

instance {n} : SententialEntailment n (BDD n) where

  entails := sorry

  entails_correct := sorry

instance {n} : BoundedConjuction n (BDD n) where

  and := sorry

  and_correct := sorry

instance {n} : BoundedDisjunction n (BDD n) where

  or := sorry

  or_correct := sorry

instance {n} : OfPartialModel n (BDD n) where

  ofPartialModel := sorry

  ofPartialModel_correct := sorry

instance {n} : Renaming n (BDD n) where

  rename := sorry

  rename_correct := sorry

end Validator.BDD
