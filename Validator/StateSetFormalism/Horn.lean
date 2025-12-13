import Validator.StateSetFormalism.Formula

namespace Validator
open Formula

structure Horn n where
  vars : VarSet' n
  -- TODO
  deriving DecidableEq, Repr

namespace Horn

def models {n} (φ : Horn n) : Models n := sorry

instance {n} : Formula n (Horn n) where

  vars φ := φ.vars

  models := models

  models_equiv_right := sorry

instance {n} : Top n (Horn n) where

  top := sorry

  top_correct := sorry

instance {n} : Bot n (Horn n) where

  bot := sorry

  bot_correct := sorry

instance {n} : ClausalEntailment n (Horn n) where

  entails := sorry

  entails_correct := sorry

instance {n} : BoundedConjuction n (Horn n) where

  and := sorry

  and_correct := sorry

instance {n} : OfPartialModel n (Horn n) where

  ofPartialModel := sorry

  ofPartialModel_correct := sorry

instance {n} : Renaming n (Horn n) where

  rename := sorry

  rename_correct := sorry

instance {n} : ToCNF n (Horn n) where

  toCNF := sorry

  toCNF_correct := sorry

end Validator.Horn
