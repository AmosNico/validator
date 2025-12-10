import Validator.StateSetFormalism.StateSetFormalism

namespace Validator
open Formalism (UnprimedVariable)

inductive ActionSetExpr : Type
| enum : List ℕ → ActionSetExpr
| union : ℕ → ℕ → ActionSetExpr
| all : ActionSetExpr
  deriving Repr

def ActionSetExpr.toSting : ActionSetExpr → String
| enum as => s!"the action set containing the actions with ids {as}"
| union Aᵢ A'ᵢ => s!"the union of the action sets #{Aᵢ} and #{A'ᵢ}"
| all => "the constant set of all actions"

instance : ToString ActionSetExpr where
  toString := ActionSetExpr.toSting

inductive StateSetExpr {n} (pt : STRIPS n) : Type
| empty : StateSetExpr pt
| init : StateSetExpr pt
| goal : StateSetExpr pt
| bdd : UnprimedVariable pt (BDD (2 * n)) → StateSetExpr pt
| horn : UnprimedVariable pt (Horn (2 * n)) → StateSetExpr pt
| mods : UnprimedVariable pt (MODS (2 * n)) → StateSetExpr pt
| neg : ℕ → StateSetExpr pt
| inter : ℕ → ℕ → StateSetExpr pt
| union : ℕ → ℕ → StateSetExpr pt
| progr : ℕ → ℕ → StateSetExpr pt
| regr : ℕ → ℕ → StateSetExpr pt
  deriving DecidableEq, Repr

def StateSetExpr.toString {n} {pt : STRIPS n} : StateSetExpr pt → String
| empty => "the constant empty set"
| init => "the constant set containing the initial state"
| goal => "the constant goal set"
| bdd _ => "a BDD state set"
| horn _ => "a horn state set"
| mods _ => "a MODS state set"
| neg Sᵢ => s!"the negation of the state set #{Sᵢ}"
| inter Sᵢ S'ᵢ => s!"the intersection of the state sets #{Sᵢ} and #{S'ᵢ}"
| union Sᵢ S'ᵢ => s!"the union of the state sets #{Sᵢ} and #{S'ᵢ}"
| progr Sᵢ Aᵢ => s!"the progression of the state set #{Sᵢ} with the action set #{Aᵢ}"
| regr Sᵢ Aᵢ => s!"the regression of the state set #{Sᵢ} with the action set #{Aᵢ}"

instance {n} {pt : STRIPS n} : ToString (StateSetExpr pt) where
  toString := StateSetExpr.toString

inductive DeadKnowledge : ℕ → Type
/-- Empty set Dead -/
| ED Sᵢ : DeadKnowledge Sᵢ
/-- Union Dead -/
| UD Sᵢ: ℕ → ℕ → DeadKnowledge Sᵢ
/-- Subset Dead -/
| SD Sᵢ: ℕ → ℕ → DeadKnowledge Sᵢ
/-- Progression Goal -/
| PG Sᵢ: ℕ → ℕ → ℕ → DeadKnowledge Sᵢ
/-- Progression Initial -/
| PI Sᵢ: ℕ → ℕ → ℕ → DeadKnowledge Sᵢ
/-- Regression Goal -/
| RG Sᵢ: ℕ → ℕ → ℕ → DeadKnowledge Sᵢ
/-- Regression Initial -/
| RI Sᵢ: ℕ → ℕ → ℕ → DeadKnowledge Sᵢ
  deriving Repr

inductive StateSubsetKnowledge : ℕ → ℕ → Type
/-- Basic statement 1 -/
| B1 Sᵢ S'ᵢ : StateSubsetKnowledge Sᵢ S'ᵢ
/-- Basic statement 2 -/
| B2 Sᵢ S'ᵢ : StateSubsetKnowledge Sᵢ S'ᵢ
/-- Basic statement 3 -/
| B3 Sᵢ S'ᵢ : StateSubsetKnowledge Sᵢ S'ᵢ
/-- Basic statement 4 -/
| B4 Sᵢ S'ᵢ : StateSubsetKnowledge Sᵢ S'ᵢ
/-- Union Right State -/
| URS Sᵢ S'ᵢ : StateSubsetKnowledge Sᵢ S'ᵢ
/-- Union Left State -/
| ULS Sᵢ S'ᵢ : StateSubsetKnowledge Sᵢ S'ᵢ
/-- Intersection Right State -/
| IRS Sᵢ S'ᵢ : StateSubsetKnowledge Sᵢ S'ᵢ
/-- Intersection Left State -/
| ILS Sᵢ S'ᵢ : StateSubsetKnowledge Sᵢ S'ᵢ
/-- DIstributivity State -/
| DIS Sᵢ S'ᵢ : StateSubsetKnowledge Sᵢ S'ᵢ
/-- Subset Union State -/
| SUS Sᵢ S'ᵢ : ℕ → ℕ → StateSubsetKnowledge Sᵢ S'ᵢ
/-- Subset Intersection State -/
| SIS Sᵢ S'ᵢ : ℕ → ℕ → StateSubsetKnowledge Sᵢ S'ᵢ
/-- Subset Transitivity State -/
| STS Sᵢ S'ᵢ : ℕ → ℕ → StateSubsetKnowledge Sᵢ S'ᵢ
/-- Action Transitivity -/
| AT Sᵢ S'ᵢ : ℕ → ℕ → StateSubsetKnowledge Sᵢ S'ᵢ
/-- Action Union -/
| AU Sᵢ S'ᵢ : ℕ → ℕ → StateSubsetKnowledge Sᵢ S'ᵢ
/-- Progression Transitivity -/
| PT Sᵢ S'ᵢ : ℕ → ℕ → StateSubsetKnowledge Sᵢ S'ᵢ
/-- Progression Union -/
| PU Sᵢ S'ᵢ : ℕ → ℕ → StateSubsetKnowledge Sᵢ S'ᵢ
/-- Progression to Regression -/
| PR Sᵢ S'ᵢ : ℕ → StateSubsetKnowledge Sᵢ S'ᵢ
/-- Regression to Progression -/
| RP Sᵢ S'ᵢ : ℕ → StateSubsetKnowledge Sᵢ S'ᵢ
  deriving Repr

inductive ActionSubsetKnowledge : ℕ → ℕ → Type
/-- Basic statement 5 -/
| B5 Aᵢ A'ᵢ : ActionSubsetKnowledge Aᵢ A'ᵢ
/-- Union Right Action -/
| URA Aᵢ A'ᵢ : ActionSubsetKnowledge Aᵢ A'ᵢ
/-- Union Left Action -/
| ULA Aᵢ A'ᵢ : ActionSubsetKnowledge Aᵢ A'ᵢ
/-- Subset Union Action -/
| SUA Aᵢ A'ᵢ : ℕ → ℕ → ActionSubsetKnowledge Aᵢ A'ᵢ
/-- Subset Transitivity Action -/
| STA Aᵢ A'ᵢ : ℕ → ℕ → ActionSubsetKnowledge Aᵢ A'ᵢ
  deriving Repr

inductive UnsolvableKnowledge
/-- Conclusion Initial -/
| CI : ℕ → UnsolvableKnowledge
/-- Conclusion Goal -/
| CG : ℕ → UnsolvableKnowledge
  deriving Repr

inductive Knowledge
| dead Sᵢ : DeadKnowledge Sᵢ → Knowledge
| actionSubset Aᵢ A'ᵢ : ActionSubsetKnowledge Aᵢ A'ᵢ → Knowledge
| stateSubset Sᵢ S'ᵢ : StateSubsetKnowledge Sᵢ S'ᵢ → Knowledge
| unsolvable : UnsolvableKnowledge → Knowledge
  deriving Repr

instance : ToString Knowledge where
  toString _ := "TODO"

structure Certificate {n} (pt : STRIPS n) where
  actions : Array ActionSetExpr
  states : Array (StateSetExpr pt)
  knowledge : Array Knowledge
  deriving Repr

-- TODO : improve
instance {n} {pt : STRIPS n} : ToString (Certificate pt) where
  toString C := s!"Actions:\n{C.actions}\nStates:\n{C.states}\nKnowledge:\n{C.knowledge}\n"

end Validator
