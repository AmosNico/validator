/- TODO : Copyright -/

import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Sort

namespace Validator

/-!
# Core definitions for the STRIPS formalism

We define some basic definitions of the STRIPS formalism for automated planning (TODO : cite).
This file only contains the definitions that belong to the trusted core of the project,
i.e. definitions that are needed to define planning problems themselves and unsolvability
of planning problems. Additional definitions can be found in `Validator.PlanningTask.Basic`.

## Implementation Notes

Some definitions in this file have two version:
* an primed version which uses a representation that is efficient for
representing instances at run-time, and
* an unprimed version which is more suited for theoretical results (usually using `Finset`).

Exceptions are `Action` and `STRIPS` which can be used for both purposes.
-/

/-! ### Sets of variables

Variables have type `Fin n`, and sets of variables therefore have type `Finset(Fin n)`.
At runtime we use an `Array` instead of `Finset`.
-/

abbrev VarSet n := Set (Fin n)

abbrev VarSet' n := { vars : List (Fin n) // vars.Sorted (· < ·) }

def convertVarSet {n} (V : VarSet' n) : VarSet n :=
  V.val.toFinset

/-! ### States and sets of states

From a theoretical perspective states are just set of variables, but at runtime they are represented
by a vector with boolean values to indicate which variables are in the set.

TODO : sets of states at runtime
-/

abbrev State n := Set (Fin n)

-- TODO : use BitVec
abbrev State' n := BitVec n

abbrev States n := Set (State n)

def convertState {n} (s' : State' n) : State n :=
  { i | s'[i] }

/-! ### Actions and sets of actions -/

/-- Actions in the STRIPS formalism -/
structure Action n where
  /-- The name of the action. -/
  name : String
  /-- The preconditions of the action. See `Action.pre` for the version using `VarSet`. -/
  pre' : VarSet' n
  /-- The adding effects of the action. See `Action.add` for the version using `VarSet`. -/
  add' : VarSet' n
  /-- The deleting effects of the action. See `Action.pre` for the version using `VarSet`. -/
  del' : VarSet' n
  /-- The cost of the action. -/
  cost : ℕ
  deriving Repr, DecidableEq

namespace Action

def pre {n} (a : Action n) : VarSet n := convertVarSet a.pre'

def add {n} (a : Action n) : VarSet n := convertVarSet a.add'

def del {n} (a : Action n) : VarSet n := convertVarSet a.del'

end Action

abbrev Actions n := Set (Action n)

abbrev Actions' n := List (Action n)

/-! ### Applicability and successor states -/

/-- An action is applicable in a state if all its preconditions are true in the state. -/
abbrev Applicable {n} (s : State n) (a : Action n) : Prop := a.pre ⊆ s

/--
If an action `a` is applicable in a state `s`,
then `s[a] := (s \ a.del) ∪ a.add` is the successor of `s`.
-/
abbrev Successor {n} (a : Action n) (s s' : State n) : Prop :=
  Applicable s a ∧ s' = (s \ a.del) ∪ a.add

/-! ### STRIPS planning problems -/
/--
A planning problem in the STRIPS formalism. The variables of the planning task are all elements of
`Fin n`.
-/
structure STRIPS n where
  /-- The names of the variables. -/
  varNames : Vector String n
  /-- The actions of the planning problem. See `STRIPS.actions` for the version using `Actions`. -/
  actions' : Actions' n
  /--
  The initial state of the planning problem.
  See `STRIPS.init` for the version using `State`.
  -/
  init' : State' n
  /--
  The goal of the planning problem, indicating which variables need to be true in a goal state.
  See also `GoalState` and `STRIPS.goal_states` in `Validator.PlanningTask.Basic`.
  -/
  goal' : VarSet' n
  deriving Repr

namespace STRIPS

def actions {n} (pt : STRIPS n) : Actions n :=
  List.toFinset pt.actions'

def init {n} (pt : STRIPS n) : State n :=
  convertState pt.init'

def GoalState {n} (pt : STRIPS n) (s : State n) : Prop :=
  convertVarSet pt.goal' ⊆ s

end STRIPS

/-! ### Paths in state space and plans -/

/--
Given a STRIPS planning task `pt`, `Path s1 s2` is a path form the state `s1` to the state `s2`
in the state space of `pt`.
-/
inductive Path {n} (pt : STRIPS n) : State n → State n → Type
/-- The empty path consisting of a single node `s`. -/
| empty s : Path pt s s
/-- The path consisting of the node `s`, and the path `π`, where `s[a]` is the first node of `π`.-/
| cons a {s1} s2 {s3}
  (ha : a ∈ pt.actions) (succ : Successor a s1 s2) (π : Path pt s2 s3) : Path pt s1 s3

/-- A plan for a state `s` for a planning task `pt` is a path from `s` to a goal state of pt. -/
structure Plan {n} (pt : STRIPS n) (s : State n) where
  /-- The goal state in `pt`. -/
  last : State n
  /-- The path from `s` to the goal state. -/
  path : Path pt s last
  /-- The proof that `last` is a goal state. -/
  goal : pt.GoalState last

/-! ### Unsolvability -/

/-- A state is unsolvable if there is no plan for that state. -/
abbrev UnsolvableState {n} (pt : STRIPS n) (s : State n):=
  IsEmpty (Plan pt s)

/-- A planning task is unsolvable if the initial state is unsolvable. -/
abbrev Unsolvable {n} (pt : STRIPS n) :=
  UnsolvableState pt pt.init

end Validator
