import Mathlib.Data.Finset.Sort
import Validator.Error
import Validator.PlanningTask.Core
import Init.Data.String.Bootstrap

namespace Validator
/-! # Parser for STRIPS Planning Tasks

This file contains some general parsing functions and a parser for STRIPS planning tasks.
-/

/-! ## General Parsing Functionality -/
abbrev Parser := ParserT Error Substring Char Id

def parseSpaces : Parser Unit :=
  Parser.dropMany (Parser.Char.char ' ')

def parseSpaces1 : Parser Unit :=
  Parser.dropMany1 (Parser.Char.char ' ')

-- TODO : check whether allowing semicoloms makes sense
def parseEol : Parser Unit :=
  parseSpaces <* Parser.optional (Parser.Char.char ';') <* Parser.Char.eol

def checkString (s : String) : Parser Unit :=
  Parser.Char.string s *> parseSpaces

def checkLine (s : String) : Parser Unit :=
  Parser.Char.string s *> parseEol

-- TODO : rename
def readLine {α} (s : String) (p : Parser α) : Parser α :=
  checkString s *> p <* parseEol

def dropLine : Parser Unit :=
  Parser.dropUntil Parser.Char.eol Parser.anyToken *> pure ()

def parseLine : Parser String :=
  do
    let ⟨⟨l⟩, _⟩ ← Parser.takeUntil Parser.Char.eol Parser.anyToken
    return String.mk l

def parseWord : Parser String :=
  do
    let stop : Parser Unit := parseSpaces1 <|> (Parser.lookAhead Parser.Char.eol *> pure ())
    let ⟨⟨l⟩, _⟩ ← Parser.takeUntil stop Parser.anyToken
    return String.mk l

def parseNat : Parser ℕ :=
  Parser.Char.ASCII.parseNat <* parseSpaces

def parseListNat : Parser (List ℕ) := do
  let n ← parseNat
  let ⟨l⟩ ← Parser.take n parseNat
  return l

abbrev push? {α} : Array α → Option α → Array α
| xs, none => xs
| xs, some x => xs.push x

/--
For each tuple `(p, p', e)` in the given list, try the parser `p`. If it succeeds,
run the parser `p'`, otherwise proceed with the next tuple in the list. The optional
error messages `e` are combined into one error message if none of the parsers `p` succeed.
-/
-- Based on `Parser.first`
def parseCases' {α} (ps : List (Parser Unit × Parser α × Option String)) :
  Parser α :=
  go ps #[]
where
  go : List (Parser Unit × Parser α × Option String) → Array String → Parser α
    | [], ⟨e⟩, s =>
      Parser.throwUnexpectedWithMessage none s!"expected one of the following : {e}" s
    | (p, p', descr) :: ps, e, s =>
      let savePos := Parser.Stream.getPosition s
      p s >>= fun
      | .ok s () => p' s
      | .error s _ => go ps (push? e descr) (Parser.Stream.setPosition s savePos)

/--
For each of the pairs `(s, p)` in `ps1`, try to parse the string `s`. If it succeeds,
run the parser `p`, otherwise proceed with the next pair in the list. If none of parsers for
`s` is successfull, continue with the list `ps2`. For each pair `(p, p')` in this list, try the
parser `p`, and if it succeed, run `p'` and return its result. If it fails continue with the next
pair. If all pairs fail, combine the strings in `ps1` into one error message.
-/
def parseCases {α} (ps1 : List (String × Parser α)) (ps2 : List (Parser Unit × Parser α) := []) :
  Parser α :=
  let ps1' := ps1.map fun ⟨s, p⟩ ↦ ⟨checkString s, p, s⟩
  let ps2' := ps2.map fun ⟨p, p'⟩ ↦ ⟨p, p', none⟩
  parseCases' (ps1' ++ ps2')


/-! ## STRIPS Parser -/
namespace STRIPS

private def parseAtoms : Parser (Array String) :=
  Parser.withErrorMessage "error while parsing atoms"
  do
    let n ← readLine "begin_atoms:" parseNat
    let atoms ← Parser.take n parseLine
    checkLine "end_atoms"
    return atoms

private def parseVar {n} : Parser (Fin n) :=
  Parser.withErrorMessage
    s!"expected a reference to an atom, this should be a natural number smaller then {n}"
  do
    let i ← parseNat
    if h : i < n
    then return Fin.mk i h
    else Parser.throwUnexpected

private def parseVarLn {n} : Parser (Fin n) := parseVar <* parseEol

private def toVarset {n} (l : List (Fin n)) : VarSet' n :=
  ⟨l.toFinset.sort (· ≤ ·), Finset.sort_sorted_lt l.toFinset⟩

private def parseVarSet {n} : Parser (VarSet' n) :=
  do
    let ⟨l⟩ ← Parser.takeMany parseVarLn
    return toVarset l

private def parseState {n} : Parser (State' n) :=
  do
    let as ← Parser.takeMany parseVarLn
    return as.foldl (fun s (v : Fin n) ↦ s ||| BitVec.twoPow n v) (BitVec.zero n)

private def parseInit n : Parser (State' n) :=
  Parser.withErrorMessage "error while parsing the inital state"
    (checkLine "begin_init" *> parseState <* checkLine "end_init")

private def parseGoal n : Parser (VarSet' n) :=
  Parser.withErrorMessage "error while parsing the goal"
    (checkLine "begin_goal" *> parseVarSet <* checkLine "end_goal")

private structure Conditions n where
  pre : List (Fin n)
  add : List (Fin n)
  del : List (Fin n)

private partial def parseConditions {n} (cs : Conditions n) : Parser (Conditions n) :=
  parseCases [
    ("PRE:", return ← parseConditions {cs with pre := (← parseVarLn) :: cs.pre}),
    ("ADD:", return ← parseConditions {cs with add := (← parseVarLn) :: cs.add}),
    ("DEL:", return ← parseConditions {cs with del := (← parseVarLn) :: cs.del}),
    ("end_action", parseEol *> pure cs)
  ]

private def parseAction n : Parser (Action n) :=
  do
    checkLine "begin_action"
    let name ← parseLine
    let cost ← readLine "cost:" parseNat
    let ⟨pre, add, del⟩ ← parseConditions (@Conditions.mk n [] [] [])
    return (Action.mk name (toVarset pre) (toVarset add) (toVarset del) cost)

private def parseActions n : Parser (List (Action n)) :=
  Parser.withErrorMessage "error while parsing the actions"
  do
    let k ← readLine "begin_actions:" parseNat
    let as ← Parser.take k (parseAction n)
    checkLine "end_actions"
    return as.toList

private def parseSTRIPS : Parser (Σ n, STRIPS n) :=
  do
    let atoms ← parseAtoms
    let n := atoms.size
    let atoms : Vector String n := ⟨atoms, by rfl⟩
    let init ← parseInit n
    let goal ← parseGoal n
    let actions ← parseActions n
    Parser.endOfInput
    return Sigma.mk n (STRIPS.mk atoms actions init goal)

/--
Try to read the file corresponding to the given path, and parse its content
into a STRIPS planning task. The file is expected to have the following format:

    begin_atoms: <#atoms>
    <atom 0>
    <atom 1>
    ... (names of all atoms, one on each line)
    end_atoms
    begin_init
    <initital state atom index 0>
    <initital state atom index 1>
    ... (indexes of atoms that are true in initial state, one on each line)
    end_init
    begin_goal
    <goal atom index 0>
    <goal atom index 1>
    ... (indexes of atoms that are true in goal, one on each line)
    end_goal
    begin_actions: <#actions>
    begin_action
    <action_name>
    cost: <action_cost>
    PRE: <precondition atom index 0>
    ADD: <added atom index 0>
    DEL: <deleted atom index 0>
    ... (more PRE, ADD and DEL in any order, one on each line)
    end_action
    ... (more actions)
    end_actions
-/
def parse (path : System.FilePath) : IO (Σ n, STRIPS n) :=
  do
    let content ← IO.FS.readFile path
    match parseSTRIPS.run content with
    | .ok _ res => return res
    | .error _ e =>
      let msg :=
        s!"An error occured when parsing the planning problem at \"{path}\":\n" ++
        e.show content
      throw (IO.userError msg)

end Validator.STRIPS
