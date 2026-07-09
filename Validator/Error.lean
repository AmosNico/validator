module

import Mathlib.Data.Nat.Notation
import Mathlib.Data.String.Defs

public import Parser
public import Validator.StateSetFormalism.StateSetFormalism

namespace Validator

/-! # Error Handling for Parsing and Validation
This file implements error handling for the parsers and the validator.
-/

/--
Get the line, line number and position in the line of the position `p` in `s`.
Panicks if `p` is not a valid position in `s`.
-/
def positionInfo (s : String) (p : String.Pos.Raw) : String × ℕ × ℕ :=
  if h : p.IsValid s then
    let pos : s.Pos := ⟨p, h⟩
    let startPos := (String.Pos.revFind? pos '\n' >>= String.Pos.next?).getD s.startPos
    let endPos := String.Pos.find pos '\n'
    let line_nb := (s.sliceTo pos).lines.length
    let offset := (s.extract startPos pos).positions.length
    (s.extract startPos endPos, line_nb, offset)
  else
    unreachable!

public inductive IndexType
  | Action
  | ActionSet
  | StateSet
  | Knowledge
  | Bdd

public instance : ToString IndexType where
  toString
  | .Action => "action"
  | .ActionSet => "action set"
  | .StateSet => "state set"
  | .Knowledge => "knowledge"
  | .Bdd => "bdd"

/-- The type of errors used in the certificate parser and checker. -/
public inductive Error
  /-- The certificate is invalid because there is no identifier `Eᵢ` for type `T`. -/
  | invalidId (T : IndexType) (Eᵢ : ℕ)
  /-- The certificate is invalid because the given identifers are invalid for type `T`. -/
  | invalidIds (T : IndexType) (ids : List ℕ)
  /-- The certificate is invalid because some id in the certificat did not match the expected id. -/
  | unexpectedId (T : IndexType) (expected found : ℕ)
  /--
  The certificate is invalid because the expression with `Eᵢ` was used when an expression with a
  different format was expected.
  -/
  | unexpected (T : IndexType) (Eᵢ : ℕ) (expected found : String)
  /-
  The certificate is invalid because it falsely caimed that the set with id `E1ᵢ` is a subset of the
  one with id `E2ᵢ`.
  -/
  | notSubset (T : IndexType) (E1ᵢ E2ᵢ : ℕ)
  /-
  The certificate tried to apply the rule `B4` with a combination of formalisms that is not
  supported.
  -/
  | unsupportedB4 (R R' : StateSetFormalism)
  /- The certificate did not claim unsolvability of the planning task. -/
  | noUnsolvability
  /-- An error occured while parsing the given bdd file. -/
  | bddError (path : System.FilePath) (e : IO.Error)
  /-- An unexpected character was found at the given position while parsing the string `s`. -/
  | parseUnexpected (s : String) (pos : String.Pos.Raw)
  /--
  Add an error message to the error `e`, with the possibility of specifiying the position in case
  of a parsing error.
  -/
  | addMessage (e : Error) (pos : Option (String × String.Pos.Raw)) (msg : String)

namespace Error

public instance : Parser.Error Error String.Slice Char where
  unexpected s p _ := Error.parseUnexpected s.str p
  addMessage e s p msg := Error.addMessage e (s.str, p) msg

/-- Format the given error. -/
def format : Error →  Std.Format
  | invalidId T found =>
    f!"There is no {T} with identifier #{found}."
  | invalidIds T found =>
    f!"The following {T} identifiers are invalid:\n{found}."
  | unexpectedId T expected found =>
    f!"Expected {T} with identifier #{expected}, but found #{found}."
  | unexpected T id expected found =>
    f!"The {T} with identifier #{id} is expect to be {expected}, but it is {found}."
  | notSubset T id1 id2 =>
    f!"The {T} #{id1} is not a subset of #{id2}."
  | unsupportedB4 R1 R2 =>
    f!"The rule B4 is not supported when the left-hand-side is a {R1}-formula and\
      the right-hand-side is a {R2}-formula."
  | noUnsolvability => "The certificate does not prove unsolvability."
  | bddError path e => f!"An error occured while parsing the bdds in the file {path}:\n{e}"
  | parseUnexpected s pos =>
    let ⟨line, k, offset⟩ := positionInfo s pos
    f!"Unexpect character on line {k}:\n{line}\n{String.replicate (offset - 1) ' '}^\n"
  | addMessage e none msg => msg ++ .indentD e.format
  | addMessage e (some (s, pos)) msg =>
    let ⟨_, n, k⟩ := positionInfo s pos
    f!"{msg} (line {n}, pos {k})" ++ .indentD e.format

@[no_expose]
public instance : Std.ToFormat Error where
  format := Error.format

end Error

public abbrev Result.{u} (α : Type u) (p : α → Prop) := Except Error { a // p a }

public abbrev ResultProp (p : Prop) := Result Unit (fun _ ↦ p)

public def withErrorMessage {α p} : Option String →  Result α p → Result α p
| none, res => res
| some msg, res => try res catch e => throw (Validator.Error.addMessage e none msg)

end Validator
