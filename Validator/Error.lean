module

public import Parser
import Mathlib.Data.Nat.Notation
import Mathlib.Data.String.Defs

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

-- Check whether it makes more sense to use `String.ValidPos`
public inductive Error
| parseUnexpected : String → String.Pos.Raw → Error
| invalid : String → Error
| addMessage : Error → Option (String × String.Pos.Raw) → String → Error

namespace Error

public instance : Parser.Error Error String.Slice Char where
  unexpected s p _ := Error.parseUnexpected s.str p
  addMessage e s p msg := Error.addMessage e (s.str, p) msg

/--
Format the given error.
-/
def format : Error →  Std.Format
  | .invalid msg => .indentD msg ++ .line
  | .parseUnexpected s pos =>
    let ⟨line, k, offset⟩ := positionInfo s pos
    f!"Unexpect character on line {k}:\n{line}\n{String.replicate offset ' '}^\n"
  | .addMessage e none msg => msg++ .indentD e.format
  | .addMessage e (some (s, pos)) msg =>
    let ⟨_, n, k⟩ := positionInfo s pos
    f!"{msg} (line {n}, pos {k})" ++ .indentD e.format

@[no_expose]
public instance : Std.ToFormat Error where
  format := Error.format

end Error

public abbrev Result.{u} (α : Type u) (p : α → Prop) := Except Error { a // p a }

public abbrev Result' (p : Prop) := Result Unit (fun _ ↦ p)

public def throwInvalid (msg : String) {α p} : Result α p :=
  throw (Error.invalid msg)

public def withErrorMessage {α p} : Option String →  Result α p → Result α p
| none, res => res
| some msg, res => try res catch e => throw (Validator.Error.addMessage e none msg)

end Validator
