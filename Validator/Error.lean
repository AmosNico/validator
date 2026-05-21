import Parser
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
inductive Error
| parseUnexpected : Parser.Stream.Position String.Slice → Error
| invalid : String → Error
| addMessage : Error → Option (Parser.Stream.Position String.Slice) → String → Error

namespace Error

instance : Parser.Error Error String.Slice Char where
  unexpected p _ := Error.parseUnexpected p
  addMessage e p msg := Error.addMessage e p msg

/--
Format the given error. The second argument is the context where the error occured.
In case of a parsing error this is the input string and for an error related to the certificate this
is the line of the certifcate causing the error.
-/
def formatWithContext : Error → String → Std.Format
  | .invalid msg, _ => .indentD msg ++ .line
  | .parseUnexpected pos, context =>
    let ⟨line, k, offset⟩ := positionInfo context pos
    f!"Unexpect character on line {k}:\n{line}\n{String.replicate offset ' '}^\n"
  | .addMessage e none msg, context => msg++ .indentD (formatWithContext e context)
  | .addMessage e (some pos) msg, context =>
    let ⟨_, n, k⟩ := positionInfo context pos
    f!"{msg} (line {n}, pos {k})" ++ .indentD (formatWithContext e context)

/-- Instance only works if one for error not containing `parseUnexpected`. -/
-- TODO : check whether it makes to use `Parser.Error.Simple` with context inside a
-- `Error` to ensure this this instance always works.
instance : Std.ToFormat Error where
  format e := formatWithContext e ""

end Error

abbrev Result.{u} (α : Type u) (p : α → Prop) := Except Error { a // p a }

abbrev Result' (p : Prop) := Result Unit (fun _ ↦ p)

def throwInvalid (msg : String) {α p} : Result α p :=
  throw (Validator.Error.invalid msg)

def withErrorMessage {α p} : Option String →  Result α p → Result α p
| none, res => res
| some msg, res => try res catch e => throw (Validator.Error.addMessage e none msg)

end Validator
