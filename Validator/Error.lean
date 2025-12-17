import Parser
import Mathlib.Data.Nat.Notation
import Mathlib.Data.String.Defs

namespace Validator
/-! # Error Handling for Parsing and Validation
This file implements error handling for the parsers and the validator.
-/

def countLines {s} (pos : String.Pos s) : ℕ :=
  (s.sliceTo pos).foldl (fun n d => if d = '\n' then n + 1 else n) 0

def positionInfo (s : String.Slice) : ℕ × ℕ × String :=
  let posStart := (s.startInclusive.revFind? '\n').getD (s.str.startPos)
  let posEnd := s.startInclusive.find (· = '\n')
  let offset := (String.extract posStart s.startInclusive).length
  ⟨countLines s.startInclusive + 1, offset, String.extract posStart posEnd⟩

-- Check whether it makes more sense to use `String.ValidPos`
inductive Error
| parseUnexpected : String.Slice → Error
| unvalid : String → Error
| addMessage : Error → Option String.Slice → String → Error

namespace Error

instance : Parser.Error Error String.Slice Char where
  unexpected p _ := Error.parseUnexpected p
  addMessage e p msg := Error.addMessage e p msg

def toString : Error → String
| parseUnexpected pos =>
    have ⟨n, k, line⟩ := positionInfo pos
    let offset := k + 11 + (ToString.toString n).length
    s!"    line {n}: {line}\n" ++ String.replicate offset ' ' ++ "^\n"
| unvalid msg => s!"  {msg}\n"
| addMessage e none msg => s!"  {msg}\n" ++ e.toString
| addMessage e (some pos) msg =>
  have ⟨n, k, _⟩ := positionInfo pos
  s!"  {msg} (line {n}, pos {k})\n" ++ e.toString

instance : ToString Error where
  toString := toString

end Error

abbrev Result.{u} (α : Type u) (p : α → Prop) := Except Error { a // p a }

abbrev Result' (p : Prop) := Result Unit (fun _ ↦ p)

def throwUnvalid (msg : String) {α p} : Result α p :=
  throw (Validator.Error.unvalid msg)

def withErrorMessage {α p} : Option String →  Result α p → Result α p
| none, res => res
| some msg, res => try res catch e => throw (Validator.Error.addMessage e none msg)

end Validator
