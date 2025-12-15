import Parser
import Mathlib.Data.Nat.Notation
import Mathlib.Data.String.Defs

namespace Validator
/-! # Error Handling for Parsing and Validation
This file implements error handling for the parsers and the validator.
-/

-- Check whether it makes more sense to use `String.ValidPos`
inductive Error
| parseUnexpected : String.Pos.Raw → Error
| unvalid : String → Error
| addMessage : Error → Option String.Pos.Raw → String → Error

instance : Parser.Error Error Substring Char where
  unexpected p _ := Error.parseUnexpected p
  addMessage e p msg := Error.addMessage e p msg

private theorem String.revFindAux_le
  {s : String} {p pos pos'} (h : s.revFindAux p pos = some pos') : pos'.1 < pos.1 :=
  by
    unfold String.revFindAux at h
    simp_all [-String.Pos.Raw.eq_zero_iff]
    rcases h with ⟨hneq, h⟩
    have := String.Pos.Raw.prev_lt_of_pos s pos hneq
    split at h
    case isTrue h =>
      simp_all
    case isFalse h =>
      simp_all
      have := String.revFindAux_le h
      omega
  termination_by pos.1

def countLines (s : String) (pos : String.Pos.Raw) : ℕ :=
  match heq : s.revFindAux (· = '\n') pos with
  | some pos' =>
    have : pos'.1 < pos.1 :=
      String.revFindAux_le heq
    1 + countLines s pos'
  | none => 0
termination_by pos.1

def positionInfo (s : String) (pos : String.Pos.Raw) : ℕ × ℕ × String :=
  let posStart := s.findLineStart pos
  let posEnd := s.findAux (· = '\n') s.endPos pos
  ⟨countLines s pos + 1, pos.1 - posStart.1, String.Pos.Raw.extract s posStart posEnd⟩

def Error.show (context : String) : Error → String
| parseUnexpected pos =>
    have ⟨n, k, line⟩ := positionInfo context pos
    s!"    line {n}: {line}\n" ++ String.replicate (k + 11 + (toString n).length) ' ' ++ "^\n"
| unvalid msg => s!"  {msg}\n"
| addMessage e none msg => s!"  {msg}\n" ++ e.show context
| addMessage e (some pos) msg =>
  have ⟨n, k, _⟩ := positionInfo context pos
  s!"  {msg} (line {n}, pos {k})\n" ++ e.show context

abbrev Result.{u} (α : Type u) (p : α → Prop) := Except Error { a // p a }

abbrev Result' (p : Prop) := Result Unit (fun _ ↦ p)

def throwUnvalid (msg : String) {α p} : Result α p :=
  throw (Validator.Error.unvalid msg)

def withErrorMessage {α p} : Option String →  Result α p → Result α p
| none, res => res
| some msg, res => try res catch e => throw (Validator.Error.addMessage e none msg)

end Validator
