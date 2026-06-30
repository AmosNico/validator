module

import Validator.PlanningTask.ParserOld
public import Validator.Certificate.Certificate

/-! # Parser for Certificates
This file contains a parser for parsing certificates for the proof system.
-/

open Validator Parser Knowledge
  DeadKnowledge UnsolvableKnowledge ActionSubsetKnowledge StateSubsetKnowledge

namespace Validator.Certificate

/--
The certificates allow for storing multiple BDDs in one file, and the name of the file is not known
in advance. To avoid that the same file is read multiple times, the file is read the first time
it is mentioned, and all BDDs in the file are stored. A `BddManager` keeps track of all Bdds read
so far.
-/
structure BddManager {n} (pt : STRIPS n) where
  dir : System.FilePath
  bdds : Std.HashMap System.FilePath (Array (StateSetExpr pt))

abbrev Parser {n} (pt : STRIPS n) := StateT (BddManager pt) (ParserT Error String.Slice Char IO)

variable {n} (pt : STRIPS n)

instance {α p} : Coe (Result α p) (Parser pt { a : α // p a }) where
  coe
  | .ok a => pure a
  | .error e => throw e

def parseActionSetExpr (idx : ℕ) : Parser pt ActionSetExpr :=
  readLine (toString idx) <| parseCases [
    ("b", return ActionSetExpr.enum (← parseListNat)),
    ("u", return ActionSetExpr.union (← parseNat) (← parseNat)),
    ("a", return ActionSetExpr.all)
  ]

def parseConstStateSetExpr {n} (pt : STRIPS n) : Parser pt (StateSetExpr pt) :=
  parseCases [
    ("e", return StateSetExpr.empty),
    ("i", return StateSetExpr.init),
    ("g", return StateSetExpr.goal)
  ]

/-
/-- Parse a bdd in the ddmp format. -/
def parseBdd' n (idx : ℕ) : Parser (BDD (2 * n)) := do
  -- First line contains variable ordering

  -- Find BDD with the correct index
  Parser.dropUntil dropLine (checkLine (toString idx))
  return parseBdd
-/


def BddManager.init {n} {pt : STRIPS n} (dir : String) : BddManager pt :=
  ⟨dir, ∅⟩

def parseBdd' {n} {pt : STRIPS n} (h : IO.FS.Handle) : Parser pt (StateSetExpr pt) := do
  let path ← parseWord
  let idx ← parseNat
  try
    let ⟨ψ, h1⟩ ← BDD.parseBDD h
    return StateSetExpr.bdd ⟨ψ, h1⟩
  catch _ =>
    let msg := s!"Unable to parse the bdd with index {idx} in the file {path}."
    throwUnexpectedWithMessage none msg

def String.toFin? (n : ℕ) (s : String) : Option (Fin n) := do
  let i ← s.toNat?
  if h : i < n then some ⟨i, h⟩ else none

def parseBddFile {n} {pt : STRIPS n} (path : System.FilePath) :
    Parser pt (Array (StateSetExpr pt)) := do
  let h ← IO.FS.Handle.mk path .read
  -- First line contains the variable ordering. For now it is assumed to be 1, ..., n
  let l ← h.getLine
  let some as := (l.splitOn " ").mapM (String.toFin? n) | sorry
  if as == List.finRange n then
    let mut bdds : Array (StateSetExpr pt) := #[]
    while True do
      let ⟨B, h⟩  ←  BDD.parseBDD (n := n) h
      bdds := bdds.push (StateSetExpr.bdd ⟨B, h⟩)
    return bdds
  else
    sorry -- throw (IO.userError "")

def getBDD {n} (pt : STRIPS n) (path : System.FilePath) (id : ℕ) :
    Parser pt (StateSetExpr pt) := do
  let M ← get
  match M.bdds[path]? with
  | some bdds => do
    let some B := bdds[id]? | throw sorry
    return B
  | none => do
    let bdds ← parseBddFile path
    set { M with bdds := M.bdds.insert path bdds }
    let some B := bdds[id]? | sorry
    return B

def parseBdd {n} (pt : STRIPS n) : Parser pt (StateSetExpr pt) := do
  let path ← parseWord
  let idx ← parseNat
  try
    getBDD pt path idx
  catch _ =>
    let msg := s!"Unable to parse the bdd with index {idx} in the file {path}."
    sorry -- throwUnexpectedWithMessage none msg

def parsePosLiteral {n} : Parser pt { l : Formula.Literal (2 * n) // Even l.1.val } := do
  let i ← parseNat
  -- The variables in dimacs format start counting with 1, whereas we start with 0
  -- Immediately make the variables unprimed.
  if h : 0 < i && i < n + 1
  then return ⟨⟨⟨2 * (i - 1), by grind⟩, true⟩, by grind⟩
  else sorry -- Parser.throwUnexpected

def parseNegLiteral {n} : Parser pt { l : Formula.Literal (2 * n) // Even l.1.val } := do
  let i ← checkString "-" *> parseNat
  if h : 0 < i && i < n + 1
  then return ⟨⟨⟨2 * (i - 1), by grind⟩, false⟩, by grind⟩
  else sorry -- Parser.throwUnexpected

def parseLiteral n : Parser pt { l : Formula.Literal (2 * n) // Even l.1.val } :=
  Parser.withErrorMessage "Parsing a literal."
    (parsePosLiteral <|> parseNegLiteral)

def parseClause n : Parser pt { γ : Formula.Clause (2 * n) // γ.vars.IsUnprimed } := do
  let ⟨γ, ()⟩ ← takeUntil (checkString "0") (parseLiteral n)
  return ⟨γ.toList, by simp [VarSet.IsUnprimed]; grind⟩

def parseCNF {n} : Parser pt { φ : Formula.CNF (2 * n) // φ.vars.IsUnprimed } :=
  Parser.withErrorMessage "Parsing CNF-formula in DIMACS format" do
    checkString "p" *> checkString "cnf" *> checkString (toString n)
    let nb_clauses ← parseNat
    let as ← take nb_clauses (parseClause n)
    return ⟨as.toList, by simp [VarSet.IsUnprimed]; grind⟩

def parseHorn {n} (pt : STRIPS n) : Parser pt (StateSetExpr pt) := do
  let ⟨φ, h1⟩ ← parseCNF
  match h : Horn.fromCNF φ with
  | none => throwUnexpectedWithMessage none "The given CNF-formula is not a Horn-formula."
  | some ψ =>
    have h2 : (Formula.vars ψ).IsUnprimed := by
      apply Horn.vars_fromCNF at h
      simp_all only [VarSet.IsUnprimed, VarSet.Subset_def, implies_true]
    return StateSetExpr.horn ⟨ψ, h2⟩

def parseMods {n} (pt : STRIPS n) : Parser pt (StateSetExpr pt) :=
  sorry

def parseStateSetExpr {n} (pt : STRIPS n) (idx : ℕ) : Parser pt (StateSetExpr pt) :=
  readLine (toString idx) <| parseCases [
    ("c", parseConstStateSetExpr pt),
    ("b", parseBdd pt),
    ("h", parseHorn pt),
    ("e", parseMods pt),
    ("n", return StateSetExpr.neg (← parseNat)),
    ("i", return StateSetExpr.inter (← parseNat) (← parseNat)),
    ("u", return StateSetExpr.union (← parseNat) (← parseNat)),
    ("p", return StateSetExpr.progr (← parseNat) (← parseNat)),
    ("r", return StateSetExpr.regr (← parseNat) (← parseNat)),
  ]

def parseDeadKnowledge : Parser pt Knowledge := do
  let Sᵢ ← parseNat
  dead Sᵢ <$> parseCases [
    ("ed", return ED Sᵢ),
    ("ud", return UD Sᵢ (← parseNat) (← parseNat)),
    ("sd", return SD Sᵢ (← parseNat) (← parseNat)),
    ("pg", return PG Sᵢ (← parseNat) (← parseNat) (← parseNat)),
    ("pi", return PI Sᵢ (← parseNat) (← parseNat) (← parseNat)),
    ("rg", return RG Sᵢ (← parseNat) (← parseNat) (← parseNat)),
    ("ri", return RI Sᵢ (← parseNat) (← parseNat) (← parseNat))
  ]

def parseUnsolvableKnowledge : Parser pt Knowledge :=
  unsolvable <$> parseCases [
    ("ci", return CI (← parseNat)),
    ("cg", return CG (← parseNat))
  ]

def parseSubsetKnowledge : Parser pt  Knowledge := do
  let Eᵢ ← parseNat
  let E'ᵢ ← parseNat
  parseCases [
    ("urs", return stateSubset Eᵢ E'ᵢ (URS Eᵢ E'ᵢ)),
    ("ura", return actionSubset Eᵢ E'ᵢ (URA Eᵢ E'ᵢ)),
    ("uls", return stateSubset Eᵢ E'ᵢ (ULS Eᵢ E'ᵢ)),
    ("ula", return actionSubset Eᵢ E'ᵢ (ULA Eᵢ E'ᵢ)),
    ("irs", return stateSubset Eᵢ E'ᵢ (IRS Eᵢ E'ᵢ)),
    ("ils", return stateSubset Eᵢ E'ᵢ (ILS Eᵢ E'ᵢ)),
    ("dis", return stateSubset Eᵢ E'ᵢ (DIS Eᵢ E'ᵢ)),
    ("sus", return stateSubset Eᵢ E'ᵢ (SUS Eᵢ E'ᵢ (← parseNat) (← parseNat))),
    ("sua", return actionSubset Eᵢ E'ᵢ (SUA Eᵢ E'ᵢ (← parseNat) (← parseNat))),
    ("sis", return stateSubset Eᵢ E'ᵢ (SIS Eᵢ E'ᵢ (← parseNat) (← parseNat))),
    ("sts", return stateSubset Eᵢ E'ᵢ (STS Eᵢ E'ᵢ (← parseNat) (← parseNat))),
    ("sta", return actionSubset Eᵢ E'ᵢ (STA Eᵢ E'ᵢ (← parseNat) (← parseNat))),
    ("at", return stateSubset Eᵢ E'ᵢ (AT Eᵢ E'ᵢ (← parseNat) (← parseNat))),
    ("au", return stateSubset Eᵢ E'ᵢ (AU Eᵢ E'ᵢ (← parseNat) (← parseNat))),
    ("pt", return stateSubset Eᵢ E'ᵢ (PT Eᵢ E'ᵢ (← parseNat) (← parseNat))),
    ("pu", return stateSubset Eᵢ E'ᵢ (PU Eᵢ E'ᵢ (← parseNat) (← parseNat))),
    ("pr", return stateSubset Eᵢ E'ᵢ (PR Eᵢ E'ᵢ (← parseNat))),
    ("rp", return stateSubset Eᵢ E'ᵢ (RP Eᵢ E'ᵢ (← parseNat))),
    ("b1", return stateSubset Eᵢ E'ᵢ (B1 Eᵢ E'ᵢ)),
    ("b2", return stateSubset Eᵢ E'ᵢ (B2 Eᵢ E'ᵢ)),
    ("b3", return stateSubset Eᵢ E'ᵢ (B3 Eᵢ E'ᵢ)),
    ("b4", return stateSubset Eᵢ E'ᵢ (B4 Eᵢ E'ᵢ)),
    ("b5", return actionSubset Eᵢ E'ᵢ (B5 Eᵢ E'ᵢ)),
  ]

def parseKnowledge (idx : ℕ) : Parser pt Knowledge :=
  readLine (toString idx) <| parseCases [
    ("d", parseDeadKnowledge),
    ("u", parseUnsolvableKnowledge),
    ("s", parseSubsetKnowledge)
  ]

partial def parseCertificate {n} (pt : STRIPS n)
    (C : optParam (Certificate pt) (Certificate.mk #[] #[] #[])) : Parser pt (Certificate pt) :=
  parseCases [
    ("a", do
      let A ← parseActionSetExpr C.actions.size
      parseCertificate pt M {C with actions := C.actions.push A}),
    ("e", do
      let S ← parseStateSetExpr pt C.states.size
      parseCertificate pt M {C with states := C.states.push S}),
    ("k", do
      let K ← parseKnowledge C.knowledge.size
      parseCertificate pt M {C with knowledge := C.knowledge.push K}),
    ("#", dropLine *> parseCertificate pt M C)
  ] [
    (parseEol, parseCertificate pt M C),
    (Parser.endOfInput, return C)
  ]

/--
Try to read the file at the given path, and try to parse it into a certificate for the planing
task `pt`. Each line of the certificate is expected to either be an action set expression,
a state set expression, a piece of knowledge or a comment (starting with `#`).

Action set expressions have the following formats, where `<AID>` stands for action set ID.
The action set ID after `a` is the ID of the action set itself, it should start at 0 and
increase by one for each action set expression.

    a <AID> b <amount of actions> <list of action IDs>         (list of actions)
    a <AID> u <AID left> <AID right>                           (union of actions)
    a <AID> a                                                  (set of all actions)

State set expressions have the following formats, where `<SID>` stands for state set ID.
The state set ID after `e` is the ID of the state set itself, it should start at 0 and
increase by one for each state set expression.

    e <SID> c e                                                 (constant empty set)
    e <SID> c i                                                 (constant initial state set)
    e <SID> c g                                                 (constant goal set)
    e <SID> b <bdd_filename> <bdd_index>                        (bdd set)
    e <SID> t <discription in DIMACS>                           (horn set)
    e <SID> e <TODO>                                            (MODS set)
    e <SID> n <ID of negated state set>                         (negation)
    e <SID> i <SID left> <SID right>                            (intersection)
    e <SID> u <SID left> <SID right>                            (union)
    e <SID> p <SID> <AID>                                       (progression)
    e <SID> r <SID> <AID>                                       (regression)

Knowledge expressions have the following formats, where `<KID>` stands for knowledge ID.
The knowledge ID after `k` is the ID of the knowledge itself, it should start at 0 and
increase by one for each piece of knowledge. For dead knowledge, the ID after `d` is the
ID of state set that is dead, and for subset knowledge the IDs after `s` are the IDs
corresponding to the left and right state set. The knowledge IDs after the rule are the IDs
of the premises.

    k <KID> d <SID> ed                                          (empty set dead)
    k <KID> d <SID> ud <KID> <KID>                              (union dead)
    k <KID> d <SID> sd <KID> <KID>                              (subset dead)
    k <KID> d <SID> pg <KID> <KID> <KID>                        (progression goal)
    k <KID> d <SID> pi <KID> <KID> <KID>                        (progression initial)
    k <KID> d <SID> sd <KID> <KID> <KID>                        (regression goal)
    k <KID> d <SID> pg <KID> <KID> <KID>                        (regression initial)
    k <KID> u ci <KID>                                          (conclusion initial)
    k <KID> u cg <KID>                                          (conclusion goal)
    k <KID> s <SID> <SID> urs                                   (union right state)
    k <KID> s <AID> <AID> ura                                   (union right action)
    k <KID> s <SID> <SID> uls                                   (union left state)
    k <KID> s <AID> <AID> ula                                   (union left action)
    k <KID> s <SID> <SID> irs                                   (intersection right state)
    k <KID> s <SID> <SID> ils                                   (intersection left state)
    k <KID> s <SID> <SID> dis                                   (distributivity state)
    k <KID> s <SID> <SID> sus <KID> <KID>                       (subset union state)
    k <KID> s <AID> <AID> sua <KID> <KID>                       (subset union action)
    k <KID> s <SID> <SID> sis <KID> <KID>                       (subset intersection state)
    k <KID> s <SID> <SID> sts <KID> <KID>                       (subset transitivity state)
    k <KID> s <AID> <AID> sta <KID> <KID>                       (subset transitivity action)
    k <KID> s <SID> <SID> at <KID> <KID>                        (action transitivity)
    k <KID> s <SID> <SID> au <KID> <KID>                        (action union)
    k <KID> s <SID> <SID> pt <KID> <KID>                        (progression transitivity)
    k <KID> s <SID> <SID> pu <KID> <KID>                        (progression union)
    k <KID> s <SID> <SID> pr <KID>                              (progression regression)
    k <KID> s <SID> <SID> rp <KID>                              (regression progression)
    k <KID> s <SID> <SID> b1                                    (basic statement 1)
    k <KID> s <SID> <SID> b2                                    (basic statement 2)
    k <KID> s <SID> <SID> b3                                    (basic statement 3)
    k <KID> s <SID> <SID> b4                                    (basic statement 4)
    k <KID> s <AID> <AID> b5                                    (basic statement 5)
-/
public def parse {n} (pt : STRIPS n) (path : System.FilePath) : IO (Certificate pt) := do
  let content ← IO.FS.readFile path
  let some dir := path.parent | sorry
  let M := BddManager.mk dir ∅
  let p := Parser.withErrorMessage
    s!"The certificate at \"{path}\" is not valid:\n"
    (parseCertificate pt M)
  match ← p.run content with
  | .ok _ res => return res
  | .error _ e => throw (IO.userError (e.formatWithContext content).pretty)

end Validator.Certificate
