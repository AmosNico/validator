import Validator.PlanningTask.Parser
import Validator.Certificate.Certificate

open Validator Parser Knowledge
  DeadKnowledge UnsolvableKnowledge ActionSubsetKnowledge StateSubsetKnowledge

/-! # Parser for Certificates
This file contains a parser for parsing certificates for the proof system.
-/

namespace Certificate

instance {α p} : Coe (Result α p) (Parser { a : α // p a }) where
  coe
  | .ok a => pure a
  | .error e => throw e

def parseActionSetExpr (idx : ℕ) : Parser ActionSetExpr :=
  readLine (toString idx) <| parseCases [
    ("b", return ActionSetExpr.enum (← parseListNat)),
    ("u", return ActionSetExpr.union (← parseNat) (← parseNat)),
    ("a", return ActionSetExpr.all)
  ]

def parserTODO {α : outParam Type} : Parser α := Parser.throwUnexpectedWithMessage none "TODO"

def parseConstStateSetExpr {n} (pt : STRIPS n) : Parser (StateSetExpr pt) :=
  parseCases [
    ("e", return StateSetExpr.empty),
    ("i", return StateSetExpr.init),
    ("g", return StateSetExpr.goal)
  ]

def parseBdd {n} (pt : STRIPS n) : Parser (StateSetExpr pt) :=
  do
    let path← parseWord
    let idx ← parseNat
    return StateSetExpr.bdd sorry

def parseStateSetExpr {n} (pt : STRIPS n) (idx : ℕ) : Parser (StateSetExpr pt) :=
  readLine (toString idx) <| parseCases [
    ("c", parseConstStateSetExpr pt),
    ("b", parseBdd pt),
    ("h", parserTODO),
    ("e", parserTODO),
    ("n", return StateSetExpr.neg (← parseNat)),
    ("i", return StateSetExpr.inter (← parseNat) (← parseNat)),
    ("u", return StateSetExpr.union (← parseNat) (← parseNat)),
    ("p", return StateSetExpr.progr (← parseNat) (← parseNat)),
    ("r", return StateSetExpr.regr (← parseNat) (← parseNat)),
  ]

def parseDeadKnowledge : Parser Knowledge :=
  do
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

def parseUnsolvableKnowledge : Parser Knowledge :=
  unsolvable <$> parseCases [
    ("ci", return CI (← parseNat)),
    ("cg", return CG (← parseNat))
  ]

def parseSubsetKnowledge : Parser Knowledge :=
  do
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

def parseKnowledge (idx : ℕ) : Parser Knowledge :=
  readLine (toString idx) <| parseCases [
    ("d", parseDeadKnowledge),
    ("u", parseUnsolvableKnowledge),
    ("s", parseSubsetKnowledge)
  ]

partial def parseCertificate {n} (pt : STRIPS n)
  (C : optParam (Certificate pt) (Certificate.mk #[] #[] #[])) :
  Parser (Certificate pt) :=
  parseCases [
    ("a", do
      let A ← parseActionSetExpr C.actions.size
      parseCertificate pt {C with actions := C.actions.push A}),
    ("e", do
      let S ← parseStateSetExpr pt C.states.size
      parseCertificate pt {C with states := C.states.push S}),
    ("k", do
      let K ← parseKnowledge C.knowledge.size
      parseCertificate pt {C with knowledge := C.knowledge.push K}),
    ("#", dropLine *> parseCertificate pt C)
  ] [
    (parseEol, parseCertificate pt C),
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
def parse {n} (pt : STRIPS n) (path : System.FilePath) : IO (Certificate pt) :=
  do
    let content ← IO.FS.readFile path
    match (parseCertificate pt).run content with
    | .ok _ res => return res
    | .error _ e =>
      let msg :=
        s!"The certificate at \"{path}\" is not valid:\n" ++
        e.show content
      throw (IO.userError msg)

end Certificate
