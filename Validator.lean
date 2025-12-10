import Validator.Certificate.Parser
import Validator.Certificate.ToDerivation

open Validator

def main : IO Unit :=
  do
    try
      let path <- IO.currentDir
      IO.println path
      let pt_path := path / "test" / "success-task.txt"
      let ⟨n, pt⟩ <- STRIPS.parse pt_path
      IO.println (repr pt)
      IO.println s!"initial state : {(List.finRange n).filter (pt.init'[·])}"
      let certificate_path := path / "test" / "success-certificate.txt"
      IO.println "Parsing the certificate"
      let C <- Certificate.parse pt certificate_path
      IO.println "Verifying the certificate"
      match C.verify with
      | .ok ⟨(), hC, h⟩ =>
        have : Unsolvable pt := hC.soundness h
        IO.println "The certificate is valid!"
      | .error e =>
        -- TODO Fix error messages
        throw (IO.userError (e.show ""))

      IO.println (repr C)
    catch e =>
      IO.println e
