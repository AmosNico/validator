module

import Strips.Parser
import Validator.Certificate.Parser
import Validator.Certificate.ToDerivation

open STRIPS Validator

public def main (args : List String) : IO Unit := do
  match args with
  | [pathTask, pathCertificate] =>
    try
      let path <- IO.currentDir
      let ⟨_, pt⟩ <- readPlanningTask (path / pathTask)
      IO.println pt
      IO.println "Parsing the certificate"
      let C <- Certificate.parse pt (path / pathCertificate)
      IO.eprintln "Verifying the certificate"
      match C.verify with
      | .ok ⟨(), hC, h⟩ =>
        have : PlanningTask.Unsolvable pt := hC.soundness h
        IO.println "The certificate is valid!"
      | .error e =>
        -- TODO Fix error messages
        throw (IO.userError (Std.ToFormat.format e).pretty)
    catch e =>
      IO.println e
  | _ =>
    IO.println "Usage: validator <task.txt> <certificate.txt>"
