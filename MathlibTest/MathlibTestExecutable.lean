import Lean
import Std
import Qq
import Batteries
import Aesop
import ProofWidgets
import Mathlib
import Plausible

def main : IO Unit := do
  IO.println "Verified that an executable importing all of Mathlib and its upstream dependencies can be built and executed."
