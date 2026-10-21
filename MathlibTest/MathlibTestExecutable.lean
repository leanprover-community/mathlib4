module

public import Lean
public import Std
public import Qq
public import Batteries
public import Aesop
public import ProofWidgets
public import Mathlib
public import Plausible

@[expose] public section

def main : IO Unit := do
  IO.println "Verified that an executable importing all of Mathlib and its upstream dependencies can be built and executed."
