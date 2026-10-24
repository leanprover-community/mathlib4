module

public import Aesop
public import Batteries
public import Lean
public import Mathlib
public import Plausible
public import ProofWidgets
public import Qq
public import Std

@[expose] public section

def main : IO Unit := do
  IO.println "Verified that an executable importing all of Mathlib and its upstream dependencies can be built and executed."
