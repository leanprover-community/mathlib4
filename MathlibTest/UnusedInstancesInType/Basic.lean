module

public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
Basic definitions used for testing the unused instances in type linters. The definitions here "use"
instances in a straightforward way.

This file also publicly imports `Mathlib.Init` so that importing this file is sufficient to import
the linters.

This file will be expanded as the linters gain functionality.
-/

@[expose] public section

/-- Infers an instance of its first argument in its second argument. Equal to `True`. -/
def UsesInstanceOf (α : Sort u) (_ : α := by infer_instance) : Prop := True

/-- Uses an arbitrary value of any type. -/
def UsesExactly {α} : α → Prop := fun _ => True

/-- Uses an instance of the given type in a proof, returning a proof of true. Can be nested in
`Uses`.-/
theorem UsesInstanceInProof (α : Sort u) (_ : α := by infer_instance) : True := trivial
