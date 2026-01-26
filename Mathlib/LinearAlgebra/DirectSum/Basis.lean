import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Bases for direct sum of modules

This file defines a `Module.Free` instance for the direct sum of modules.

## Implementation notes

Currently, to get a basis on `⨁ i, M i` from a basis on each `M i`, use `DFinsupp.basis`
(using that the types are defeq).
-/

@[expose] public section

open DirectSum

section Semiring

variable (R : Type*) [Semiring R] {ι : Type*} (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)]
variable [∀ i : ι, Module R (M i)]

instance Module.Free.directSum [∀ i : ι, Module.Free R (M i)] : Module.Free R (⨁ i, M i) :=
  Module.Free.dfinsupp R M

end Semiring
