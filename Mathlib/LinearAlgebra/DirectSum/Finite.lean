import Mathlib.RingTheory.Finiteness.Defs

/-!
# A finite direct sum of finite modules is finite

This file defines a `Module.Finite` instance for a finite direct sum of finite modules.

-/

@[expose] public section

open DirectSum

variable {R ι : Type*} [Semiring R] [Finite ι] (M : ι → Type*)
  [∀ i : ι, AddCommMonoid (M i)] [∀ i : ι, Module R (M i)] [∀ (i : ι), Module.Finite R (M i)]

instance Module.Finite.instDFinsupp : Module.Finite R (Π₀ (i : ι), M i) :=
  letI : Fintype ι := Fintype.ofFinite _
  Module.Finite.equiv DFinsupp.linearEquivFunOnFintype.symm

instance Module.Finite.instDirectSum : Module.Finite R (⨁ i, M i) :=
  Module.Finite.instDFinsupp M
