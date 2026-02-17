/-
Copyright (c) 2026 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.RepresentationTheory.Irreducible

/-!
# Semisimple representations

This file defines the typeclass `IsSemisimpleRepresentation` for semisimple monoid representations.

-/

namespace Representation

variable {k G V : Type*}

@[expose] public section

open scoped MonoidAlgebra

variable [Monoid G] [Field k] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- A representation is semisimple when every subrepresentation has a complement. -/
abbrev IsSemisimpleRepresentation :=
  ComplementedLattice (Subrepresentation ρ)

theorem isSemisimpleRepresentation_iff_isSemisimpleModule_asModule :
    IsSemisimpleRepresentation ρ ↔ IsSemisimpleModule k[G] ρ.asModule := by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.subrepresentationSubmoduleOrderIso

theorem isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule (M : Type*) [AddCommGroup M]
    [Module k[G] M] :
    IsSemisimpleModule k[G] M ↔ IsSemisimpleRepresentation (ofModule (k := k) (G := G) M) := by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.submoduleSubrepresentationOrderIso

end

end Representation
