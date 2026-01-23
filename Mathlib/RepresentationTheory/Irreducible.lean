/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Irreducible representations

This file defines irreducible monoid representations.

-/

namespace Representation

@[expose] public section

open scoped MonoidAlgebra

variable {G k V : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)

/-- A representation `ρ` is irreducible if it is non-trivial and has no proper non-trivial
subrepresentations. -/
@[mk_iff] class IsIrreducible extends
  IsSimpleOrder (Subrepresentation ρ)

theorem irreducible_iff_isSimpleModule_asModule :
    IsIrreducible ρ ↔ IsSimpleModule k[G] ρ.asModule := by
  rw [isSimpleModule_iff, isIrreducible_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.subrepresentationSubmoduleOrderIso

theorem is_simple_module_iff_irreducible_ofModule (M : Type*) [AddCommGroup M] [Module k[G] M] :
    IsSimpleModule k[G] M ↔ IsIrreducible (ofModule (k := k) (G := G) M) := by
  rw [isSimpleModule_iff, isIrreducible_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.submoduleSubrepresentationOrderIso

end

end Representation
