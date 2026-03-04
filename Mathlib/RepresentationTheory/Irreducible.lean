/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
# Irreducible representations

This file defines irreducible monoid representations.

-/

@[expose] public section

namespace Representation

open scoped MonoidAlgebra

variable {G k V W : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (ρ : Representation k G V) (σ : Representation k G W)

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

namespace IsIrreducible

variable {ρ σ} (f : IntertwiningMap ρ σ) [IsIrreducible ρ]

instance : IsSimpleModule k[G] ρ.asModule :=
  (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance

open Function IntertwiningMap

theorem injective_or_eq_zero : Injective f ∨ f = 0 := by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule ρ σ)]
  exact LinearMap.injective_or_eq_zero (equivLinearMapAsModule ρ σ f)

theorem bijective_or_eq_zero [IsIrreducible σ] : Bijective f ∨ f = 0 := by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule ρ σ)]
  exact LinearMap.bijective_or_eq_zero (equivLinearMapAsModule ρ σ f)

variable [FiniteDimensional k V] [IsAlgClosed k]

variable (f : IntertwiningMap ρ ρ) in
theorem algebraMap_intertwiningMap_bijective_of_isAlgClosed :
    Bijective (algebraMap k (IntertwiningMap ρ ρ)) := by
  have : Bijective (algebraMap k (Module.End k[G] ρ.asModule)) :=
    IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
  exact (Bijective.of_comp_iff' (IntertwiningMap.equivAlgEnd (ρ:=ρ)).bijective _).1 this

include ρ in
variable (ρ) in
theorem finrank_eq_one_of_isMulCommutative
    [IsMulCommutative G] : Module.finrank k V = 1 := by
  have _ : IsMulCommutative k[G] := ⟨⟨mul_comm⟩⟩
  exact IsSimpleModule.finrank_eq_one_of_isMulCommutative k[G] ρ.asModule k

end IsIrreducible

end Representation
