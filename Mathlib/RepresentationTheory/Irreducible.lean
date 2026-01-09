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

namespace Representation

@[expose] public section

open scoped MonoidAlgebra

variable {G k V W : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (ρ : Representation k G V) (σ : Representation k G W)

/-- A representation `ρ` is irreducible if it has no proper non-trivial subrepresentations.
-/
@[mk_iff] class IsIrreducible extends
  IsSimpleOrder (Subrepresentation ρ)

theorem irreducible_iff_is_simple_module_as_module :
    IsIrreducible ρ ↔ IsSimpleModule k[G] ρ.asModule := by
  rw [isSimpleModule_iff, isIrreducible_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.subrepresentationSubmoduleOrderIso

theorem is_simple_module_iff_irreducible_of_module (M : Type*) [AddCommGroup M] [Module k[G] M] :
    IsSimpleModule k[G] M ↔ IsIrreducible (ofModule (k := k) (G := G) M) := by
  rw [isSimpleModule_iff, isIrreducible_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.submoduleSubrepresentationOrderIso

variable {ρ σ} (f : IntertwiningMap ρ σ) [IsIrreducible ρ]

theorem injective_or_eq_zero : Function.Injective f ∨ f = 0 := by
  haveI _ : IsSimpleModule k[G] ρ.asModule :=
    (irreducible_iff_is_simple_module_as_module ρ).mp (by assumption)
  rw [← asLinearMap_zero_iff f]
  exact LinearMap.injective_or_eq_zero (asLinearMap f)

theorem bijective_or_eq_zero [IsIrreducible σ] : Function.Bijective f ∨ f = 0 :=
    by
  haveI _ : IsSimpleModule k[G] ρ.asModule :=
    (irreducible_iff_is_simple_module_as_module ρ).mp (by assumption)
  haveI _ : IsSimpleModule k[G] σ.asModule :=
    (irreducible_iff_is_simple_module_as_module σ).mp (by assumption)
  rw [← asLinearMap_zero_iff f]
  exact LinearMap.bijective_or_eq_zero (asLinearMap f)

variable [FiniteDimensional k V] [IsAlgClosed k]

variable (f : IntertwiningMap ρ ρ) in
theorem algebraMap_intertwiningMap_bijective_of_isAlgClosed :
    Function.Bijective (algebraMap k (IntertwiningMap ρ ρ)) := by
  haveI _ : IsSimpleModule k[G] ρ.asModule :=
    (irreducible_iff_is_simple_module_as_module ρ).mp (by assumption)
  haveI _ : FiniteDimensional k ρ.asModule := by assumption
  have : Function.Bijective (algebraMap k (Module.End k[G] ρ.asModule)) :=
    IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
  have h_comp :
      (asLinearMap (ρ := ρ) (σ := ρ)) ∘ (algebraMap k (IntertwiningMap ρ ρ)) =
      algebraMap k (Module.End k[G] ρ.asModule) := by
    funext a
    ext v
    rfl
  have h_bij : Function.Bijective
      ((asLinearMap (ρ := ρ) (σ := ρ)) ∘ (algebraMap k (IntertwiningMap ρ ρ))) := by
    simpa [h_comp] using this
  exact (Function.Bijective.of_comp_iff' (asLinearMap_bijective (ρ := ρ) (σ := ρ))
    (algebraMap k (IntertwiningMap ρ ρ))).1 h_bij

theorem finrank_eq_one_of_isMulCommutative (ρ : Representation k G V) [IsIrreducible ρ]
    [IsMulCommutative G] : Module.finrank k V = 1 := by
  haveI _ : IsSimpleModule k[G] ρ.asModule :=
    (irreducible_iff_is_simple_module_as_module ρ).mp (by assumption)
  haveI _ : FiniteDimensional k ρ.asModule := by assumption
  haveI _ : IsMulCommutative k[G] := ⟨⟨mul_comm⟩⟩
  exact IsSimpleModule.finrank_eq_one_of_isMulCommutative k[G] ρ.asModule k

end

end Representation
