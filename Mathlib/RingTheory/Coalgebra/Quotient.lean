/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Coalgebra structure on the quotient by a coideal

## Main definitions

* `IsCoideal I` : the submodule `I : Submodule R C` is a coideal.

## Main results

* `Coalgebra` instance on `C ⧸ I` when `[IsCoideal I]`.
-/

public section

open Coalgebra LinearMap TensorProduct

variable {R C : Type*} [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- An `R`-submodule `I` of an `R`-coalgebra `C` is a *coideal* if the counit vanishes on
`I` and the comultiplication descends through the module quotient `C ⧸ I`. -/
@[mk_iff]
class IsCoideal (I : Submodule R C) : Prop where
  counit_eq_zero : ∀ ⦃x : C⦄, x ∈ I → counit x = (0 : R)
  comul_eq_zero : ∀ ⦃x : C⦄, x ∈ I → map I.mkQ I.mkQ (comul x) = 0

namespace Coalgebra.Quotient

variable (I : Submodule R C) [IsCoideal I]

noncomputable instance : CoalgebraStruct R (C ⧸ I) where
  comul := I.liftQ (map I.mkQ I.mkQ ∘ₗ comul) fun _ hx => IsCoideal.comul_eq_zero hx
  counit := I.liftQ counit fun _ hx => IsCoideal.counit_eq_zero hx

lemma comul_comp_mkQ : comul ∘ₗ I.mkQ = map I.mkQ I.mkQ ∘ₗ (comul : C →ₗ[R] _) := rfl

lemma counit_comp_mkQ : counit ∘ₗ I.mkQ = (counit : C →ₗ[R] R) := rfl

noncomputable instance : Coalgebra R (C ⧸ I) where
  coassoc := by ext : 1; simp only [coassoc_simps, comul_comp_mkQ]
  rTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_mkQ, ← comp_assoc, rTensor_comp_map, counit_comp_mkQ,
      ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_mkQ, ← comp_assoc, lTensor_comp_map, counit_comp_mkQ,
      ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]

end Coalgebra.Quotient
