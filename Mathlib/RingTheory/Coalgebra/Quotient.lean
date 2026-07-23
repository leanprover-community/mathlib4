/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Coalgebra structure on the quotient by a coideal

## Main definitions

* `Submodule.IsCoideal I` : the submodule `I : Submodule R C` is a coideal.
* `Coalgebra.Quotient.mkQCoalgHom` : `Submodule.mkQ` as a coalgebra homomorphism.

## Main results

* `Coalgebra` instance on `C ⧸ I` when `[I.IsCoideal]`.
-/

public section

open Coalgebra LinearMap TensorProduct

variable {R C : Type*} [CommRing R] [AddCommGroup C] [Module R C]

section CoalgebraStruct

variable [CoalgebraStruct R C]

/-- An `R`-submodule `I` of an `R`-coalgebra `C` is a *coideal* if the counit vanishes on
`I` and the comultiplication descends through the module quotient `C ⧸ I`. -/
@[mk_iff]
class Submodule.IsCoideal (I : Submodule R C) : Prop where
  counit_eq_zero : ∀ ⦃x : C⦄, x ∈ I → counit (R := R) x = 0
  map_mkQ_comul_eq_zero : ∀ ⦃x : C⦄, x ∈ I → TensorProduct.map I.mkQ I.mkQ (comul x) = 0

/-- A submodule is a coideal iff the counit vanishes on it and its comultiplication image lies
in `I ⊗ C + C ⊗ I`, the textbook form of the coideal condition. -/
lemma Submodule.isCoideal_iff_comul_mem (I : Submodule R C) :
    I.IsCoideal ↔ (∀ x ∈ I, counit (R := R) x = 0) ∧
      ∀ x ∈ I, comul x ∈
        LinearMap.range (lTensor C I.subtype) ⊔ LinearMap.range (rTensor C I.subtype) := by
  simp_rw [isCoideal_iff, ← LinearMap.mem_ker,
    TensorProduct.map_ker (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
      (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective]

end CoalgebraStruct

namespace Coalgebra.Quotient

section CoalgebraStruct

variable [CoalgebraStruct R C] (I : Submodule R C) [I.IsCoideal]

instance : CoalgebraStruct R (C ⧸ I) where
  comul := I.liftQ (map I.mkQ I.mkQ ∘ₗ comul) Submodule.IsCoideal.map_mkQ_comul_eq_zero
  counit := I.liftQ counit Submodule.IsCoideal.counit_eq_zero

lemma comul_comp_mkQ : comul ∘ₗ I.mkQ = map I.mkQ I.mkQ ∘ₗ (comul : C →ₗ[R] _) := rfl

lemma counit_comp_mkQ : counit ∘ₗ I.mkQ = (counit : C →ₗ[R] R) := rfl

@[simp]
lemma counit_mk (x : C) : counit (R := R) (Submodule.Quotient.mk (p := I) x) = counit x := rfl

@[simp]
lemma comul_mk (x : C) :
    comul (R := R) (Submodule.Quotient.mk (p := I) x) = map I.mkQ I.mkQ (comul x) := rfl

/-- `Submodule.mkQ` as a coalgebra homomorphism. -/
@[expose] def mkQCoalgHom : C →ₗc[R] C ⧸ I := ⟨I.mkQ, rfl, rfl⟩

@[simp] lemma mkQCoalgHom_apply (x : C) :
    mkQCoalgHom (R := R) I x = Submodule.Quotient.mk x := rfl

end CoalgebraStruct

variable [Coalgebra R C] (I : Submodule R C) [I.IsCoideal]

instance : Coalgebra R (C ⧸ I) := by
  constructor <;> ext : 1 <;>
    simp only [coassoc_simps, comul_comp_mkQ, counit_comp_mkQ]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl

end Coalgebra.Quotient
