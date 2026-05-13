/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Projection
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Ideal.Maps

/-! # Augmentation ideals

## Main definitions

* `Ideal.IsAugmentation` :  An ideal `I` of an `A`-algebra `S` is an augmentation ideal
  if its underlying submodule is a complement of `1 : Submodule A S`.

* `Ideal.isAugmentation_subalgebra_iff` : If `S` is a subalgebra of an `R`-algebra `A`,
  then an ideal `I`of `A` is an augmentation ideal for the `R`-algebra structure if and only if
  it is an augmentation ideal for the `S`-algebra structure.

## Main results

* `Ideal.isAugmentation_baseChange`: if `R` is a `CommRing` and an `A`-algebra,
then the ideal `R ⊗[A] I` of `R ⊗[A] S` is an augmentation ideal.

## Notes

* There is a weaker version that holds for general commutative rings and would just assert that the
  quotient map `R →+* R ⧸ I` has a section which is a ring homomorphism (possibly with a variant
  “with data” that keeps track of the choice of one such section).

-/

@[expose] public section

namespace Ideal

variable (R : Type*) [CommSemiring R] {A : Type*}

open Submodule Subalgebra

/-- An ideal `I` of an `R`-algebra `A` is an augmentation ideal
if its underlying module is a complement to `1 : Submodule R A`. -/
def IsAugmentation [Semiring A] [Algebra R A] (I : Ideal A) : Prop :=
  IsCompl 1 (I.restrictScalars R)

lemma isAugmentation_iff [Semiring A] [Algebra R A] (I : Ideal A) :
    I.IsAugmentation R ↔ IsCompl 1 (I.restrictScalars R) := Iff.rfl

/-- If `S` is a subalgebra of an `R`-algebra `A`, then an ideal `I`of `A` is an augmentation ideal
for the `R`-algebra structure
if and only if it is an augmentation ideal for the `S`-algebra structure. -/
theorem isAugmentation_subalgebra_iff [CommSemiring A] [Algebra R A]
    {S : Subalgebra R A} {I : Ideal A} :
    I.IsAugmentation S ↔ IsCompl S.toSubmodule (I.restrictScalars R) := by
  simp [Ideal.IsAugmentation, ← Submodule.isCompl_restrictScalars_iff R]

variable [CommSemiring A] [Algebra A R] (J : Ideal A)

open TensorProduct Ideal LinearMap Submodule Algebra.TensorProduct

/-- If `I` is an augmentation ideal of the `A`-algebra `R` and `R` is an `A`-algebra,
then the ideal `R ⊗[A] I` of `R ⊗[A] S` is an augmentation ideal. -/
theorem isAugmentation_baseChange
    {A : Type*} [CommRing A]
    {R : Type*} [CommRing R] [Algebra A R]
    {S : Type*} [Ring S] [Algebra A S]
    {I : Ideal S} (hI : IsAugmentation A I) :
    (I.map includeRight : Ideal (R ⊗[A] S)).IsAugmentation R := by
  rw [isAugmentation_iff, map_includeRight_eq_range_baseChange,
    Algebra.baseChange_one]
  exact isCompl_baseChange hI R

section

variable {A M M' N N' : Type*} [CommSemiring A]
    [AddCommMonoid M] [Module A M] [AddCommMonoid M'] [Module A M'] (f : M →ₗ[A] M')
    [AddCommMonoid N] [Module A N] [AddCommMonoid N'] [Module A N'] (g : N →ₗ[A] N')

theorem _root_.LinearMap.subtype_comp_rangeRestrict :
    f.range.subtype ∘ₗ f.rangeRestrict = f := by
  rw [rangeRestrict, subtype_comp_codRestrict]

theorem _root_.TensorProduct.map_range_eq :
    (TensorProduct.map f g).range = (TensorProduct.map f.range.subtype g.range.subtype).range := by
  nth_rewrite 1 [← subtype_comp_rangeRestrict f]
  nth_rewrite 1 [← subtype_comp_rangeRestrict g]
  rw [TensorProduct.map_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  exact TensorProduct.map_surjective (surjective_rangeRestrict f)
    (surjective_rangeRestrict g)

#find_home! TensorProduct.map_range_eq
end

theorem isAugmentation_tensorProduct
    (A : Type*) [CommRing A] {R S : Type*} [CommRing R]
    [Algebra A R] {R₀ : Subalgebra A R} {I : Ideal R} (hI : I.IsAugmentation R₀) [CommRing S]
    [Algebra A S] {S₀ : Subalgebra A S} {J : Ideal S} (hJ : J.IsAugmentation S₀) :
    let K : Ideal (R ⊗[A] S) := I.map (includeLeft (S := A)) ⊔
      J.map Algebra.TensorProduct.includeRight
    let T₀ : Subalgebra A (R ⊗[A] S) := Subalgebra.map (Algebra.TensorProduct.map R₀.val S₀.val) ⊤
    K.IsAugmentation T₀ := by
  rw [isAugmentation_subalgebra_iff] at hI hJ ⊢
  convert isCompl_left_left hI hJ
  · simp only [Submodule.TensorProduct, Algebra.map_top, mapIncl]
    rw [← SetLike.coe_set_eq, Subalgebra.coe_toSubmodule, AlgHom.coe_range,
      ← AlgHom.coe_toLinearMap, ← LinearMap.coe_range,
        toLinearMap_map, AlgebraTensorModule.map_eq]
    simp [AlgHom.toLinearMap_eq_coe]
  · simp only [restrictScalars_sup, Submodule.TensorProduct, mapIncl]
    rw [sup_comm]
    apply congr_arg₂
    · simp only [Ideal.map_includeRight_eq, LinearMap.lTensor]
      rw [← id_comp (⊤: Submodule A R).subtype,
        ← comp_id (Submodule.restrictScalars A J).subtype, TensorProduct.map_comp, range_comp,
        comp_id, LinearMap.range_eq_map]
      congr
      rw [eq_comm, range_eq_top]
      apply TensorProduct.map_surjective _ Function.surjective_id
      rw [← LinearMap.range_eq_top, range_subtype]
    · simp only [Ideal.map_includeLeft_eq, LinearMap.rTensor]
      rw [← id_comp (⊤: Submodule A S).subtype,
        ← comp_id (Submodule.restrictScalars A I).subtype, TensorProduct.map_comp, range_comp,
        comp_id, LinearMap.range_eq_map]
      congr
      rw [eq_comm, range_eq_top]
      apply TensorProduct.map_surjective Function.surjective_id
      rw [← LinearMap.range_eq_top, range_subtype]

end Ideal

end
