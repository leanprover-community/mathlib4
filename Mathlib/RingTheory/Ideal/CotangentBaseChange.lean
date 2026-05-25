/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of cotangent spaces

Given an `R`-algebra `S`, an ideal `I` of `S` and a flat `R`-algebra `T`, we show that
the base change `T ⊗[R] I/I²` of the cotangent space of `I` is naturally isomorphic to the
cotangent space of the extended ideal `I · (T ⊗[R] S)`.

## Main definitions

- `Ideal.tensorCotangentHom`: The canonical map `T ⊗[R] I/I² → (I · (T ⊗[R] S))/(I · (T ⊗[R] S))²`.
- `Ideal.tensorCotangentEquiv`: When `T` is `R`-flat, `tensorCotangentHom` is an isomorphism.
-/

@[expose] public noncomputable section

universe u

open TensorProduct

namespace Ideal

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T] (I : Ideal S)

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The canonical map from the base change of the cotangent space `T ⊗[R] I/I²` to the
cotangent space `(I · (T ⊗[R] S))/(I · (T ⊗[R] S))²` of the extended ideal.
This map is always surjective (`tensorCotangentHom_surjective`) and injective
if `T` is `R`-flat (`tensorCotangentHom_injective_of_flat`). -/
def tensorCotangentHom :
    T ⊗[R] I.Cotangent →ₗ[T]
      (I.map <| (Algebra.TensorProduct.includeRight.toRingHom : S →+* T ⊗[R] S)).Cotangent :=
  let a : S →+* T ⊗[R] S := Algebra.TensorProduct.includeRight.toRingHom
  letI : IsScalarTower R (T ⊗[R] S) (I.map a).Cotangent :=
    Submodule.Quotient.isScalarTower
      (P := ((I.map a) • ⊤ : Submodule (T ⊗[R] S) (I.map a)))
      (S := R) (T := T ⊗[R] S)
  letI : LinearMap.CompatibleSMul (I.map a) (I.map a).Cotangent R (T ⊗[R] S) :=
    LinearMap.IsScalarTower.compatibleSMul
  LinearMap.liftBaseChange T <|
    Cotangent.lift
      ((I.map a).toCotangent.restrictScalars R ∘ₗ
        (Algebra.idealMap _ I).restrictScalars R) <| fun x y ↦ by
    simp only [AlgHom.toRingHom_eq_coe, LinearMap.coe_comp, Function.comp_apply]
    exact ((I.map a).toCotangent_eq_zero _).mpr <| by
      have h :
          ((((Algebra.idealMap (T ⊗[R] S) I).restrictScalars R) (x * y) :
              I.map a) : T ⊗[R] S) =
            ((Algebra.idealMap (T ⊗[R] S) I) x : T ⊗[R] S) *
              ((Algebra.idealMap (T ⊗[R] S) I) y : T ⊗[R] S) := by
        exact congrArg Subtype.val (Algebra.idealMap_mul (T ⊗[R] S) I x y)
      exact h.symm ▸ (by
        simpa [sq] using mul_mem_mul ((Algebra.idealMap (T ⊗[R] S) I) x).property
          ((Algebra.idealMap (T ⊗[R] S) I) y).property)

-- TODO: make this @[simp] when `Ideal.map` is refactored to only take `RingHom`s
lemma tensorCotangentHom_tmul (t : T) (x : I) :
    tensorCotangentHom R T I (t ⊗ₜ[R] I.toCotangent x) =
      t • (I.map Algebra.TensorProduct.includeRight.toRingHom).toCotangent
        ⟨1 ⊗ₜ x, Ideal.mem_map_of_mem _ x.2⟩ := by
  rw [tensorCotangentHom, LinearMap.liftBaseChange_tmul, Cotangent.lift_toCotangent]
  congr 1

lemma tensorCotangentHom_surjective :
    Function.Surjective (I.tensorCotangentHom R T) := by
  let a : S →+* T ⊗[R] S := Algebra.TensorProduct.includeRight.toRingHom
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  obtain ⟨y, rfl⟩ := I.map_includeRight_eq.le hx
  obtain rfl : hx = I.map_includeRight_eq.ge ⟨y, rfl⟩ := rfl
  induction y with
  | zero => exact ⟨0, by simp only [map_zero]; exact (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb]; rfl⟩
  | tmul t x =>
    use t ⊗ₜ I.toCotangent x
    apply Ideal.cotangentToQuotientSquare_injective
    simp [-AlgHom.toRingHom_eq_coe, tensorCotangentHom_tmul, Algebra.smul_def,
      ← Ideal.Quotient.mk_algebraMap, ← map_mul]

/-- If `T` is a flat `R`-module, the canonical map `tensorCotangentHom R T I` is injective. -/
lemma tensorCotangentHom_injective_of_flat [Module.Flat R T] :
    Function.Injective (I.tensorCotangentHom R T) := by
  let a : S →+* T ⊗[R] S := Algebra.TensorProduct.includeRight.toRingHom
  letI : IsScalarTower T (T ⊗[R] S) (I.map a).Cotangent :=
    Submodule.Quotient.isScalarTower
      (P := ((I.map a) • ⊤ : Submodule (T ⊗[R] S) (I.map a)))
      (S := T) (T := T ⊗[R] S)
  letI : LinearMap.CompatibleSMul (I.map a).Cotangent (T ⊗[R] S ⧸ (I.map a) ^ 2)
      T (T ⊗[R] S) :=
    LinearMap.IsScalarTower.compatibleSMul
  let f : (I.map a).Cotangent →ₗ[T] T ⊗[R] S ⧸ (I.map a) ^ 2 :=
    (Ideal.cotangentToQuotientSquare _).restrictScalars T
  suffices h : Function.Injective (f ∘ₗ tensorCotangentHom R T I) from .of_comp h
  let g : T ⊗[R] I.Cotangent →ₗ[T] T ⊗[R] (S ⧸ I ^ 2) :=
    AlgebraTensorModule.lTensor T T I.cotangentToQuotientSquare
  let hₐ : T ⊗[R] (S ⧸ I ^ 2) ≃ₐ[T] T ⊗[R] S ⧸ (I.map a) ^ 2 :=
    (Algebra.TensorProduct.tensorQuotientEquiv _ _ _ _).trans
      (Ideal.quotientEquivAlgOfEq T (Ideal.map_pow _ _ _))
  have : f ∘ₗ tensorCotangentHom R T I = hₐ.toLinearMap ∘ₗ g := by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    dsimp [f, g, hₐ]
    rw [tensorCotangentHom_tmul, one_smul, Ideal.toCotangent_to_quotient_square]
    rfl
  rw [this, LinearMap.coe_comp]
  apply hₐ.injective.comp
  · apply Module.Flat.lTensor_preserves_injective_linearMap (M := T)
      (I.cotangentToQuotientSquare.restrictScalars R)
    apply cotangentToQuotientSquare_injective

/-- If `T` is a flat `R`-module, the base change of the cotangent space of `I` is linearly
equivalent to the cotangent space of the extended ideal `I · (T ⊗[R] S)`. -/
def tensorCotangentEquiv [Module.Flat R T] :
    T ⊗[R] I.Cotangent ≃ₗ[T]
      (I.map (Algebra.TensorProduct.includeRight.toRingHom : _ →+* T ⊗[R] S)).Cotangent :=
  LinearEquiv.ofBijective (I.tensorCotangentHom R T)
    ⟨I.tensorCotangentHom_injective_of_flat R T, I.tensorCotangentHom_surjective R T⟩

-- TODO: make this @[simp] when `Ideal.map` is refactored to only take `RingHom`s
lemma tensorCotangentEquiv_tmul [Module.Flat R T] (t : T) (x : I) :
    I.tensorCotangentEquiv R T (t ⊗ₜ I.toCotangent x) =
      t • (I.map Algebra.TensorProduct.includeRight.toRingHom).toCotangent
        ⟨1 ⊗ₜ x, Ideal.mem_map_of_mem _ x.2⟩ :=
  tensorCotangentHom_tmul R T I t x

end Ideal
