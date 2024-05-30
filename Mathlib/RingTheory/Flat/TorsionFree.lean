/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Relationships between flatness and torsionfreeness.

We show that flat implies torsion-free, and that they're the same
concept for PIDs.

## Main theorems

* `Module.Flat.isSMulRegular_of_nonZeroDivisors`: Scalar multiplication by a nonzerodivisor of `R`
  is injective on a flat `R`-module.
* `Module.Flat.torsion_eq_bot`: `Torsion R M = ⊥` if `M` is a flat `R`-module.

-/

universe u v

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

namespace Module.Flat

section Composition

variable {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]

open scoped nonZeroDivisors

open Module LinearMap in
/-- Scalar multiplication `m ↦ r • m` by a nonzerodivisor `r` is injective on a flat module. -/
lemma isSMulRegular_of_nonZeroDivisors {r : R} (hr : r ∈ R⁰) [Flat R M] : IsSMulRegular M r := by
  -- `r ∈ R⁰` implies that `toSpanSingleton R R r`, i.e. `(r * ⬝) : R → R` is injective
  -- Flatness implies that corresponding map `R ⊗[R] M →ₗ[R] R ⊗[R] M` is injective
  have h := Flat.rTensor_preserves_injective_linearMap (M := M)
    (toSpanSingleton R R r) <| (injective_iff_map_eq_zero _).mpr hr
  -- But precomposing and postcomposing with the isomorphism `M ≃ₗ[R] (R ⊗[R] M)`
  -- we get a map `M →ₗ[R] M` which is just `(r • ·)`.
  have h2 : (fun (x : M) ↦ r • x) = ((TensorProduct.lid R M) ∘ₗ
            (rTensor M (toSpanSingleton R R r)) ∘ₗ
            (TensorProduct.lid R M).symm) := by ext; simp
  -- Hence `(r • ·) : M → M` is also injective
  rw [IsSMulRegular, h2]
  simp [h, LinearEquiv.injective]

open Module Submodule in
/-- Flat modules have no torsion. -/
theorem torsion_eq_bot [hflat : Flat R M] : torsion R M = ⊥ := by
  rw [eq_bot_iff]
  -- indeed the definition of torsion means "annihiliated by a nonzerodivisor"
  rintro m ⟨⟨r, hr⟩, (h : r • m = 0)⟩
  -- and we just showed that 0 is the only element with this property
  exact isSMulRegular_of_nonZeroDivisors hr (by simp [h])

-- should be elsewhere
/-- The linear map from R to I sending r to r * g where g is the `generator` of `I`. -/
noncomputable def Ideal.mulGeneratorOfIsPrincipal (I : Ideal R) [hprinc : I.IsPrincipal] :
    R →ₗ[R] I where
  toFun r := ⟨r * hprinc.generator, I.mul_mem_left r <| hprinc.generator_mem⟩
  map_add' _ _ := Subtype.ext <| add_mul _ _ _
  map_smul' _ _ := Subtype.ext <| mul_assoc _ _ _

-- should be elsewhere
variable {R : Type*} [CommRing R]
  variable {M : Type*} [AddCommGroup M] [Module R M]
  variable {M' : Type*} [AddCommGroup M'] [Module R M'] in
noncomputable def LinearMap.EquivOfKerEqBotOfSurjective
    (φ : M' →ₗ[R] M) (h1 : LinearMap.ker φ = ⊥) (h2 : Function.Surjective φ) :
    M' ≃ₗ[R] M := { φ with
  invFun := fun m' ↦ (h2 m').choose
  left_inv := fun m ↦ by
    rw [LinearMap.ker_eq_bot] at h1
    exact h1 <| (h2 (φ m)).choose_spec
  right_inv := fun m' ↦ (h2 m').choose_spec
  }

noncomputable def Ideal.isoBaseOfIsPrincipal {I : Ideal R} [IsDomain R] [hprinc : I.IsPrincipal]
    (hI : I ≠ ⊥) : R ≃ₗ[R] I :=
  LinearMap.EquivOfKerEqBotOfSurjective (I.mulGeneratorOfIsPrincipal)
  (by
    rw [eq_bot_iff]
    intro m h
    rw [LinearMap.mem_ker] at h
    apply (AddSubmonoid.mk_eq_zero _).mp at h
    rw [Ideal.mem_bot]
    refine eq_zero_of_ne_zero_of_mul_right_eq_zero ?_ h
    refine mt (fun h3 ↦ ?_) hI
    rwa [Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I])
  (by
    rintro ⟨i, hi⟩
    rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator] at hi
    obtain ⟨s, rfl⟩ := hi
    exact ⟨s, rfl⟩)

open Module Submodule in
/-- If `R` is a PID then an `R`-module is flat iff it has no torsion. -/
theorem flat_iff_torsion_eq_bot [IsPrincipalIdealRing R] [IsDomain R] :
    Flat R M ↔ torsion R M = ⊥ := by
  refine ⟨?_, ?_⟩
    -- one way is true in general
  · apply torsion_eq_bot
    -- now assume R is a PID and M is a torsionfree R-module
  · intro htors
    -- we need to show that if I is an ideal of R then the natural map I ⊗ M → M is injective
    constructor
    rintro I -
    -- If I = 0 this is obvious because I ⊗ M is a subsingleton (i.e. has ≤1 element)
    obtain (rfl | h) := eq_or_ne I ⊥
    · rintro x y -
      apply Subsingleton.elim
    · -- If I ≠ 0 then I ≅ R because R is a PID
      apply Function.Injective.of_comp_right _
        (LinearEquiv.rTensor M (Ideal.IsoBaseOfPrincipal h)).surjective
      rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]

      sorry
