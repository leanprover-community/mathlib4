/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard
-/

import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Ideal.IsPrincipal

/-!
# Relationships between flatness and torsionfreeness.

We show that flat implies torsion-free, and that they're the same
concept for rings satisfying a certain property, including Dedekind
domains and valuation rings.

## Main theorems

* `Module.Flat.isSMulRegular_of_nonZeroDivisors`: Scalar multiplication by a nonzerodivisor of `R`
  is injective on a flat `R`-module.
* `Module.Flat.torsion_eq_bot`: `Torsion R M = ⊥` if `M` is a flat `R`-module.
* `Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localized_maximal`: if localizing `R` at
  the complement of any maximal ideal is a valuation ring then `Torsion R M = ⊥` iff `M` is a
  flat `R`-module.
-/
-- TODO: Add definition and properties of Prüfer domains.
-- TODO: Use `IsTorsionFree`.

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open Submodule (IsPrincipal torsion)

open TensorProduct

namespace Module.Flat

section Semiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

open LinearMap in
/-- Scalar multiplication `m ↦ r • m` by a regular `r` is injective on a flat module. -/
lemma isSMulRegular_of_isRegular {r : R} (hr : IsRegular r) [Flat R M] :
    IsSMulRegular M r := by
  -- `r ∈ R⁰` implies that `toSpanSingleton R R r`, i.e. `(r * ⬝) : R → R` is injective
  -- Flatness implies that corresponding map `R ⊗[R] M →ₗ[R] R ⊗[R] M` is injective
  have h := Flat.rTensor_preserves_injective_linearMap (M := M)
    (toSpanSingleton R R r) <| hr.right
  -- But precomposing and postcomposing with the isomorphism `M ≃ₗ[R] (R ⊗[R] M)`
  -- we get a map `M →ₗ[R] M` which is just `(r • ·)`.
  have h2 : (fun (x : M) ↦ r • x) = ((TensorProduct.lid R M) ∘ₗ
            (rTensor M (toSpanSingleton R R r)) ∘ₗ
            (TensorProduct.lid R M).symm) := by ext; simp
  -- Hence `(r • ·) : M → M` is also injective
  rw [IsSMulRegular, h2]
  simp [h, LinearEquiv.injective]

end Semiring

section Ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open scoped nonZeroDivisors

open LinearMap in

/-- Scalar multiplication `m ↦ r • m` by a nonzerodivisor `r` is injective on a flat module. -/
lemma isSMulRegular_of_nonZeroDivisors {r : R} (hr : r ∈ R⁰) [Flat R M] : IsSMulRegular M r := by
  apply isSMulRegular_of_isRegular
  exact le_nonZeroDivisors_iff_isRegular.mp (le_refl R⁰) ⟨r, hr⟩

/-- Flat modules have no torsion. -/
theorem torsion_eq_bot [Flat R M] : torsion R M = ⊥ := by
  rw [eq_bot_iff]
  -- indeed the definition of torsion means "annihiliated by a nonzerodivisor"
  rintro m ⟨⟨r, hr⟩, h⟩
  -- and we just showed that 0 is the only element with this property
  exact isSMulRegular_of_nonZeroDivisors hr (by simpa using h)

/-- If `R` is Bezout then an `R`-module is flat iff it has no torsion. -/
@[stacks 0539 "Generalized valuation ring to Bezout domain"]
theorem flat_iff_torsion_eq_bot_of_isBezout [IsBezout R] [IsDomain R] :
    Flat R M ↔ torsion R M = ⊥ := by
  -- one way is true in general
  refine ⟨fun _ ↦ torsion_eq_bot, ?_⟩
  -- now assume R is a Bezout domain and M is a torsionfree R-module
  intro htors
  -- we need to show that if I is an ideal of R then the natural map I ⊗ M → M is injective
  rw [iff_lift_lsmul_comp_subtype_injective]
  rintro I hFG
  -- If I = 0 this is obvious because I ⊗ M is a subsingleton (i.e. has ≤1 element)
  obtain (rfl | h) := eq_or_ne I ⊥
  · rintro x y -
    apply Subsingleton.elim
  · -- If I ≠ 0 then I ≅ R because R is Bezout and I is finitely generated
    have hprinc : I.IsPrincipal := IsBezout.isPrincipal_of_FG I hFG
    have : IsPrincipal.generator I ≠ 0 := by
      rwa [ne_eq, ← IsPrincipal.eq_bot_iff_generator_eq_zero]
    apply Function.Injective.of_comp_right _
      (LinearEquiv.rTensor M (Ideal.isoBaseOfIsPrincipal h)).surjective
    rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp, LinearEquiv.coe_rTensor, rTensor,
      lift_comp_map, LinearMap.compl₂_id, LinearMap.comp_assoc,
      Ideal.subtype_isoBaseOfIsPrincipal_eq_mul, LinearMap.lift_lsmul_mul_eq_lsmul_lift_lsmul,
      LinearMap.coe_comp]
    rw [← Submodule.noZeroSMulDivisors_iff_torsion_eq_bot] at htors
    refine Function.Injective.comp (LinearMap.lsmul_injective this) ?_
    rw [← Equiv.injective_comp (TensorProduct.lid R M).symm.toEquiv]
    convert Function.injective_id
    ext
    simp

/-- If every localization of `R` at a maximal ideal is a valuation ring then an `R`-module
is flat iff it has no torsion. -/
theorem flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal [IsDomain R]
    (h : ∀ (P : Ideal R), [P.IsMaximal] → ValuationRing (Localization P.primeCompl)) :
    Flat R M ↔ torsion R M = ⊥ := by
  refine ⟨fun _ ↦ Flat.torsion_eq_bot, fun h ↦ ?_⟩
  apply flat_of_localized_maximal
  intro P hP
  rw [← Submodule.noZeroSMulDivisors_iff_torsion_eq_bot] at h
  rw [← flat_iff_of_isLocalization (Localization P.primeCompl) P.primeCompl,
    Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.noZeroSMulDivisors_iff_torsion_eq_bot]
  infer_instance

/-- If `R` is a Dedekind domain then an `R`-module is flat iff it has no torsion. -/
@[stacks 0AUW "(1)"]
theorem _root_.IsDedekindDomain.flat_iff_torsion_eq_bot [IsDedekindDomain R] :
    Flat R M ↔ torsion R M = ⊥ := by
  apply flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
  exact fun P ↦ inferInstance

instance [IsDedekindDomain R] [NoZeroSMulDivisors R M] : Flat R M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot,
    ← Submodule.noZeroSMulDivisors_iff_torsion_eq_bot]
  infer_instance

end Ring

end Module.Flat
