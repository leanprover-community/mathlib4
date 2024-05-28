/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Eric Rodriguez
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.NormTrace

#align_import number_theory.number_field.norm from "leanprover-community/mathlib"@"00f91228655eecdcd3ac97a7fd8dbcb139fe990a"

/-!
# Norm in number fields
Given a finite extension of number fields, we define the norm morphism as a function between the
rings of integers.

## Main definitions
* `RingOfIntegers.norm K` : `Algebra.norm` as a morphism `(𝓞 L) →* (𝓞 K)`.
## Main results
* `RingOfIntegers.dvd_norm` : if `L/K` is a finite Galois extension of fields, then, for all
  `(x : 𝓞 L)` we have that `x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x)`.

-/


open scoped NumberField

open Finset NumberField Algebra FiniteDimensional

section Rat

variable {K : Type*} [Field K] [NumberField K] (x : 𝓞 K)

theorem Algebra.coe_norm_int : (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : K) :=
  (Algebra.norm_localization (R := ℤ) (Rₘ := ℚ) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors ℤ) x).symm

theorem Algebra.coe_trace_int : (Algebra.trace ℤ _ x : ℚ) = Algebra.trace ℚ K (x : K) :=
  (Algebra.trace_localization (R := ℤ) (Rₘ := ℚ) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors ℤ) x).symm

end Rat

namespace RingOfIntegers

variable {L : Type*} (K : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- `Algebra.norm` as a morphism betwen the rings of integers. -/
noncomputable def norm [IsSeparable K L] : 𝓞 L →* 𝓞 K :=
  RingOfIntegers.restrict_monoidHom
    ((Algebra.norm K).comp (algebraMap (𝓞 L) L : (𝓞 L) →* L))
    fun x => isIntegral_norm K x.2
#align ring_of_integers.norm RingOfIntegers.norm

@[simp] lemma coe_norm [IsSeparable K L] (x : 𝓞 L) :
  norm K x = Algebra.norm K (x : L) := rfl

theorem coe_algebraMap_norm [IsSeparable K L] (x : 𝓞 L) :
    (algebraMap (𝓞 K) (𝓞 L) (norm K x) : L) = algebraMap K L (Algebra.norm K (x : L)) :=
  rfl
#align ring_of_integers.coe_algebra_map_norm RingOfIntegers.coe_algebraMap_norm

theorem algebraMap_norm_algebraMap [IsSeparable K L] (x : 𝓞 K) :
    algebraMap _ K (norm K (algebraMap (𝓞 K) (𝓞 L) x)) =
      Algebra.norm K (algebraMap K L (algebraMap _ _ x)) := rfl
#align ring_of_integers.coe_norm_algebra_map RingOfIntegers.algebraMap_norm_algebraMap

theorem norm_algebraMap [IsSeparable K L] (x : 𝓞 K) :
    norm K (algebraMap (𝓞 K) (𝓞 L) x) = x ^ finrank K L := by
  rw [RingOfIntegers.ext_iff, RingOfIntegers.coe_eq_algebraMap,
    RingOfIntegers.algebraMap_norm_algebraMap, Algebra.norm_algebraMap,
    RingOfIntegers.coe_eq_algebraMap, map_pow]
#align ring_of_integers.norm_algebra_map RingOfIntegers.norm_algebraMap

theorem isUnit_norm_of_isGalois [IsGalois K L] {x : 𝓞 L} : IsUnit (norm K x) ↔ IsUnit x := by
  classical
  refine ⟨fun hx => ?_, IsUnit.map _⟩
  replace hx : IsUnit (algebraMap (𝓞 K) (𝓞 L) <| norm K x) := hx.map (algebraMap (𝓞 K) <| 𝓞 L)
  refine @isUnit_of_mul_isUnit_right (𝓞 L) _
    ⟨(univ \ {AlgEquiv.refl}).prod fun σ : L ≃ₐ[K] L => σ x,
      prod_mem fun σ _ => x.2.map (σ : L →+* L).toIntAlgHom⟩ _ ?_
  convert hx using 1
  ext
  convert_to ((univ \ {AlgEquiv.refl}).prod fun σ : L ≃ₐ[K] L => σ x) *
    ∏ σ ∈ {(AlgEquiv.refl : L ≃ₐ[K] L)}, σ x = _
  · rw [prod_singleton, AlgEquiv.coe_refl, _root_.id, RingOfIntegers.coe_eq_algebraMap, map_mul,
      RingOfIntegers.map_mk]
  · rw [prod_sdiff <| subset_univ _, ← norm_eq_prod_automorphisms, coe_algebraMap_norm]
#align ring_of_integers.is_unit_norm_of_is_galois RingOfIntegers.isUnit_norm_of_isGalois

/-- If `L/K` is a finite Galois extension of fields, then, for all `(x : 𝓞 L)` we have that
`x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x)`. -/
theorem dvd_norm [IsGalois K L] (x : 𝓞 L) : x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x) := by
  classical
  have hint :
    IsIntegral ℤ (∏ σ ∈ univ.erase (AlgEquiv.refl : L ≃ₐ[K] L), σ x) :=
    IsIntegral.prod _ (fun σ _ =>
      ((RingOfIntegers.isIntegral_coe x).map σ))
  refine ⟨⟨_, hint⟩, ?_⟩
  ext
  rw [coe_algebraMap_norm K x, norm_eq_prod_automorphisms]
  simp [← Finset.mul_prod_erase _ _ (mem_univ AlgEquiv.refl)]
#align ring_of_integers.dvd_norm RingOfIntegers.dvd_norm

variable (F : Type*) [Field F] [Algebra K F] [IsSeparable K F] [FiniteDimensional K F]

theorem norm_norm [IsSeparable K L] [Algebra F L] [IsSeparable F L] [FiniteDimensional F L]
    [IsScalarTower K F L] (x : 𝓞 L) : norm K (norm F x) = norm K x := by
  rw [RingOfIntegers.ext_iff, coe_norm, coe_norm, coe_norm, Algebra.norm_norm]
#align ring_of_integers.norm_norm RingOfIntegers.norm_norm

variable {F}

theorem isUnit_norm [CharZero K] {x : 𝓞 F} : IsUnit (norm K x) ↔ IsUnit x := by
  letI : Algebra K (AlgebraicClosure K) := AlgebraicClosure.instAlgebra K
  let L := normalClosure K F (AlgebraicClosure F)
  haveI : FiniteDimensional F L := FiniteDimensional.right K F L
  haveI : IsAlgClosure K (AlgebraicClosure F) :=
    IsAlgClosure.ofAlgebraic K F (AlgebraicClosure F)
  haveI : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  calc
    IsUnit (norm K x) ↔ IsUnit ((norm K) x ^ finrank F L) :=
      (isUnit_pow_iff (pos_iff_ne_zero.mp finrank_pos)).symm
    _ ↔ IsUnit (norm K (algebraMap (𝓞 F) (𝓞 L) x)) := by
      rw [← norm_norm K F (algebraMap (𝓞 F) (𝓞 L) x), norm_algebraMap F _, map_pow]
    _ ↔ IsUnit (algebraMap (𝓞 F) (𝓞 L) x) := isUnit_norm_of_isGalois K
    _ ↔ IsUnit (norm F (algebraMap (𝓞 F) (𝓞 L) x)) := (isUnit_norm_of_isGalois F).symm
    _ ↔ IsUnit (x ^ finrank F L) := (congr_arg IsUnit (norm_algebraMap F _)).to_iff
    _ ↔ IsUnit x := isUnit_pow_iff (pos_iff_ne_zero.mp finrank_pos)
#align ring_of_integers.is_unit_norm RingOfIntegers.isUnit_norm

end RingOfIntegers
