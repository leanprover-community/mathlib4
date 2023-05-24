/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebraic_geometry.prime_spectrum.is_open_comap_C
! leanprover-community/mathlib commit 052f6013363326d50cb99c6939814a4b8eb7b301
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathbin.RingTheory.Polynomial.Basic

/-!
The morphism `Spec R[x] --> Spec R` induced by the natural inclusion `R --> R[x]` is an open map.

The main result is the first part of the statement of Lemma 00FB in the Stacks Project.

https://stacks.math.columbia.edu/tag/00FB
-/


open Ideal Polynomial PrimeSpectrum Set

open Polynomial

namespace AlgebraicGeometry

namespace Polynomial

variable {R : Type _} [CommRing R] {f : R[X]}

/-- Given a polynomial `f ∈ R[x]`, `image_of_Df` is the subset of `Spec R` where at least one
of the coefficients of `f` does not vanish.  Lemma `image_of_Df_eq_comap_C_compl_zero_locus`
proves that `image_of_Df` is the image of `(zero_locus {f})ᶜ` under the morphism
`comap C : Spec R[x] → Spec R`. -/
def imageOfDf (f) : Set (PrimeSpectrum R) :=
  { p : PrimeSpectrum R | ∃ i : ℕ, coeff f i ∉ p.asIdeal }
#align algebraic_geometry.polynomial.image_of_Df AlgebraicGeometry.Polynomial.imageOfDf

theorem isOpen_imageOfDf : IsOpen (imageOfDf f) :=
  by
  rw [image_of_Df, set_of_exists fun i (x : PrimeSpectrum R) => coeff f i ∉ x.asIdeal]
  exact isOpen_iUnion fun i => is_open_basic_open
#align algebraic_geometry.polynomial.is_open_image_of_Df AlgebraicGeometry.Polynomial.isOpen_imageOfDf

/-- If a point of `Spec R[x]` is not contained in the vanishing set of `f`, then its image in
`Spec R` is contained in the open set where at least one of the coefficients of `f` is non-zero.
This lemma is a reformulation of `exists_C_coeff_not_mem`. -/
theorem comap_c_mem_imageOfDf {I : PrimeSpectrum R[X]}
    (H : I ∈ (zeroLocus {f} : Set (PrimeSpectrum R[X]))ᶜ) :
    PrimeSpectrum.comap (Polynomial.C : R →+* R[X]) I ∈ imageOfDf f :=
  exists_C_coeff_not_mem (mem_compl_zeroLocus_iff_not_mem.mp H)
#align algebraic_geometry.polynomial.comap_C_mem_image_of_Df AlgebraicGeometry.Polynomial.comap_c_mem_imageOfDf

/-- The open set `image_of_Df f` coincides with the image of `basic_open f` under the
morphism `C⁺ : Spec R[x] → Spec R`. -/
theorem imageOfDf_eq_comap_c_compl_zeroLocus :
    imageOfDf f = PrimeSpectrum.comap (C : R →+* R[X]) '' zeroLocus {f}ᶜ :=
  by
  ext x
  refine' ⟨fun hx => ⟨⟨map C x.as_ideal, is_prime_map_C_of_is_prime x.is_prime⟩, ⟨_, _⟩⟩, _⟩
  · rw [mem_compl_iff, mem_zero_locus, singleton_subset_iff]
    cases' hx with i hi
    exact fun a => hi (mem_map_C_iff.mp a i)
  · ext x
    refine' ⟨fun h => _, fun h => subset_span (mem_image_of_mem C.1 h)⟩
    rw [← @coeff_C_zero R x _]
    exact mem_map_C_iff.mp h 0
  · rintro ⟨xli, complement, rfl⟩
    exact comap_C_mem_image_of_Df complement
#align algebraic_geometry.polynomial.image_of_Df_eq_comap_C_compl_zero_locus AlgebraicGeometry.Polynomial.imageOfDf_eq_comap_c_compl_zeroLocus

/-- The morphism `C⁺ : Spec R[x] → Spec R` is open.
Stacks Project "Lemma 00FB", first part.

https://stacks.math.columbia.edu/tag/00FB
-/
theorem isOpenMap_comap_c : IsOpenMap (PrimeSpectrum.comap (C : R →+* R[X])) :=
  by
  rintro U ⟨s, z⟩
  rw [← compl_compl U, ← z, ← Union_of_singleton_coe s, zero_locus_Union, compl_Inter, image_Union]
  simp_rw [← image_of_Df_eq_comap_C_compl_zero_locus]
  exact isOpen_iUnion fun f => is_open_image_of_Df
#align algebraic_geometry.polynomial.is_open_map_comap_C AlgebraicGeometry.Polynomial.isOpenMap_comap_c

end Polynomial

end AlgebraicGeometry

