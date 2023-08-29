/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Polynomial.Basic

#align_import algebraic_geometry.prime_spectrum.is_open_comap_C from "leanprover-community/mathlib"@"052f6013363326d50cb99c6939814a4b8eb7b301"

/-!
The morphism `Spec R[x] --> Spec R` induced by the natural inclusion `R --> R[x]` is an open map.

The main result is the first part of the statement of Lemma 00FB in the Stacks Project.

https://stacks.math.columbia.edu/tag/00FB
-/


open Ideal Polynomial PrimeSpectrum Set

namespace AlgebraicGeometry

namespace Polynomial

variable {R : Type*} [CommRing R] {f : R[X]}

set_option linter.uppercaseLean3 false

/-- Given a polynomial `f ∈ R[x]`, `imageOfDf` is the subset of `Spec R` where at least one
of the coefficients of `f` does not vanish.  Lemma `imageOfDf_eq_comap_C_compl_zeroLocus`
proves that `imageOfDf` is the image of `(zeroLocus {f})ᶜ` under the morphism
`comap C : Spec R[x] → Spec R`. -/
def imageOfDf (f : R[X]) : Set (PrimeSpectrum R) :=
  { p : PrimeSpectrum R | ∃ i : ℕ, coeff f i ∉ p.asIdeal }
#align algebraic_geometry.polynomial.image_of_Df AlgebraicGeometry.Polynomial.imageOfDf

theorem isOpen_imageOfDf : IsOpen (imageOfDf f) := by
  rw [imageOfDf, setOf_exists fun i (x : PrimeSpectrum R) => coeff f i ∉ x.asIdeal]
  -- ⊢ IsOpen (⋃ (i : ℕ), {x | ¬coeff f i ∈ x.asIdeal})
  exact isOpen_iUnion fun i => isOpen_basicOpen
  -- 🎉 no goals
#align algebraic_geometry.polynomial.is_open_image_of_Df AlgebraicGeometry.Polynomial.isOpen_imageOfDf

/-- If a point of `Spec R[x]` is not contained in the vanishing set of `f`, then its image in
`Spec R` is contained in the open set where at least one of the coefficients of `f` is non-zero.
This lemma is a reformulation of `exists_C_coeff_not_mem`. -/
theorem comap_C_mem_imageOfDf {I : PrimeSpectrum R[X]}
    (H : I ∈ (zeroLocus {f} : Set (PrimeSpectrum R[X]))ᶜ) :
    PrimeSpectrum.comap (Polynomial.C : R →+* R[X]) I ∈ imageOfDf f :=
  exists_C_coeff_not_mem (mem_compl_zeroLocus_iff_not_mem.mp H)
#align algebraic_geometry.polynomial.comap_C_mem_image_of_Df AlgebraicGeometry.Polynomial.comap_C_mem_imageOfDf

/-- The open set `imageOfDf f` coincides with the image of `basicOpen f` under the
morphism `C⁺ : Spec R[x] → Spec R`. -/
theorem imageOfDf_eq_comap_C_compl_zeroLocus :
    imageOfDf f = PrimeSpectrum.comap (C : R →+* R[X]) '' (zeroLocus {f})ᶜ := by
  ext x
  -- ⊢ x ∈ imageOfDf f ↔ x ∈ ↑(PrimeSpectrum.comap C) '' (zeroLocus {f})ᶜ
  refine' ⟨fun hx => ⟨⟨map C x.asIdeal, isPrime_map_C_of_isPrime x.IsPrime⟩, ⟨_, _⟩⟩, _⟩
  · rw [mem_compl_iff, mem_zeroLocus, singleton_subset_iff]
    -- ⊢ ¬f ∈ ↑{ asIdeal := Ideal.map C x.asIdeal, IsPrime := (_ : Ideal.IsPrime (Ide …
    cases' hx with i hi
    -- ⊢ ¬f ∈ ↑{ asIdeal := Ideal.map C x.asIdeal, IsPrime := (_ : Ideal.IsPrime (Ide …
    exact fun a => hi (mem_map_C_iff.mp a i)
    -- 🎉 no goals
  · ext x
    -- ⊢ x ∈ (↑(PrimeSpectrum.comap C) { asIdeal := Ideal.map C x✝.asIdeal, IsPrime : …
    refine' ⟨fun h => _, fun h => subset_span (mem_image_of_mem C.1 h)⟩
    -- ⊢ x ∈ x✝.asIdeal
    rw [← @coeff_C_zero R x _]
    -- ⊢ coeff (↑C x) 0 ∈ x✝.asIdeal
    exact mem_map_C_iff.mp h 0
    -- 🎉 no goals
  · rintro ⟨xli, complement, rfl⟩
    -- ⊢ ↑(PrimeSpectrum.comap C) xli ∈ imageOfDf f
    exact comap_C_mem_imageOfDf complement
    -- 🎉 no goals
#align algebraic_geometry.polynomial.image_of_Df_eq_comap_C_compl_zero_locus AlgebraicGeometry.Polynomial.imageOfDf_eq_comap_C_compl_zeroLocus

/-- The morphism `C⁺ : Spec R[x] → Spec R` is open.
Stacks Project "Lemma 00FB", first part.

https://stacks.math.columbia.edu/tag/00FB
-/
theorem isOpenMap_comap_C : IsOpenMap (PrimeSpectrum.comap (C : R →+* R[X])) := by
  rintro U ⟨s, z⟩
  -- ⊢ IsOpen (↑(PrimeSpectrum.comap C) '' U)
  rw [← compl_compl U, ← z, ← iUnion_of_singleton_coe s, zeroLocus_iUnion, compl_iInter,
    image_iUnion]
  simp_rw [← imageOfDf_eq_comap_C_compl_zeroLocus]
  -- ⊢ IsOpen (⋃ (i : ↑s), imageOfDf ↑i)
  exact isOpen_iUnion fun f => isOpen_imageOfDf
  -- 🎉 no goals
#align algebraic_geometry.polynomial.is_open_map_comap_C AlgebraicGeometry.Polynomial.isOpenMap_comap_C

end Polynomial

end AlgebraicGeometry
