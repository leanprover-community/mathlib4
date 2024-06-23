/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-!

# Localization of multivariate polynomial rings

If `S` is the localization of `R` at a submonoid `M`, then `MvPolynomial σ S`
is the localization of `MvPolynomial σ R` at the image of `M` in `MvPolynomial σ R`.

-/

open Classical

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] (M : Submonoid R)
variable (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]

attribute [local instance] algebraMvPolynomial

/--
If `S` is the localization of `R` at a submonoid `M`, then `MvPolynomial σ S`
is the localization of `MvPolynomial σ R` at `M.map MvPolynomial.C`.
-/
instance isLocalization : IsLocalization (M.map <| C (σ := σ))
    (MvPolynomial σ S) where
  map_units' := by
    rintro ⟨p, q, hq, rfl⟩
    simp only [algebraMap_def, map_C]
    exact IsUnit.map _ (IsLocalization.map_units _ ⟨q, hq⟩)
  surj' p := by
    simp only [algebraMap_def, Prod.exists, Subtype.exists,
      Submonoid.mem_map, exists_prop, exists_exists_and_eq_and, map_C]
    refine induction_on' p ?_ ?_
    · intro u s
      obtain ⟨⟨r, m⟩, hr⟩ := IsLocalization.surj M s
      use monomial u r, m, m.property
      simp only [map_monomial]
      rw [← hr, mul_comm, C_mul_monomial, mul_comm]
    · intro p p' ⟨x, m, hm, hxm⟩ ⟨x', m', hm', hxm'⟩
      use x * (C m') + x' * (C m), m * m', Submonoid.mul_mem _ hm hm'
      simp only [map_mul, map_add, map_C]
      rw [add_mul, ← mul_assoc, hxm, ← mul_assoc, ← hxm, ← hxm']
      ring
  exists_of_eq {p q} := by
    intro h
    simp_rw [algebraMap_def, ext_iff, coeff_map] at h
    choose c hc using (fun m ↦ IsLocalization.exists_of_eq (M := M) (h m))
    simp only [Subtype.exists, Submonoid.mem_map, exists_prop, exists_exists_and_eq_and]
    refine ⟨Finset.prod (p.support ∪ q.support) (fun m ↦ c m), ?_, ?_⟩
    · exact M.prod_mem (fun m _ ↦ (c m).property)
    · ext m
      simp only [coeff_C_mul]
      by_cases h : m ∈ p.support ∪ q.support
      · exact Finset.prod_mul_eq_prod_mul_of_exists m h (hc m)
      · simp only [Finset.mem_union, mem_support_iff, ne_eq, not_or, Decidable.not_not] at h
        rw [h.left, h.right]

lemma isLocalization_C_mk' (a : R) (m : M) :
    C (IsLocalization.mk' S a m) = IsLocalization.mk' (MvPolynomial σ S) (C (σ := σ) a)
      ⟨C m, Submonoid.mem_map_of_mem C m.property⟩ := by
  simp_rw [IsLocalization.eq_mk'_iff_mul_eq, algebraMap_def, map_C, ← map_mul,
    IsLocalization.mk'_spec]

end MvPolynomial
