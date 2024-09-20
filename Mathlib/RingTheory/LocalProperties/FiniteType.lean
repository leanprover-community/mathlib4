/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalProperties.Finite

/-!
# `RingHom.FiniteType` is a local property

In this file, we prove that `RingHom.FiniteType` is a local property.


## Main results

Let `R` be a commutative ring, `S` is an `R`-algebra, `M` be a submonoid of `R`.

* `localization_finiteType` : If `S` is a finite type `R`-algebra, then `S' = M⁻¹S` is a
  finite type `R' = M⁻¹R`-algebra.
* `finiteType_ofLocalizationSpan` : `S` is a finite type `R`-algebra if there exists
  a set `{ r }` that spans `R` such that `Sᵣ` is a finite type `Rᵣ`-algebra.

-/

open scoped Pointwise Classical

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (M : Submonoid R) (f : R →+* S)
variable (R' S' : Type u) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

/-- If `S` is a finite type `R`-algebra, then `S' = M⁻¹S` is a finite type `R' = M⁻¹R`-algebra. -/
theorem localization_finiteType : RingHom.LocalizationPreserves @RingHom.FiniteType := by
  introv R hf
  -- mirrors the proof of `localization_map_finite`
  letI := f.toAlgebra
  letI := ((algebraMap S S').comp f).toAlgebra
  let f' : R' →+* S' := IsLocalization.map S' f (Submonoid.le_comap_map M)
  letI := f'.toAlgebra
  haveI : IsScalarTower R R' S' :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp M.le_comap_map).symm
  let fₐ : S →ₐ[R] S' := AlgHom.mk' (algebraMap S S') fun c x => RingHom.map_mul _ _ _
  obtain ⟨T, hT⟩ := id hf
  use T.image (algebraMap S S')
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, ⟨_, ⟨r, hr, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (M.map f) x
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm, Finset.coe_image]
  have hy : y ∈ Algebra.adjoin R (T : Set S) := by rw [hT]; trivial
  replace hy : algebraMap S S' y ∈ (Algebra.adjoin R (T : Set S)).map fₐ :=
    Subalgebra.mem_map.mpr ⟨_, hy, rfl⟩
  rw [fₐ.map_adjoin T] at hy
  have H : Algebra.adjoin R (algebraMap S S' '' T) ≤
      (Algebra.adjoin R' (algebraMap S S' '' T)).restrictScalars R := by
    rw [Algebra.adjoin_le_iff]; exact Algebra.subset_adjoin
  convert (Algebra.adjoin R' (algebraMap S S' '' T)).smul_mem (H hy)
    (IsLocalization.mk' R' (1 : R) ⟨r, hr⟩) using 1
  rw [Algebra.smul_def]
  erw [IsLocalization.map_mk' M.le_comap_map]
  rw [map_one]

theorem localization_away_map_finiteType (r : R) [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'] (hf : f.FiniteType) :
    (IsLocalization.Away.map R' S' f r).FiniteType :=
  localization_finiteType.away r hf

variable {S'}

/-- Let `S` be an `R`-algebra, `M` a submonoid of `S`, `S' = M⁻¹S`.
Suppose the image of some `x : S` falls in the adjoin of some finite `s ⊆ S'` over `R`,
and `A` is an `R`-subalgebra of `S` containing both `M` and the numerators of `s`.
Then, there exists some `m : M` such that `m • x` falls in `A`.
-/
theorem IsLocalization.exists_smul_mem_of_mem_adjoin [Algebra R S] [Algebra R S']
    [IsScalarTower R S S'] (M : Submonoid S) [IsLocalization M S'] (x : S) (s : Finset S')
    (A : Subalgebra R S) (hA₁ : (IsLocalization.finsetIntegerMultiple M s : Set S) ⊆ A)
    (hA₂ : M ≤ A.toSubmonoid) (hx : algebraMap S S' x ∈ Algebra.adjoin R (s : Set S')) :
    ∃ m : M, m • x ∈ A := by
  let g : S →ₐ[R] S' := IsScalarTower.toAlgHom R S S'
  let y := IsLocalization.commonDenomOfFinset M s
  have hx₁ : (y : S) • (s : Set S') = g '' _ :=
    (IsLocalization.finsetIntegerMultiple_image _ s).symm
  obtain ⟨n, hn⟩ :=
    Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin (y : S) (s : Set S') (A.map g)
      (by rw [hx₁]; exact Set.image_subset _ hA₁) hx (Set.mem_image_of_mem _ (hA₂ y.2))
  obtain ⟨x', hx', hx''⟩ := hn n (le_of_eq rfl)
  rw [Algebra.smul_def, ← _root_.map_mul] at hx''
  obtain ⟨a, ha₂⟩ := (IsLocalization.eq_iff_exists M S').mp hx''
  use a * y ^ n
  convert A.mul_mem hx' (hA₂ a.prop) using 1
  rw [Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow, mul_assoc, ← ha₂,
    mul_comm]

/-- Let `S` be an `R`-algebra, `M` a submonoid of `R`, and `S' = M⁻¹S`.
If the image of some `x : S` falls in the adjoin of some finite `s ⊆ S'` over `R`,
then there exists some `m : M` such that `m • x` falls in the
adjoin of `IsLocalization.finsetIntegerMultiple _ s` over `R`.
-/
theorem IsLocalization.lift_mem_adjoin_finsetIntegerMultiple [Algebra R S] [Algebra R S']
    [IsScalarTower R S S'] [IsLocalization (M.map (algebraMap R S)) S'] (x : S) (s : Finset S')
    (hx : algebraMap S S' x ∈ Algebra.adjoin R (s : Set S')) :
    ∃ m : M, m • x ∈
      Algebra.adjoin R
        (IsLocalization.finsetIntegerMultiple (M.map (algebraMap R S)) s : Set S) := by
  obtain ⟨⟨_, a, ha, rfl⟩, e⟩ :=
    IsLocalization.exists_smul_mem_of_mem_adjoin (M.map (algebraMap R S)) x s (Algebra.adjoin R _)
      Algebra.subset_adjoin (by rintro _ ⟨a, _, rfl⟩; exact Subalgebra.algebraMap_mem _ a) hx
  refine ⟨⟨a, ha⟩, ?_⟩
  simpa only [Submonoid.smul_def, algebraMap_smul] using e

theorem finiteType_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.FiniteType := by
  rw [RingHom.ofLocalizationSpan_iff_finite]
  introv R hs H
  -- mirrors the proof of `finite_ofLocalizationSpan`
  letI := f.toAlgebra
  letI := fun r : s => (Localization.awayMap f r).toAlgebra
  have : ∀ r : s,
      IsLocalization ((Submonoid.powers (r : R)).map (algebraMap R S)) (Localization.Away (f r)) :=
    by intro r; rw [Submonoid.map_powers]; exact Localization.isLocalization
  haveI : ∀ r : s, IsScalarTower R (Localization.Away (r : R)) (Localization.Away (f r)) :=
    fun r => IsScalarTower.of_algebraMap_eq'
      (IsLocalization.map_comp (Submonoid.powers (r : R)).le_comap_map).symm
  constructor
  replace H := fun r => (H r).1
  choose s₁ s₂ using H
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (f x)) (s₁ x)
  use s.attach.biUnion sf
  convert (Algebra.adjoin_attach_biUnion (R := R) sf).trans _
  rw [eq_top_iff]
  rintro x -
  apply (⨆ x : s, Algebra.adjoin R (sf x : Set S)).toSubmodule.mem_of_span_eq_top_of_smul_pow_mem
    _ hs _ _
  intro r
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ :=
    multiple_mem_adjoin_of_mem_localization_adjoin (Submonoid.powers (r : R))
      (Localization.Away (r : R)) (s₁ r : Set (Localization.Away (f r)))
      (algebraMap S (Localization.Away (f r)) x) (by rw [s₂ r]; trivial)
  rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S, ← map_mul] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ :=
    IsLocalization.lift_mem_adjoin_finsetIntegerMultiple (Submonoid.powers (r : R)) _ (s₁ r) hn₁
  rw [Submonoid.smul_def, ← Algebra.smul_def, smul_smul, ← pow_add] at hn₂
  simp_rw [Submonoid.map_powers] at hn₂
  use n₂ + n₁
  exact le_iSup (fun x : s => Algebra.adjoin R (sf x : Set S)) r hn₂
