/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.RingHom.Finite

/-!

# The meta properties of finite-type ring homomorphisms.

## Main results

Let `R` be a commutative ring, `S` is an `R`-algebra, `M` be a submonoid of `R`.

* `finiteType_localizationPreserves` : If `S` is a finite type `R`-algebra, then `S' = M⁻¹S` is a
  finite type `R' = M⁻¹R`-algebra.
* `finiteType_ofLocalizationSpan` : `S` is a finite type `R`-algebra if there exists
  a set `{ r }` that spans `R` such that `Sᵣ` is a finite type `Rᵣ`-algebra.
*`RingHom.finiteType_isLocal`: `RingHom.FiniteType` is a local property.

-/


namespace RingHom

open scoped Pointwise TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (M : Submonoid R) (f : R →+* S)
variable (R' S' : Type u) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

theorem finiteType_stableUnderComposition : StableUnderComposition @FiniteType := by
  introv R hf hg
  exact hg.comp hf

/-- If `S` is a finite type `R`-algebra, then `S' = M⁻¹S` is a finite type `R' = M⁻¹R`-algebra. -/
theorem finiteType_localizationPreserves : RingHom.LocalizationPreserves @RingHom.FiniteType := by
  classical
  introv R hf
  -- mirrors the proof of `localization_map_finite`
  letI := f.toAlgebra
  letI := ((algebraMap S S').comp f).toAlgebra
  let f' : R' →+* S' := IsLocalization.map S' f (Submonoid.le_comap_map M)
  letI := f'.toAlgebra
  have algF'_eq : algebraMap R' S' = IsLocalization.map S' f (Submonoid.le_comap_map M) := rfl
  haveI : IsScalarTower R R' S' :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp M.le_comap_map).symm
  let fₐ : S →ₐ[R] S' := AlgHom.mk' (algebraMap S S') fun c x => RingHom.map_mul _ _ _
  obtain ⟨T, hT⟩ := hf
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
  rw [Algebra.smul_def, algF'_eq, IsLocalization.map_mk' M.le_comap_map, map_one]

theorem localization_away_map_finiteType (r : R) [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'] (hf : f.FiniteType) :
    (IsLocalization.Away.map R' S' f r).FiniteType :=
  finiteType_localizationPreserves.away _ r _ _ hf

variable {S'}

open scoped Classical in
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
  rw [Algebra.smul_def, ← map_mul] at hx''
  obtain ⟨a, ha₂⟩ := (IsLocalization.eq_iff_exists M S').mp hx''
  use a * y ^ n
  convert A.mul_mem hx' (hA₂ a.prop) using 1
  rw [Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow, mul_assoc, ← ha₂,
    mul_comm]

open scoped Classical in
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
  classical
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

theorem finiteType_holdsForLocalizationAway : HoldsForLocalizationAway @FiniteType := by
  introv R _
  suffices Algebra.FiniteType R S by
    rw [RingHom.FiniteType]
    convert this; ext
    rw [Algebra.smul_def]; rfl
  exact IsLocalization.finiteType_of_monoid_fg (Submonoid.powers r) S

theorem finiteType_ofLocalizationSpanTarget : OfLocalizationSpanTarget @FiniteType := by
  -- Setup algebra instances.
  rw [ofLocalizationSpanTarget_iff_finite]
  introv R hs H
  classical
  letI := f.toAlgebra
  replace H : ∀ r : s, Algebra.FiniteType R (Localization.Away (r : S)) := by
    intro r; simp_rw [RingHom.FiniteType] at H; convert H r; ext; simp_rw [Algebra.smul_def]; rfl
  replace H := fun r => (H r).1
  constructor
  -- Suppose `s : Finset S` spans `S`, and each `Sᵣ` is finitely generated as an `R`-algebra.
  -- Say `t r : Finset Sᵣ` generates `Sᵣ`. By assumption, we may find `lᵢ` such that
  -- `∑ lᵢ * sᵢ = 1`. I claim that all `s` and `l` and the numerators of `t` and generates `S`.
  choose t ht using H
  obtain ⟨l, hl⟩ :=
    (Finsupp.mem_span_iff_linearCombination S (s : Set S) 1).mp
      (show (1 : S) ∈ Ideal.span (s : Set S) by rw [hs]; trivial)
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (x : S)) (t x)
  use s.attach.biUnion sf ∪ s ∪ l.support.image l
  rw [eq_top_iff]
  -- We need to show that every `x` falls in the subalgebra generated by those elements.
  -- Since all `s` and `l` are in the subalgebra, it suffices to check that `sᵢ ^ nᵢ • x` falls in
  -- the algebra for each `sᵢ` and some `nᵢ`.
  rintro x -
  apply Subalgebra.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set S) l hl _ _ x _
  · intro x hx
    apply Algebra.subset_adjoin
    rw [Finset.coe_union, Finset.coe_union]
    exact Or.inl (Or.inr hx)
  · intro i
    by_cases h : l i = 0; · rw [h]; exact zero_mem _
    apply Algebra.subset_adjoin
    rw [Finset.coe_union, Finset.coe_image]
    exact Or.inr (Set.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr h))
  · intro r
    rw [Finset.coe_union, Finset.coe_union, Finset.coe_biUnion]
    -- Since all `sᵢ` and numerators of `t r` are in the algebra, it suffices to show that the
    -- image of `x` in `Sᵣ` falls in the `R`-adjoin of `t r`, which is of course true.
    -- Porting note: The following `obtain` fails because Lean wants to know right away what the
    -- placeholders are, so we need to provide a little more guidance
    -- obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := IsLocalization.exists_smul_mem_of_mem_adjoin
    --   (Submonoid.powers (r : S)) x (t r) (Algebra.adjoin R _) _ _ _
    rw [show ∀ A : Set S, (∃ n, (r : S) ^ n • x ∈ Algebra.adjoin R A) ↔
      (∃ m : (Submonoid.powers (r : S)), (m : S) • x ∈ Algebra.adjoin R A) by
      { exact fun _ => by simp [Submonoid.mem_powers_iff] }]
    refine IsLocalization.exists_smul_mem_of_mem_adjoin
      (Submonoid.powers (r : S)) x (t r) (Algebra.adjoin R _) ?_ ?_ ?_
    · intro x hx
      apply Algebra.subset_adjoin
      exact Or.inl (Or.inl ⟨_, ⟨r, rfl⟩, _, ⟨s.mem_attach r, rfl⟩, hx⟩)
    · rw [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff]
      apply Algebra.subset_adjoin
      exact Or.inl (Or.inr r.2)
    · rw [ht]; trivial

theorem finiteType_isLocal : PropertyIsLocal @FiniteType :=
  ⟨finiteType_localizationPreserves.away,
    finiteType_ofLocalizationSpanTarget,
    finiteType_ofLocalizationSpanTarget.ofLocalizationSpan
      (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finiteType_holdsForLocalizationAway).left,
    (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finiteType_holdsForLocalizationAway).right⟩

@[deprecated (since := "2025-03-01")]
alias finiteType_is_local := finiteType_isLocal

theorem finiteType_respectsIso : RingHom.RespectsIso @RingHom.FiniteType :=
  RingHom.finiteType_isLocal.respectsIso

theorem finiteType_isStableUnderBaseChange : IsStableUnderBaseChange @FiniteType := by
  apply IsStableUnderBaseChange.mk
  · exact finiteType_respectsIso
  · introv h
    replace h : Algebra.FiniteType R T := by
      rw [RingHom.FiniteType] at h; convert h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.FiniteType S (S ⊗[R] T) by
      rw [RingHom.FiniteType]; convert this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

end RingHom
