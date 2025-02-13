/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Artinian rings over jacobson rings

## Main results
- `Module.finite_iff_isArtinianRing`: If `A` is a finite type algebra over an artinian ring `R`,
then `A` is finite over `R` if and only if `A` is an artinian ring.

-/

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

lemma Module.finite_of_finite_mul_of_field [IsJacobsonRing R]
    (I J : Ideal A) [I.IsMaximal]
    [IsArtinian A J] [Module.Finite R (I * J)] : Module.Finite R J := by
  let IJ := Submodule.comap J.subtype (I * J)
  have : Module.IsTorsionBySet A (J ⧸ IJ) I := by
    rintro x ⟨y, hy : y ∈ I⟩
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [← map_smul]
    simpa [Submodule.Quotient.mk_eq_zero] using Ideal.mul_mem_mul hy hx
  letI : Module (A ⧸ I) (J ⧸ IJ) := this.module
  letI := Ideal.Quotient.field I
  haveI : Module.Finite R (A ⧸ I) := finite_of_finite_type_of_isJacobsonRing R (A ⧸ I)
  have : Module.Finite R (J ⧸ IJ) :=
    have := ((IsArtinianRing.tfae (A ⧸ I) (J ⧸ IJ)).out 2 0 rfl rfl).mp
      (isArtinian_of_tower A inferInstance)
    .trans (A ⧸ I) _
  have : Module.Finite R J := by
    constructor
    apply Submodule.fg_of_fg_map_of_fg_inf_ker (IJ.mkQ.restrictScalars R)
    · rwa [Submodule.map_top, LinearMap.range_eq_top.mpr, ← Module.finite_def]
      exact IJ.mkQ_surjective
    · simp only [LinearMap.ker_restrictScalars, Submodule.ker_mkQ, le_top, inf_of_le_right]
      apply Submodule.fg_of_fg_map_injective (J.subtype.restrictScalars R) Subtype.val_injective
      rw [← Submodule.restrictScalars_map, Submodule.map_comap_eq_of_le, ← Submodule.fg_top]
      · exact Module.Finite.fg_top (M := I * J)
      · rw [Submodule.range_subtype]; exact Ideal.mul_le_left
  exact this

/-- If `A` is a finite type algebra over `R`, then `A` is an artinian ring and `R` is jacobson
implies `A` is finite over `R`. -/
lemma Module.finite_of_isArtinianRing [IsJacobsonRing R] [IsArtinianRing A] :
    Module.Finite R A := by
  by_contra H
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  cases nonempty_fintype (MaximalSpectrum A)
  let s : Multiset (MaximalSpectrum A) := k • Finset.univ.1
  suffices ¬ Module.Finite R ((s.map (MaximalSpectrum.asIdeal)).prod) by
    have hs : (s.map (MaximalSpectrum.asIdeal)).prod = ⊥ := by
      rw [← le_bot_iff, ← Ideal.zero_eq_bot, ← hk]
      simp only [Multiset.map_nsmul, Multiset.prod_nsmul, Finset.prod_map_val, s]
      refine pow_le_pow_left' (Ideal.prod_le_inf.trans ?_) k
      simp only [bot_le, true_and, le_sInf_iff, Set.mem_setOf_eq, Ideal.jacobson]
      intro b hb
      refine Finset.inf_le (β := MaximalSpectrum A) (b := ⟨b, hb⟩) (Finset.mem_univ _)
    exact this (hs ▸ inferInstance)
  induction s using Multiset.induction with
  | empty =>
    contrapose! H
    simp only [Multiset.map_zero, Multiset.prod_zero] at H
    rw [Ideal.one_eq_top] at H
    exact .of_surjective (Submodule.topEquiv (R := R)).toLinearMap Submodule.topEquiv.surjective
  | cons a s IH =>
    contrapose! IH
    rw [Multiset.map_cons, Multiset.prod_cons] at IH
    exact Module.finite_of_finite_mul_of_field a.asIdeal _

/-- If `A` is a finite type algebra over an artinian ring `R`,
then `A` is finite over `R` if and only if `A` is an artinian ring. -/
lemma Module.finite_iff_isArtinianRing [IsArtinianRing R] :
    Module.Finite R A ↔ IsArtinianRing A := by
  have := (IsArtinianRing.tfae R A).out 0 2
  exact ⟨isArtinian_of_tower _ ∘ this.mp, fun _ ↦ finite_of_isArtinianRing⟩

/-- If `A` is a finite type algebra over an artinian ring `R`,
then `A` is finite over `R` if and only if `dim A = 0`. -/
lemma Module.finite_iff_krullDimLE_zero [IsArtinianRing R] :
    Module.Finite R A ↔ Ring.KrullDimLE 0 A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  rw [finite_iff_isArtinianRing, isArtinianRing_iff_isNoetherianRing_krullDimLE_zero,
    and_iff_right this]
