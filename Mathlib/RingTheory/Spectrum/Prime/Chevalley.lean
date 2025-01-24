/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Polynomial

/-!
# Chevalley's theorem

This file proves Chevalley's theorem, namely that if `f : R → S` is a finitely presented ring hom
between commutative rings, then the image of a constructible set in `Spec S` is a constructible set
in `Spec R`.
-/

open Polynomial PrimeSpectrum TensorProduct Topology

universe u v
variable {R M A} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]

private lemma Ideal.span_range_update_divByMonic' {ι : Type*} [DecidableEq ι]
    (v : ι → R[X]) (i j : ι) (hij : i ≠ j) (h : IsUnit (v i).leadingCoeff) :
    Ideal.span (Set.range (Function.update v j (v j %ₘ (C ((h.unit⁻¹ : Rˣ) : R) * v i)))) =
      Ideal.span (Set.range v) := by
  have H : (C (↑(h.unit⁻¹) : R) * v i).Monic := by simp [Monic, leadingCoeff_C_mul_of_isUnit]
  refine le_antisymm ?_ ?_ <;>
    simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe]
  · intro k
    by_cases hjk : j = k
    · subst hjk
      rw [Function.update_self, modByMonic_eq_sub_mul_div (v j) H]
      apply sub_mem (Ideal.subset_span ?_) (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ <| Ideal.subset_span ?_))
      · exact ⟨j, rfl⟩
      · exact ⟨i, rfl⟩
    exact Ideal.subset_span ⟨k, (Function.update_of_ne (.symm hjk) _ _).symm⟩
  · intro k
    by_cases hjk : j = k
    · subst hjk
      nth_rw 2 [← modByMonic_add_div (v j) H]
      apply add_mem (Ideal.subset_span ?_) (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ <| Ideal.subset_span ?_))
      · exact ⟨j, Function.update_self _ _ _⟩
      · exact ⟨i, Function.update_of_ne hij _ _⟩
    exact Ideal.subset_span ⟨k, Function.update_of_ne (.symm hjk) _ _⟩

private lemma foo_induction
    (P : ∀ (R : Type u) [CommRing R], Ideal R[X] → Prop)
    (hP₀ : ∀ (R) [CommRing R] (g : R[X]), g.Monic → P R (Ideal.span {g}))
    (hP₁ : ∀ (R) [CommRing R], P R ⊥)
    (hP : ∀ (R) [CommRing R] (c : R) (I : Ideal R[X]),
      P (Localization.Away c) (I.map (mapRingHom (algebraMap _ _))) →
      P (R ⧸ Ideal.span {c}) (I.map (mapRingHom (algebraMap _ _))) → P R I)
    {R} [CommRing R] (I : Ideal R[X]) (hI : I.FG) : P R I := by
  classical
  obtain ⟨n, e, rfl⟩ : ∃ (n : ℕ) (e : Fin (n + 1) → R[X]), I = Ideal.span (Set.range e) := by
    obtain ⟨s, rfl⟩ := hI
    exact ⟨s.card, Fin.cons 0 (Subtype.val ∘ s.equivFin.symm),
      by simp [← Set.union_singleton, Ideal.span_union, Set.singleton_zero]⟩
  clear hI
  set v : (Fin (n + 1) → WithBot ℕ) ×ₗ Prop := toLex
    (degree ∘ e, ¬ ∃ i, IsUnit (e i).leadingCoeff ∧ ∀ j, e j ≠ 0 →
      (e i).degree ≤ (e j).degree) with hv
  clear_value v
  induction' v using WellFoundedLT.induction with v H_IH generalizing R
  by_cases he0 : e = 0
  · simpa [he0, Set.range_zero, Set.singleton_zero] using hP₁ R
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (Ideal.span (Set.range e)) ⊥]; exact hP₁ R
  simp only [funext_iff, Pi.zero_apply, not_forall] at he0
  -- Case I : The `e i ≠ 0` with minimal degree has invertible leading coefficient
  by_cases H : ∃ i, IsUnit (e i).leadingCoeff ∧ ∀ j, e j ≠ 0 → (e i).degree ≤ (e j).degree
  · obtain ⟨i, hi, i_min⟩ := H
    have hi_monic : (C (↑(hi.unit⁻¹) : R) * e i).Monic := by
      simp [Monic, leadingCoeff_C_mul_of_isUnit]
    -- Case I.ii : `e j = 0` for all `j ≠ i`.
    by_cases H' : ∀ j ≠ i, e j = 0
    -- then `I = Ideal.span {e i}`
    · convert hP₀ R (C ((hi.unit⁻¹ : Rˣ) : R) * e i) hi_monic using 1
      refine le_antisymm ?_ ?_ <;>
        simp only [Ideal.span_le, Set.range_subset_iff, Set.singleton_subset_iff]
      · intro j
        by_cases hij : i = j
        · simp only [SetLike.mem_coe, Ideal.mem_span_singleton]
          use C (e i).leadingCoeff
          rw [mul_comm, ← mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, one_mul, hij]
        · rw [H' j (.symm hij)]
          exact Ideal.zero_mem _
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
    -- Case I.i : There is another `e j ≠ 0`
    · simp only [ne_eq, not_forall, Classical.not_imp] at H'
      obtain ⟨j, hj, hj'⟩ := H'
      replace i_min := i_min j hj'
      -- then we can replace `e j` with `e j %ₘ (C h.unit⁻¹ * e i) `
      -- with `h : IsUnit (e i).leadingCoeff`.
      rw [← Ideal.span_range_update_divByMonic' e i j (.symm hj) hi]
      refine H_IH _ ?_ _ rfl
      refine .left _ _ (lt_of_le_of_ne (b := (ofLex v).1) ?_ ?_)
      · intro k
        simp only [Function.comp_apply, Function.update_apply, hv, ne_eq, not_exists, not_and,
          not_forall, Classical.not_imp, not_le, ofLex_toLex]
        split_ifs with hjk
        · rw [hjk]
          refine (degree_modByMonic_le _ hi_monic).trans
            ((degree_C_mul_of_mul_ne_zero ?_).trans_le i_min)
          rw [IsUnit.val_inv_mul]
          exact one_ne_zero
        · exact le_rfl
      · simp only [hv, ne_eq, not_exists, not_and, not_forall, not_le, funext_iff,
          Function.comp_apply, exists_prop, ofLex_toLex]
        use j
        simp only [Function.update_self]
        refine ((degree_modByMonic_lt _ hi_monic).trans_le <|
          (degree_C_mul_of_mul_ne_zero ?_).trans_le i_min).ne
        rw [IsUnit.val_inv_mul]
        exact one_ne_zero
  -- Case II : The `e i ≠ 0` with minimal degree has non-invertible leading coefficient
  obtain ⟨i, hi, i_min⟩ : ∃ i, e i ≠ 0 ∧ ∀ j, e j ≠ 0 → (e i).degree ≤ (e j).degree := by
    have : ∃ n : ℕ, ∃ i, (e i).degree = n ∧ (e i) ≠ 0 := by
      obtain ⟨i, hi⟩ := he0; exact ⟨(e i).natDegree, i, degree_eq_natDegree hi, hi⟩
    let m := Nat.find this
    obtain ⟨i, hi, hi'⟩ : ∃ i, (e i).degree = m ∧ (e i) ≠ 0 := Nat.find_spec this
    refine ⟨i, hi', fun j hj ↦ ?_⟩
    refine hi.le.trans ?_
    rw [degree_eq_natDegree hj, Nat.cast_le]
    exact Nat.find_min' _ ⟨j, degree_eq_natDegree hj, hj⟩
  have : ¬ IsUnit (e i).leadingCoeff := fun HH ↦ H ⟨i, HH, i_min⟩
  -- We replace `R` by `R ⧸ Ideal.span {(e i).leadingCoeff}` where `(e i).degree` is lowered
  -- and `Localization.Away (e i).leadingCoeff` where `(e i).leadingCoeff` becomes invertible.
  apply hP _ (e i).leadingCoeff
  · rw [Ideal.map_span, ← Set.range_comp]
    refine H_IH _ ?_ _ rfl
    rw [hv, Prod.Lex.lt_iff']
    constructor
    · intro j; simpa using degree_map_le
    simp only [coe_mapRingHom, Function.comp_apply, ne_eq, hv, ofLex_toLex,
      not_exists, not_and, not_forall, Classical.not_imp, not_le, H, not_false_eq_true]
    intro h_eq
    rw [lt_iff_le_not_le]
    simp only [exists_prop, le_Prop_eq, implies_true, true_implies, not_forall, Classical.not_imp,
      not_exists, not_and, not_lt, true_and]
    refine ⟨i, ?_, ?_⟩
    · replace h_eq := congr_fun h_eq i
      simp only [Function.comp_apply] at h_eq
      have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (e i).leadingCoeff)
        (e i).leadingCoeff
      convert this
      nth_rw 2 [← coeff_natDegree]
      rw [natDegree_eq_of_degree_eq h_eq, coeff_map, coeff_natDegree]
    · intro j hj
      refine le_trans ?_ ((i_min j (fun e ↦ hj (by simp [e]))).trans_eq (congr_fun h_eq j).symm)
      simpa using degree_map_le
  · rw [Ideal.map_span, ← Set.range_comp]
    refine H_IH _ ?_ _ rfl
    rw [hv]
    refine .left _ _ (lt_of_le_of_ne ?_ ?_)
    · intro j; simpa using degree_map_le
    simp only [coe_mapRingHom, Function.comp_apply, ne_eq, hv, ofLex_toLex,
      not_exists, not_and, not_forall, Classical.not_imp, not_le, H, not_false_eq_true]
    intro h_eq
    replace h_eq := congr_fun h_eq i
    simp only [Ideal.Quotient.algebraMap_eq, Function.comp_apply, degree_map_eq_iff,
      Ideal.Quotient.mk_singleton_self, ne_eq, not_true_eq_false, false_or] at h_eq
    exact hi h_eq

private lemma comap_C_eq_comap_quotient_union_comap_localization (s : Set (PrimeSpectrum R[X]))
    (c : R) :
    comap C '' s =
      comap (Ideal.Quotient.mk (.span {c})) '' (comap C ''
        (comap (mapRingHom (Ideal.Quotient.mk _)) ⁻¹' s)) ∪
      comap (algebraMap R (Localization.Away c)) '' (comap C ''
        (comap (mapRingHom (algebraMap R (Localization.Away c))) ⁻¹' s)) := by
  simp_rw [← Set.image_comp, ← ContinuousMap.coe_comp, ← comap_comp, ← mapRingHom_comp_C,
    comap_comp, ContinuousMap.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range,
    ← Set.image_union, ← Set.inter_union_distrib_left]
  letI := (mapRingHom (algebraMap R (Localization.Away c))).toAlgebra
  suffices Set.range (comap (mapRingHom (Ideal.Quotient.mk (.span {c})))) =
      (Set.range (comap (algebraMap R[X] (Localization.Away c)[X])))ᶜ by
    rw [this, RingHom.algebraMap_toAlgebra, Set.compl_union_self, Set.inter_univ]
  have := Polynomial.isLocalization (.powers c) (Localization.Away c)
  rw [Submonoid.map_powers] at this
  have surj : Function.Surjective (mapRingHom (Ideal.Quotient.mk (.span {c}))) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  rw [range_comap_of_surjective _ _ surj, localization_away_comap_range _ (C c)]
  simp [Polynomial.ker_mapRingHom, Ideal.map_span]

private lemma isConstructible_comap_C_zeroLocus_sdiff_zeroLocus {R} [CommRing R]
    (I : Ideal R[X]) (hI : I.FG) (f : R[X]) :
    IsConstructible (comap C '' (zeroLocus I \ zeroLocus {f})) := by
  revert f
  apply foo_induction (hI := hI)
  · intros R _ g hg f
    simp only [zeroLocus_span]
    exact ((isRetrocompact_iff (isOpen_image_comap_of_monic f g hg)).mpr
      (isCompact_image_comap_of_monic f g hg)).isConstructible (isOpen_image_comap_of_monic f g hg)
  · intro R _ f
    simp only [Submodule.bot_coe, zeroLocus_singleton_zero, ← Set.compl_eq_univ_diff,
      ← basicOpen_eq_zeroLocus_compl]
    exact ((isRetrocompact_iff (isOpenMap_comap_C _ (basicOpen f).2)).mpr
      ((isCompact_basicOpen f).image (comap C).2)).isConstructible
      (isOpenMap_comap_C _ (basicOpen f).2)
  · intro R _ c I H₁ H₂ f
    replace H₁ := (H₁ (mapRingHom (algebraMap _ _) f)).image_of_isOpenEmbedding
      (localization_away_isOpenEmbedding (Localization.Away c) c)
      (by rw [localization_away_comap_range _ c]
          exact (isRetrocompact_iff (basicOpen c).2).mpr (isCompact_basicOpen c))
    replace H₂ := (H₂ (mapRingHom (Ideal.Quotient.mk _) f)).image_of_isClosedEmbedding
      (isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective)
      (by rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
          simp only [Ideal.mk_ker, zeroLocus_span, ← basicOpen_eq_zeroLocus_compl]
          exact (isRetrocompact_iff (basicOpen c).2).mpr (isCompact_basicOpen c))
    rw [comap_C_eq_comap_quotient_union_comap_localization _ c]
    simp_rw [Set.preimage_diff, preimage_comap_zeroLocus, Set.image_singleton]
    convert H₂.union H₁ using 5 <;>
      simp only [Ideal.map, zeroLocus_span, coe_mapRingHom, Ideal.Quotient.algebraMap_eq]

/-- The special case of **Chevalley's theorem** applied to `Polynomial.C : R → R[X]`. -/
private theorem isConstructible_image_comap_C {R} [CommRing R] (s : Set (PrimeSpectrum R[X]))
    (hs : IsConstructible s) :
    IsConstructible (comap C '' s) := by
  induction s, hs using IsConstructible.induction_of_isTopologicalBasis (ι := R[X]) _
    isTopologicalBasis_basic_opens with
  | isCompact_basis i => exact isCompact_basicOpen _
  | union s hs t ht hs' ht' =>
    rw [Set.image_union]
    exact hs'.union ht'
  | sdiff i s hs =>
    simp only [basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂,
      compl_sdiff_compl, ← zeroLocus_iUnion₂, Set.biUnion_of_singleton]
    rw [← zeroLocus_span]
    apply isConstructible_comap_C_zeroLocus_sdiff_zeroLocus
    exact ⟨hs.toFinset, by simp⟩

/-- **Chevalley's theorem**.

If `f : R → S` is a finitely presented ring hom between commutative rings, then the image of a
constructible set in `Spec S` is a constructible set in `Spec R`. -/
@[stacks 00FE]
theorem isConstructible_image_comap {R S} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.FinitePresentation) (s : Set (PrimeSpectrum S)) (hs : IsConstructible s) :
    IsConstructible (comap f '' s) := by
  apply hf.polynomial_induction
    (P := fun _ _ _ _ f ↦ ∀ s, IsConstructible s → IsConstructible (comap f '' s))
    (Q := fun _ _ _ _ f ↦ ∀ s, IsConstructible s → IsConstructible (comap f '' s))
  · exact fun _ ↦ isConstructible_image_comap_C
  · intro R _ S _ f hf hf' s hs
    refine hs.image_of_isClosedEmbedding (isClosedEmbedding_comap_of_surjective _ _ hf) ?_
    rw [range_comap_of_surjective _ _ hf, isRetrocompact_iff (isClosed_zeroLocus _).isOpen_compl]
    obtain ⟨t, ht⟩ := hf'
    rw [← ht, ← t.toSet.iUnion_of_singleton_coe, zeroLocus_span, zeroLocus_iUnion, Set.compl_iInter]
    apply isCompact_iUnion
    exact fun _ ↦ by simpa using isCompact_basicOpen _
  · intro R _ S _ T _ f g hf hg s hs
    simp only [comap_comp, ContinuousMap.coe_comp, Set.image_comp]
    exact hf _ (hg _ hs)
  · exact hs
