/-
Copyright (c) 2026 Jay Scambler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jay Scambler
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lebesgue measure of a triangle in `ℝ²`

The 2-dimensional Lebesgue measure of the convex hull of three points
`a b c : Fin 2 → ℝ` equals one half the absolute determinant of the
edge matrix `![b - a; c - a]`.

## Main results

* `volume_convexHull_triple_fin_two`: ENNReal form, primary statement,
  using the matrix determinant.
* `volume_convexHull_triple_fin_two_toReal`: `.toReal` corollary.
* `volume_convexHull_triple_fin_two_polynomial`: explicit polynomial
  form (corollary, useful for symbolic computation).

The helpers are kept `private` and live in this file; only the named
results above are exported.
-/

open MeasureTheory Set Matrix Module Function ENNReal

namespace MeasureTheory

/-- Standard 2-simplex defined as a half-plane intersection.
Equivalent to the projection of `stdSimplex ℝ (Fin 3)` to its first
two coordinates. -/
private def stdTri : Set (Fin 2 → ℝ) :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

/-- Standard 2-simplex defined as a half-plane intersection. -/
private lemma stdTri_convex : Convex ℝ stdTri := by
  have h0 : IsLinearMap ℝ (fun x : Fin 2 → ℝ => x 0) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have h1 : IsLinearMap ℝ (fun x : Fin 2 → ℝ => x 1) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hsum : IsLinearMap ℝ (fun x : Fin 2 → ℝ => x 0 + x 1) := by
    refine ⟨fun a b => ?_, fun c a => ?_⟩
    · change (a 0 + b 0) + (a 1 + b 1) = (a 0 + a 1) + (b 0 + b 1)
      ring
    · change c • a 0 + c • a 1 = c • (a 0 + a 1)
      rw [smul_add]
  have hC1 : Convex ℝ {x : Fin 2 → ℝ | 0 ≤ x 0} := convex_halfSpace_ge h0 0
  have hC2 : Convex ℝ {x : Fin 2 → ℝ | 0 ≤ x 1} := convex_halfSpace_ge h1 0
  have hC3 : Convex ℝ {x : Fin 2 → ℝ | x 0 + x 1 ≤ 1} := convex_halfSpace_le hsum 1
  have heq : stdTri =
      ({x : Fin 2 → ℝ | 0 ≤ x 0} ∩ {x : Fin 2 → ℝ | 0 ≤ x 1}) ∩
        {x : Fin 2 → ℝ | x 0 + x 1 ≤ 1} := by
    ext x
    constructor
    · rintro ⟨ha, hb, hc⟩; exact ⟨⟨ha, hb⟩, hc⟩
    · rintro ⟨⟨ha, hb⟩, hc⟩; exact ⟨ha, hb, hc⟩
  rw [heq]
  exact (hC1.inter hC2).inter hC3

private lemma zero_mem_stdTri : (0 : Fin 2 → ℝ) ∈ stdTri := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

private lemma e0_mem_stdTri : (![1, 0] : Fin 2 → ℝ) ∈ stdTri := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma e1_mem_stdTri : (![0, 1] : Fin 2 → ℝ) ∈ stdTri := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma convexHull_subset_stdTri :
    convexHull ℝ ({0, ![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) ⊆ stdTri := by
  apply convexHull_min _ stdTri_convex
  intro x hx
  rcases hx with hx | hx
  · rw [hx]; exact zero_mem_stdTri
  rcases hx with hx | hx
  · rw [hx]; exact e0_mem_stdTri
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact e1_mem_stdTri

private lemma stdTri_subset_convexHull :
    stdTri ⊆ convexHull ℝ ({0, ![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) := by
  intro x hx
  obtain ⟨hx0, hx1, hxsum⟩ := hx
  have ha : (0 : ℝ) ≤ 1 - x 0 - x 1 := by linarith
  have h0 : (0 : Fin 2 → ℝ) ∈ convexHull ℝ ({0, ![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have h1 : (![1, 0] : Fin 2 → ℝ) ∈ convexHull ℝ ({0, ![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have h2 : (![0, 1] : Fin 2 → ℝ) ∈ convexHull ℝ ({0, ![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have hconv : Convex ℝ (convexHull ℝ ({0, ![1, 0], ![0, 1]} : Set (Fin 2 → ℝ))) :=
    convex_convexHull ℝ _
  have hxeq : (1 - x 0 - x 1) • (0 : Fin 2 → ℝ)
            + x 0 • (![1, 0] : Fin 2 → ℝ)
            + x 1 • (![0, 1] : Fin 2 → ℝ) = x := by
    funext j
    fin_cases j
    · change (1 - x 0 - x 1) * 0 + x 0 * 1 + x 1 * 0 = x 0
      ring
    · change (1 - x 0 - x 1) * 0 + x 0 * 0 + x 1 * 1 = x 1
      ring
  rw [← hxeq]
  have hsum_eq :
      (1 - x 0 - x 1) • (0 : Fin 2 → ℝ)
      + x 0 • (![1, 0] : Fin 2 → ℝ)
      + x 1 • (![0, 1] : Fin 2 → ℝ)
    = ∑ i : Fin 3,
        (![1 - x 0 - x 1, x 0, x 1] : Fin 3 → ℝ) i •
        (![(0 : Fin 2 → ℝ), ![1, 0], ![0, 1]] : Fin 3 → (Fin 2 → ℝ)) i := by
    rw [Fin.sum_univ_three]
    rfl
  rw [hsum_eq]
  refine hconv.sum_mem ?_ ?_ ?_
  · intro i _
    fin_cases i
    · change (0 : ℝ) ≤ 1 - x 0 - x 1; exact ha
    · change (0 : ℝ) ≤ x 0; exact hx0
    · change (0 : ℝ) ≤ x 1; exact hx1
  · rw [Fin.sum_univ_three]
    change (1 - x 0 - x 1) + x 0 + x 1 = 1
    ring
  · intro i _
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

private lemma stdTri_eq_convexHull :
    stdTri = convexHull ℝ ({0, ![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) :=
  Set.Subset.antisymm stdTri_subset_convexHull convexHull_subset_stdTri

private lemma convexHull_zero_eq_image_stdTri (u v : Fin 2 → ℝ) :
    convexHull ℝ ({0, u, v} : Set (Fin 2 → ℝ))
    = (fun st : Fin 2 → ℝ ↦ st 0 • u + st 1 • v) '' stdTri := by
  have hlin : IsLinearMap ℝ (fun st : Fin 2 → ℝ ↦ st 0 • u + st 1 • v) := by
    refine ⟨fun a b => ?_, fun c a => ?_⟩
    · change (a + b) 0 • u + (a + b) 1 • v = a 0 • u + a 1 • v + (b 0 • u + b 1 • v)
      simp only [Pi.add_apply, add_smul]; abel
    · change (c • a) 0 • u + (c • a) 1 • v = c • (a 0 • u + a 1 • v)
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [smul_add, SemigroupAction.mul_smul, SemigroupAction.mul_smul]
  rw [stdTri_eq_convexHull, hlin.image_convexHull]
  congr 1
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  have e0 : (0 : Fin 2 → ℝ) 0 • u + (0 : Fin 2 → ℝ) 1 • v = 0 := by simp
  have e1 : (![1, 0] : Fin 2 → ℝ) 0 • u + (![1, 0] : Fin 2 → ℝ) 1 • v = u := by
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have e2 : (![0, 1] : Fin 2 → ℝ) 0 • u + (![0, 1] : Fin 2 → ℝ) 1 • v = v := by
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [e0, e1, e2]

/-- The standard 2-simplex has Lebesgue measure 1/2. -/
private lemma volume_stdTri : volume stdTri = ENNReal.ofReal (1/2) := by
  have hT_meas : MeasurableSet ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}) := by
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_le measurable_const measurable_fst
    · exact measurableSet_le measurable_const measurable_snd
    · exact measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  have h_pre : stdTri = (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) ⁻¹'
                {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} := by
    ext x; rfl
  rw [h_pre,
      (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).measure_preimage
        hT_meas.nullMeasurableSet]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      Measure.prod_apply hT_meas]
  have h_section : ∀ x : ℝ,
      volume (Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}) =
        (Set.Icc (0:ℝ) 1).indicator (fun a => ENNReal.ofReal (1 - a)) x := by
    intro x
    by_cases h0 : 0 ≤ x
    · by_cases h1 : x ≤ 1
      · have hpre_eq :
            Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} =
              Set.Icc (0:ℝ) (1 - x) := by
          ext y
          constructor
          · intro h; exact ⟨h.2.1, by linarith [h.2.2]⟩
          · intro h; exact ⟨h0, h.1, by linarith [h.2]⟩
        rw [hpre_eq, Real.volume_Icc,
            Set.indicator_of_mem (show x ∈ Icc (0:ℝ) 1 from ⟨h0, h1⟩)]
        congr 1
        ring
      · push Not at h1
        have hxmem : x ∉ Icc (0:ℝ) 1 := fun h => (not_le.mpr h1) h.2
        have hpre_eq :
            Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} =
              (∅ : Set ℝ) := by
          ext y
          constructor
          · intro h; exfalso; linarith [h.2.1, h.2.2]
          · intro h; exact h.elim
        rw [hpre_eq, measure_empty, Set.indicator_of_notMem hxmem]
    · push Not at h0
      have hxmem : x ∉ Icc (0:ℝ) 1 := fun h => (not_le.mpr h0) h.1
      have hpre_eq :
          Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} =
            (∅ : Set ℝ) := by
        ext y
        constructor
        · intro h; exfalso; linarith [h.1]
        · intro h; exact h.elim
      rw [hpre_eq, measure_empty, Set.indicator_of_notMem hxmem]
  simp_rw [h_section]
  rw [lintegral_indicator measurableSet_Icc]
  have h_integrable : IntegrableOn (fun x => (1:ℝ) - x) (Icc (0:ℝ) 1) volume := by
    have h_cont : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
    exact h_cont.continuousOn.integrableOn_Icc
  have h_integrand_nn : 0 ≤ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun x => 1 - x := by
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards with x hx
    change 0 ≤ 1 - x
    linarith [hx.2]
  rw [← ofReal_integral_eq_lintegral_ofReal h_integrable h_integrand_nn]
  congr 1
  rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id,
      integral_one, integral_id]
  norm_num

private lemma det_combo_2 (u v : Fin 2 → ℝ) :
    LinearMap.det
      ((LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).smulRight u
      + (LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).smulRight v)
    = u 0 * v 1 - u 1 * v 0 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 2))]
  have hM : LinearMap.toMatrix (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 2))
              ((LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).smulRight u
              + (LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).smulRight v)
            = !![u 0, v 0; u 1, v 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  rw [hM, Matrix.det_fin_two]
  simp
  ring

private lemma volume_translate (a : Fin 2 → ℝ) (s : Set (Fin 2 → ℝ)) :
    volume ((fun x => a + x) '' s) = volume s := by
  have heq : (fun x : Fin 2 → ℝ => a + x) '' s = (fun x => -a + x) ⁻¹' s := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨-a + y, hy, by abel⟩
  rw [heq]
  exact measure_preimage_add volume (-a) s

private lemma convexHull_translate (a b c : Fin 2 → ℝ) :
    convexHull ℝ ({a, b, c} : Set (Fin 2 → ℝ))
    = (fun x => a + x) '' convexHull ℝ ({0, b - a, c - a} : Set (Fin 2 → ℝ)) := by
  have hset : ({a, b, c} : Set (Fin 2 → ℝ))
      = (fun x => a + x) '' ({0, b - a, c - a} : Set (Fin 2 → ℝ)) := by
    ext x
    simp only [mem_image, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (hx | hx | hx)
      · exact ⟨0, Or.inl rfl, by simp [hx]⟩
      · exact ⟨b - a, Or.inr (Or.inl rfl), by rw [hx]; abel⟩
      · exact ⟨c - a, Or.inr (Or.inr rfl), by rw [hx]; abel⟩
    · rintro ⟨y, hy, rfl⟩
      rcases hy with hy | hy | hy
      · left; rw [hy]; simp
      · right; left; rw [hy]; abel
      · right; right; rw [hy]; abel
  rw [hset]
  let f : (Fin 2 → ℝ) →ᵃ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun x => a + x
      linear := LinearMap.id
      map_vadd' := fun p v => by
        change a + (v + p) = v + (a + p)
        abel }
  exact (AffineMap.image_convexHull f _).symm

/-- **Lebesgue measure of a triangle in `Fin 2 → ℝ`** equals one half
the absolute value of the determinant of the edge matrix.

ENNReal form (primary statement, matches mathlib conventions). -/
theorem volume_convexHull_triple_fin_two (a b c : Fin 2 → ℝ) :
    volume (convexHull ℝ ({a, b, c} : Set (Fin 2 → ℝ)))
    = ENNReal.ofReal
        ((1/2) * |Matrix.det !![b 0 - a 0, c 0 - a 0; b 1 - a 1, c 1 - a 1]|) := by
  rw [convexHull_translate, volume_translate, convexHull_zero_eq_image_stdTri]
  have key :
      (fun st : Fin 2 → ℝ => st 0 • (b - a) + st 1 • (c - a)) '' stdTri
      = ((LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).smulRight (b - a)
          + (LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).smulRight (c - a)) '' stdTri := rfl
  rw [key, MeasureTheory.Measure.addHaar_image_linearMap volume,
      det_combo_2, volume_stdTri]
  rw [show (b - a) 0 = b 0 - a 0 from rfl, show (b - a) 1 = b 1 - a 1 from rfl,
      show (c - a) 0 = c 0 - a 0 from rfl, show (c - a) 1 = c 1 - a 1 from rfl]
  rw [show |Matrix.det !![b 0 - a 0, c 0 - a 0; b 1 - a 1, c 1 - a 1]|
        = |(b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)| by
        rw [Matrix.det_fin_two_of]; congr 1; ring]
  rw [mul_comm (ENNReal.ofReal _) (ENNReal.ofReal (1/2)),
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]

/-- `.toReal` corollary of `volume_convexHull_triple_fin_two`. -/
theorem volume_convexHull_triple_fin_two_toReal (a b c : Fin 2 → ℝ) :
    (volume (convexHull ℝ ({a, b, c} : Set (Fin 2 → ℝ)))).toReal
    = (1/2) * |Matrix.det !![b 0 - a 0, c 0 - a 0; b 1 - a 1, c 1 - a 1]| := by
  rw [volume_convexHull_triple_fin_two]
  exact ENNReal.toReal_ofReal (by positivity)

/-- Polynomial form of the triangle-volume theorem, useful for symbolic
computation. Corollary of `volume_convexHull_triple_fin_two_toReal`
after `Matrix.det_fin_two_of`. -/
theorem volume_convexHull_triple_fin_two_polynomial (a b c : Fin 2 → ℝ) :
    (volume (convexHull ℝ ({a, b, c} : Set (Fin 2 → ℝ)))).toReal
    = (1/2) * |(b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)| := by
  rw [volume_convexHull_triple_fin_two_toReal, Matrix.det_fin_two_of]
  congr 1; congr 1; ring

end MeasureTheory
