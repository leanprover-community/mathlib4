/-
Copyright (c) 2023 Yaël Dilies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dilies
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# L2 inner product of finite sequences

This file defines the weighted L2 inner product of functions `f g : ι → R` where `ι` is a fintype as
`∑ i, conj (f i) * g i`. This convention (conjugation on the left) matches the inner product coming
from `RCLike.innerProductSpace`.

## TODO

* Build a non-instance `InnerProductSpace` from `wInner`.
* `cWeight` is a poor name. Can we find better? It doesn't hugely matter for typing, since it's
  hidden behind the `⟪f, g⟫ₙ_[𝕝] `notation, but it does show up in lemma names
  `⟪f, g⟫_[𝕝, cWeight]` is called `wInner_cWeight`. Maybe we should introduce some naming
  convention, similarly to `MeasureTheory.average`?
-/

open Finset Function Real
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

variable {ι κ 𝕜 : Type*} {E : ι → Type*} [Fintype ι]

namespace RCLike
variable [RCLike 𝕜]

section Pi
variable [∀ i, SeminormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)] {w : ι → ℝ}

/-- Weighted inner product giving rise to the L2 norm, denoted as `⟪g, f⟫_[𝕜, w]`. -/
def wInner (w : ι → ℝ) (f g : ∀ i, E i) : 𝕜 := ∑ i, w i • ⟪f i, g i⟫_𝕜

/-- The weight function making `wInner` into the compact inner product. -/
noncomputable abbrev cWeight : ι → ℝ := Function.const _ (Fintype.card ι)⁻¹

@[inherit_doc] notation "⟪" f ", " g "⟫_[" 𝕝 ", " w "]" => wInner (𝕜 := 𝕝) w f g

/-- Discrete inner product giving rise to the discrete L2 norm. -/
notation "⟪" f ", " g "⟫_[" 𝕝 "]" => ⟪f, g⟫_[𝕝, 1]

/-- Compact inner product giving rise to the compact L2 norm. -/
notation "⟪" f ", " g "⟫ₙ_[" 𝕝 "]" => ⟪f, g⟫_[𝕝, cWeight]

lemma wInner_cWeight_eq_smul_wInner_one (f g : ∀ i, E i) :
    ⟪f, g⟫ₙ_[𝕜] = (Fintype.card ι : ℚ≥0)⁻¹ • ⟪f, g⟫_[𝕜] := by
  simp [wInner, smul_sum, ← NNRat.cast_smul_eq_nnqsmul ℝ]

@[simp] lemma conj_wInner_symm (w : ι → ℝ) (f g : ∀ i, E i) :
    conj ⟪f, g⟫_[𝕜, w] = ⟪g, f⟫_[𝕜, w] := by
  simp [wInner, map_sum, inner_conj_symm, rclike_simps]

@[simp] lemma wInner_zero_left (w : ι → ℝ) (g : ∀ i, E i) : ⟪0, g⟫_[𝕜, w] = 0 := by simp [wInner]
@[simp] lemma wInner_zero_right (w : ι → ℝ) (f : ∀ i, E i) : ⟪f, 0⟫_[𝕜, w] = 0 := by simp [wInner]

lemma wInner_add_left (w : ι → ℝ) (f₁ f₂ g : ∀ i, E i) :
    ⟪f₁ + f₂, g⟫_[𝕜, w] = ⟪f₁, g⟫_[𝕜, w] + ⟪f₂, g⟫_[𝕜, w] := by
  simp [wInner, inner_add_left, smul_add, sum_add_distrib]

lemma wInner_add_right (w : ι → ℝ) (f g₁ g₂ : ∀ i, E i) :
    ⟪f, g₁ + g₂⟫_[𝕜, w] = ⟪f, g₁⟫_[𝕜, w] + ⟪f, g₂⟫_[𝕜, w] := by
  simp [wInner, inner_add_right, smul_add, sum_add_distrib]

@[simp] lemma wInner_neg_left (w : ι → ℝ) (f g : ∀ i, E i) : ⟪-f, g⟫_[𝕜, w] = -⟪f, g⟫_[𝕜, w] := by
  simp [wInner]

@[simp] lemma wInner_neg_right (w : ι → ℝ) (f g : ∀ i, E i) : ⟪f, -g⟫_[𝕜, w] = -⟪f, g⟫_[𝕜, w] := by
  simp [wInner]

lemma wInner_sub_left (w : ι → ℝ) (f₁ f₂ g : ∀ i, E i) :
    ⟪f₁ - f₂, g⟫_[𝕜, w] = ⟪f₁, g⟫_[𝕜, w] - ⟪f₂, g⟫_[𝕜, w] := by
  simp_rw [sub_eq_add_neg, wInner_add_left, wInner_neg_left]

lemma wInner_sub_right (w : ι → ℝ) (f g₁ g₂ : ∀ i, E i) :
    ⟪f, g₁ - g₂⟫_[𝕜, w] = ⟪f, g₁⟫_[𝕜, w] - ⟪f, g₂⟫_[𝕜, w] := by
  simp_rw [sub_eq_add_neg, wInner_add_right, wInner_neg_right]

@[simp] lemma wInner_of_isEmpty [IsEmpty ι] (w : ι → ℝ) (f g : ∀ i, E i) : ⟪f, g⟫_[𝕜, w] = 0 := by
  simp [Subsingleton.elim f 0]

lemma wInner_smul_left {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜]
    [SMulCommClass ℝ 𝕝 𝕜] [∀ i, Module 𝕝 (E i)] [∀ i, IsScalarTower 𝕝 𝕜 (E i)] (c : 𝕝)
    (w : ι → ℝ) (f g : ∀ i, E i) : ⟪c • f, g⟫_[𝕜, w] = star c • ⟪f, g⟫_[𝕜, w] := by
  simp_rw [wInner, Pi.smul_apply, inner_smul_left_eq_star_smul, starRingEnd_apply, smul_sum,
    smul_comm (w _)]

lemma wInner_smul_right {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜]
    [SMulCommClass ℝ 𝕝 𝕜] [∀ i, Module 𝕝 (E i)] [∀ i, IsScalarTower 𝕝 𝕜 (E i)] (c : 𝕝)
    (w : ι → ℝ) (f g : ∀ i, E i) : ⟪f, c • g⟫_[𝕜, w] = c • ⟪f, g⟫_[𝕜, w] := by
  simp_rw [wInner, Pi.smul_apply, inner_smul_right_eq_smul, smul_sum, smul_comm]

lemma mul_wInner_left (c : 𝕜) (w : ι → ℝ) (f g : ∀ i, E i) :
    c * ⟪f, g⟫_[𝕜, w] = ⟪star c • f, g⟫_[𝕜, w] := by rw [wInner_smul_left, star_star, smul_eq_mul]

lemma wInner_one_eq_sum (f g : ∀ i, E i) : ⟪f, g⟫_[𝕜] = ∑ i, ⟪f i, g i⟫_𝕜 := by simp [wInner]
lemma wInner_cWeight_eq_expect (f g : ∀ i, E i) : ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, ⟪f i, g i⟫_𝕜 := by
  simp [wInner, expect, smul_sum, ← NNRat.cast_smul_eq_nnqsmul ℝ]

end Pi

section Function
variable {w : ι → ℝ} {f g : ι → 𝕜}

lemma wInner_const_left (a : 𝕜) (f : ι → 𝕜) :
    ⟪const _ a, f⟫_[𝕜, w] = (∑ i, w i • f i) * conj a := by simp [wInner, const_apply, sum_mul]

lemma wInner_const_right (f : ι → 𝕜) (a : 𝕜) :
    ⟪f, const _ a⟫_[𝕜, w] = a * (∑ i, w i • conj (f i)) := by simp [wInner, const_apply, mul_sum]

@[simp] lemma wInner_one_const_left (a : 𝕜) (f : ι → 𝕜) :
    ⟪const _ a, f⟫_[𝕜] = (∑ i, f i) * conj a := by simp [wInner_one_eq_sum, sum_mul]

@[simp] lemma wInner_one_const_right (f : ι → 𝕜) (a : 𝕜) :
    ⟪f, const _ a⟫_[𝕜] = a * (∑ i, conj (f i)) := by simp [wInner_one_eq_sum, mul_sum]

@[simp] lemma wInner_cWeight_const_left (a : 𝕜) (f : ι → 𝕜) :
    ⟪const _ a, f⟫ₙ_[𝕜] = 𝔼 i, f i * conj a := by simp [wInner_cWeight_eq_expect]

@[simp] lemma wInner_cWeight_const_right (f : ι → 𝕜) (a : 𝕜) :
    ⟪f, const _ a⟫ₙ_[𝕜] = a * (𝔼 i, conj (f i)) := by simp [wInner_cWeight_eq_expect, mul_expect]

lemma wInner_one_eq_inner (f g : ι → 𝕜) :
    ⟪f, g⟫_[𝕜, 1] = ⟪(WithLp.equiv 2 _).symm f, (WithLp.equiv 2 _).symm g⟫_𝕜 := by
  simp [wInner]

lemma inner_eq_wInner_one (f g : PiLp 2 fun _i : ι ↦ 𝕜) :
    ⟪f, g⟫_𝕜 = ⟪WithLp.equiv 2 _ f, WithLp.equiv 2 _ g⟫_[𝕜, 1] := by simp [wInner]

lemma linearIndependent_of_ne_zero_of_wInner_one_eq_zero {f : κ → ι → 𝕜} (hf : ∀ k, f k ≠ 0)
    (hinner : Pairwise fun k₁ k₂ ↦ ⟪f k₁, f k₂⟫_[𝕜] = 0) : LinearIndependent 𝕜 f := by
  simp_rw [wInner_one_eq_inner] at hinner
  have := linearIndependent_of_ne_zero_of_inner_eq_zero ?_ hinner
  exacts [this, hf]

lemma linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero {f : κ → ι → 𝕜} (hf : ∀ k, f k ≠ 0)
    (hinner : Pairwise fun k₁ k₂ ↦ ⟪f k₁, f k₂⟫ₙ_[𝕜] = 0) : LinearIndependent 𝕜 f := by
  cases isEmpty_or_nonempty ι
  · have : IsEmpty κ := ⟨fun k ↦ hf k <| Subsingleton.elim ..⟩
    exact linearIndependent_empty_type
  · exact linearIndependent_of_ne_zero_of_wInner_one_eq_zero hf <| by
      simpa [wInner_cWeight_eq_smul_wInner_one, ← NNRat.cast_smul_eq_nnqsmul 𝕜] using hinner

lemma wInner_nonneg (hw : 0 ≤ w) (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜, w] :=
  sum_nonneg fun _ _ ↦ smul_nonneg (hw _) <| mul_nonneg (hg _) (star_nonneg_iff.2 (hf _))

lemma norm_wInner_le (hw : 0 ≤ w) : ‖⟪f, g⟫_[𝕜, w]‖ ≤ ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫_[ℝ, w] :=
  (norm_sum_le ..).trans_eq <| sum_congr rfl fun i _ ↦ by
    simp [Algebra.smul_def, norm_mul, abs_of_nonneg (hw i)]

end Function

section Real
variable {w f g : ι → ℝ}

lemma abs_wInner_le (hw : 0 ≤ w) : |⟪f, g⟫_[ℝ, w]| ≤ ⟪|f|, |g|⟫_[ℝ, w] := by
  simpa using norm_wInner_le (𝕜 := ℝ) hw

end Real
end RCLike
