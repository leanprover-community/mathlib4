/-
Copyright (c) 2025 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Data.Real.StarOrdered

/-!
# closed range theorem

This file contains the closed range theorem
reference : [Rudin, *Functional Analysis* (Theorem 4.12)][rudin1991]
-/

open Metric

example {a b : ℝ} (ha : a ≤ 1) (hb : b ≥ 0) : a * b ≤ b := by
  exact mul_le_of_le_one_left hb ha

lemma p12 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] (T : α →L[ℝ] β) {δ : ℝ} (h0 : δ > 0)
    (h : ∀ f : β →L[ℝ] ℝ , δ * ‖f‖ ≤ ‖f.comp T‖) :
    closure (T '' (ball 0 1)) ⊇ ball 0 δ := fun y hy ↦ by
  have t1 : Convex ℝ (closure (T '' (ball 0 1))) :=
    (convex_ball 0 1).is_linear_image T.isBoundedLinearMap.toIsLinearMap |> .closure
  have t3 : Balanced ℝ (closure (T '' ball 0 1)) := by
    refine Balanced.closure fun _ ha _ ⟨_, ⟨_, hc, hd⟩, d⟩ ↦ ?_
    simp only [← d, ← hd, ← ContinuousLinearMap.map_smul]
    exact Set.mem_image_of_mem T (balanced_ball_zero.smul_mem ha hc)
  have t4 : (closure (T '' ball 0 1)).Nonempty := ⟨T 0, subset_closure ⟨0, by simp⟩⟩
  have : ∀ z ∉ closure (T '' (ball 0 1)), z ∉ ball 0 δ := fun z hz ↦ by
    obtain ⟨f, hf1, hf2⟩ := RCLike.geometric_hahn_banach' t1 isClosed_closure t3 t4 z hz
    have ha : ∀ a ∈ closedBall (0 : α) 1, ‖f (T a)‖ < 1 := fun a ha ↦
      hf2 (T a) ((image_closure_subset_closure_image T.continuous)
        ⟨a, by simp [closure_ball (0 : α) (zero_ne_one' ℝ).symm, ha]⟩)
    have : ‖(f : β →L[ℝ] ℝ).comp T‖ ≤ 1 := by
      refine (f.comp T).opNorm_le_bound' (zero_le_one' ℝ) fun x hx ↦ ?_
      have xin : (1 / ‖x‖) • x ∈ closedBall 0 1 := by simp [norm_smul_of_nonneg ?_ x, hx]
      exact le_of_lt (by calc
        _ = ‖f.comp T ((1 / ‖x‖) • x)‖ * ‖x‖ := by simp [field]
        _ < 1 * ‖x‖ := (mul_lt_mul_iff_of_pos_right (by positivity)).mpr (ha ((1 / ‖x‖) • x) xin))
    have : δ < ‖z‖ := by calc
      _ < δ * (‖f‖ * ‖z‖) := by
        grind [lt_mul_iff_one_lt_right, ContinuousLinearMap.le_opNorm]
      _ ≤ ‖(f : β →L[ℝ] ℝ).comp T‖ * ‖z‖ := by
        grind [mul_assoc, mul_le_mul_of_nonneg_right, norm_nonneg]
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg z) this
    simp [le_of_lt this]
  by_contra! nh
  exact (this y nh) hy

/-- Following [Rudin, *Functional Analysis* (Theorem 4.12 (b) => (c))][rudin1991] -/
lemma p23 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] [CompleteSpace α] (T : α →L[ℝ] β) {δ : ℝ}
    (h0 : δ > 0) (h : closure (T '' (ball 0 1)) ⊇ ball 0 δ) : T '' (ball 0 1) ⊇ ball 0 δ := by
  have int_t : interior (closure (T '' ball 0 1)) ⊇ ball 0 δ :=
    (IsOpen.subset_interior_iff isOpen_ball).mpr h
  have convex_t : Convex ℝ ((T '' (ball 0 1))) :=
    (convex_ball 0 1).is_linear_image T.isBoundedLinearMap.toIsLinearMap
  have : IsOpenMap T := T.isOpenMap' ⟨1, 0, mem_interior.mpr ⟨ball 0 δ, by simpa, by simpa⟩⟩
  have : interior (closure (T '' ball 0 1)) = interior (T '' ball 0 1) := by
    apply convex_t.interior_closure_eq_interior_of_nonempty_interior
    use 0
    exact mem_interior.mpr ⟨T '' ball 0 1, subset_refl (T '' (ball 0 1)),
      this (ball 0 1) (isOpen_ball), ⟨0, by simp⟩⟩
  rw [this] at int_t
  exact fun _ a => interior_subset (int_t a)

theorem ContinuousLinearMap.comp_le_opNorm {𝕜 𝕜₂ 𝕜₃ : Type*} {E F G : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃}
    [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (f : E →SL[σ₁₂] F) (g : F →SL[σ₂₃] G) (x : E) :
    ‖g (f x)‖ ≤ ‖g‖ * ‖f‖ * ‖x‖ := by calc
  _ ≤ ‖g‖ * ‖f x‖ := g.le_opNorm (f x)
  _ ≤ ‖g‖ * (‖f‖ * ‖x‖) := mul_le_mul_of_nonneg_left (f.le_opNorm x) (by positivity)
  _ = _ := Eq.symm (mul_assoc ‖g‖ ‖f‖ ‖x‖)

lemma p41 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] [CompleteSpace β] [CompleteSpace α] (T : α →L[ℝ] β)
    (surj : (⇑T).Surjective) : ∃ δ > 0, ∀ f : β →L[ℝ] ℝ , δ * ‖f‖ ≤ ‖f.comp T‖ := by
  have ho : IsOpen (T '' (ball 0 1)) := T.isOpenMap surj (ball 0 1) isOpen_ball
  rw [Metric.isOpen_iff] at ho
  obtain⟨δ, δpos, hδ⟩ : ∃ δ > 0, ball 0 δ ⊆ T '' (ball 0 1) := ho 0 ⟨0, by simp⟩
  refine ⟨δ, δpos, fun f ↦ ?_⟩
  have := Real.sSup_smul_of_nonneg (a := δ) (by positivity) ((fun x => ‖f x‖) '' ball 0 1)
  rw [smul_eq_mul] at this
  rw [← (f.comp T).sSup_unit_ball_eq_norm, ← f.sSup_unit_ball_eq_norm, ← this]
  refine csSup_le_csSup ?_ (by simp) ?_
  · use ‖f‖ * ‖T‖
    simp [upperBounds]
    intro a ha
    calc
    _ ≤ ‖f‖ * ‖T‖ * ‖a‖ := T.comp_le_opNorm f a
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (Std.le_of_lt ha)
  · intro _ ⟨_, ⟨b, bin, beq⟩, eq⟩
    have : δ • b ∈ ball 0 δ := by
      simp [norm_smul, abs_of_pos δpos] at ⊢ bin
      exact mul_lt_of_lt_one_right δpos bin
    obtain ⟨c, cin, ceq⟩ := hδ this
    exact ⟨c, by simpa [← eq, cin, ceq, beq] using Or.inl (Std.le_of_lt δpos)⟩

lemma closedRange {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β]
    [InnerProductSpace ℝ α] [InnerProductSpace ℝ β] [CompleteSpace β] [CompleteSpace α]
    (T : α →L[ℝ] β) : List.TFAE [
    ∃ δ > 0, ∀ f : β →L[ℝ] ℝ , δ * ‖f‖ ≤ ‖f.comp T‖,
    ∃ δ > 0, closure (T '' (ball 0 1)) ⊇ ball 0 δ,
    ∃ δ > 0, T '' (ball 0 1) ⊇ ball 0 δ,
    (⇑T).Surjective] := by
  tfae_have 1 → 2 := fun ⟨δ, δpos, h⟩ ↦ ⟨δ, δpos, p12 T δpos h⟩
  tfae_have 2 → 3 := fun ⟨δ, δpos, h⟩ ↦ ⟨δ, δpos, p23 T δpos h⟩
  tfae_have 3 → 4 := fun ⟨_, δpos, h⟩ ↦ by
    rw [← ball_subset_range_iff_surjective δpos]
    exact Set.SurjOn.subset_range h
  tfae_have 4 → 1 := p41 T
  tfae_finish
