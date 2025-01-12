/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Analysis.Normed.Field.Basic

/-!
# A normed field is a completable topological field
-/

variable {F : Type*} [NormedField F]

instance NormedField.instCompletableTopField : CompletableTopField F where
  t0 := (inferInstanceAs <| T0Space _).t0
  nice f hc hn := by
    -- We show in a rather pedestrian way that if `x` and `y` are uniformly close
    -- and away from `0`, then `x⁻¹` and `y⁻¹` are also uniformly close.
    rw [Metric.cauchy_iff] at hc ⊢
    obtain ⟨hf₁, hf₂⟩ := hc
    refine ⟨Filter.map_neBot, ?_⟩
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.inf_eq_bot_iff.mp hn
    obtain ⟨ε, hε₀, hε⟩ := Metric.mem_nhds_iff.mp hU
    intro δ hδ₀
    obtain ⟨t, ht₁, ht₂⟩ := hf₂ (δ * ε * ε) (by positivity)
    let t' := t ∩ V
    have h : ∀ x ∈ t', ∀ y ∈ t', dist x y < δ * ε * ε :=
      fun x hx y hy ↦
        ht₂ x (Set.mem_of_mem_inter_left hx) y (Set.mem_of_mem_inter_left hy)
    simp_rw [Filter.mem_map]
    refine ⟨(· ⁻¹) ⁻¹' t', by simpa only [Set.inv_preimage, inv_inv] using Filter.inter_mem ht₁ hV,
      fun x hx y hy ↦ ?_⟩
    simp only [Set.inv_preimage, Set.mem_inv] at hx hy
    specialize h x⁻¹ hx y⁻¹ hy
    rw [dist_eq_norm_sub] at h ⊢
    have hinv {z : F} (hz : z⁻¹ ∈ t') : z⁻¹ ∉ Metric.ball 0 ε :=
      fun H ↦ (Set.mem_empty_iff_false _).mp <|
        hUV ▸ Set.mem_inter (hε H) (Set.mem_of_mem_inter_right hz)
    have h₀ {z : F} (hz : z⁻¹ ∈ t') : z ≠ 0 := by
      rintro rfl
      exact inv_zero (G₀ := F) ▸ hinv hz <| Metric.mem_ball_self hε₀
    have Hε {z : F} (hz : z⁻¹ ∈ t') : ‖z‖ ≤ ε⁻¹ := by
      refine le_inv_of_le_inv₀ hε₀ ?_
      simpa only [Metric.mem_ball, dist_zero_right, norm_inv, not_lt] using hinv hz
    have hx₀ := h₀ hx
    have hy₀ := h₀ hy
    rw [inv_sub_inv hx₀ hy₀, norm_div, norm_mul, norm_sub_rev,
      div_lt_iff₀ (by simp [hx₀, hy₀])] at h
    refine h.trans_le ?_
    rw [mul_assoc, mul_assoc, ← mul_assoc ε]
    conv_rhs => rw [← mul_one δ]
    gcongr
    calc ε * ε * (‖x‖ * ‖y‖)
    _ ≤ ε * ε * (ε⁻¹ * ε⁻¹) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (Hε hx) (Hε hy) (norm_pos_iff.mpr hy₀).le (inv_pos_of_pos hε₀).le)
        (mul_pos hε₀ hε₀).le
    _ = 1 := by rw [mul_mul_mul_comm, mul_inv_cancel₀ hε₀.ne', one_mul]
