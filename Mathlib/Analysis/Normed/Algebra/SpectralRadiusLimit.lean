/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Subadditive

/-!
# The spectrum radius limit in a normed ring

This file defines the spectal radius limit `lim ‖a ^ k‖ ^ (1 / k)` in a normed ring and proves
basic properties.

## Main definitions

* `spectralRadiusLimit a`: the limit of the sequence `‖a ^ k‖ ^ (1 / k)`.

## Main statements

* `spectrum.isOpen_resolventSet`: the resolvent set is open.
* `spectrum.isClosed`: the spectrum is closed.
* `spectrum.subset_closedBall_norm`: the spectrum is a subset of closed disk of radius
  equal to the norm.
* `spectrum.isCompact`: the spectrum is compact.
* `spectrum.spectralRadius_le_nnnorm`: the spectral radius is bounded above by the norm.

-/

@[expose] public section

open scoped Topology

variable {A : Type*}

section SeminormedRing

variable [SeminormedRing A]

/-- The limit `‖a ^ k‖ ^ (1 / k)` of an element `a` in a normed ring. -/
noncomputable def spectralRadiusLim (a : A) : ℝ :=
  Filter.atTop.limUnder fun k : ℕ ↦ ‖a ^ k‖ ^ (k : ℝ)⁻¹

theorem tendsto_spectralRadiusLim (a : A) :
    Filter.atTop.Tendsto (fun k : ℕ ↦ ‖a ^ k‖ ^ (k : ℝ)⁻¹) (𝓝 (spectralRadiusLim a)) := by
  have h : Submultiplicative fun k ↦ ‖a ^ k‖ :=
    fun m n ↦ by simpa [pow_add] using norm_mul_le (a ^ m) (a ^ n)
  exact tendsto_nhds_limUnder ⟨h.lim, h.tendsto_lim fun n ↦ norm_nonneg (a ^ n)⟩

@[bound]
theorem spectralRadiusLim_nonneg (a : A) : 0 ≤ spectralRadiusLim a :=
  isClosed_Ici.mem_of_tendsto (tendsto_spectralRadiusLim a)
    (.of_forall fun k ↦ by rw [Set.mem_Ici]; positivity)

theorem Commute.spectralRadiusLim_mul {a b : A} (h : Commute a b) :
    spectralRadiusLim (a * b) ≤ spectralRadiusLim a * spectralRadiusLim b := by
  refine OrderClosedTopology.isClosed_le'.mem_of_tendsto
    ((tendsto_spectralRadiusLim (a * b)).prodMk_nhds
      ((tendsto_spectralRadiusLim a).mul (tendsto_spectralRadiusLim b))) (.of_forall fun n ↦ ?_)
  simp_rw [Set.mem_ofPred_eq, h.mul_pow]
  grw [norm_mul_le, Real.mul_rpow] <;> positivity

theorem spectralRadiusLim_pow_of_ne_zero (a : A) (n : ℕ) (hn : n ≠ 0) :
    spectralRadiusLim (a ^ n) = spectralRadiusLim a ^ n := by
  refine tendsto_nhds_unique (tendsto_spectralRadiusLim (a ^ n)) ((((tendsto_spectralRadiusLim a).comp
    (strictMono_mul_left_of_pos hn.pos).tendsto_atTop).pow n).congr fun k ↦ ?_)
  rw [Function.comp_apply, Nat.cast_mul, mul_inv_rev,
    ← Real.rpow_mul_natCast (by positivity), inv_mul_cancel_right₀ (by simpa), pow_mul]

theorem spectralRadiusLim_pow [NormOneClass A] (a : A) (n : ℕ) :
    spectralRadiusLim (a ^ n) = spectralRadiusLim a ^ n := by
  by_cases hn : n = 0
  · simpa [hn, eq_comm] using tendsto_spectralRadiusLim (1 : A)
  · exact spectralRadiusLim_pow_of_ne_zero a n hn

theorem Commute.spectralRadiusLim_add_le {a b : A} (hc : Commute a b) :
    spectralRadiusLim (a + b) ≤ spectralRadiusLim a + spectralRadiusLim b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h_le : ∀ a : A, ∃ C > 0, ∀ n, ‖a ^ n‖ ≤ C * (spectralRadiusLim a + ε / 3) ^ n := by
    sorry
  have h_ge : ∀ a : A, ∃ C > 0, ∀ n, C * (spectralRadiusLim a - ε / 3) ^ n ≤ ‖a ^ n‖ := by
    sorry
  suffices spectralRadiusLim (a + b) - ε / 3 ≤ (spectralRadiusLim a + ε / 3) + (spectralRadiusLim b + ε / 3) by
    grind
  obtain ⟨Cx, hCx, hx⟩ := h_le a
  obtain ⟨Cy, hCy, hy⟩ := h_le b
  obtain ⟨Cxy, hCxy, hxy⟩ := h_ge (a + b)
  let C := Cx * Cy * ‖(1 : A)‖
  suffices ∀ n, Cxy * (spectralRadiusLim (a + b) - ε / 3) ^ n ≤ C * ((spectralRadiusLim a + ε / 3) + (spectralRadiusLim b + ε / 3)) ^ n by
    -- take `n`th powers and take the limit
    sorry
  intro n
  rw [add_pow]
  specialize hxy n
  have tmp (k : ℕ) : ‖(n.choose k : A)‖ ≤ (n.choose k) * ‖(1 : A)‖ := by
    grw [← nsmul_one, norm_nsmul_le]
  have := spectralRadiusLim_nonneg a
  have := spectralRadiusLim_nonneg b
  grw [hc.add_pow, norm_sum_le, norm_mul_le, norm_mul_le, hx, hy, tmp] at hxy
  grind [Finset.mul_sum]

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing A]

theorem spectralRadiusLim_mul (a b : A) :
    spectralRadiusLim (a * b) ≤ spectralRadiusLim a * spectralRadiusLim b :=
  (Commute.all a b).spectralRadiusLim_mul

theorem spectralRadiusLim_add_le (a b : A) :
    spectralRadiusLim (a + b) ≤ spectralRadiusLim a + spectralRadiusLim b :=
  (Commute.all a b).spectralRadiusLim_add_le

end SeminormedCommRing
