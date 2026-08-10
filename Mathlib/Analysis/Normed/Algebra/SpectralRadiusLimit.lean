/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Subadditive
public import Mathlib.Data.Fintype.Order

/-!
# The spectrum radius limit in a normed ring

This file defines the spectal radius limit `lim ‖a ^ k‖ ^ (1 / k)` in a normed ring and proves
basic properties.

## Main definitions

* `spectralRadiusLimit a`: the limit of the sequence `‖a ^ k‖ ^ (1 / k)`.

## Main statements

* `tendsto_spectralRadiusLim`: the sequence `‖a ^ k‖ ^ (1 / k)` converges to `spectralRadiusLimit`.
* `spectralRadiusLim_add_le`: `spectralRadiusLimit` is subadditive.
* `spectralRadiusLim_mul_le`: `spectralRadiusLimit` is submultiplicative.

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

theorem spectralRadiusLim_le_norm (a : A) : spectralRadiusLim a ≤ ‖a‖ := by
  refine le_of_tendsto (tendsto_spectralRadiusLim a)
    (Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩)
  grw [norm_pow_le' a hn, ← Real.rpow_natCast_mul (by positivity),
    mul_inv_cancel₀ (by positivity), Real.rpow_one]

theorem spectralRadiusLim_pow_of_ne_zero (a : A) (n : ℕ) (hn : n ≠ 0) :
    spectralRadiusLim (a ^ n) = spectralRadiusLim a ^ n := by
  refine tendsto_nhds_unique (tendsto_spectralRadiusLim (a ^ n)) ((tendsto_spectralRadiusLim a).comp
    (strictMono_mul_left_of_pos hn.pos).tendsto_atTop |>.pow n |>.congr fun k ↦ ?_)
  rw [Function.comp_apply, Nat.cast_mul, mul_inv_rev,
    ← Real.rpow_mul_natCast (by positivity), inv_mul_cancel_right₀ (by simpa), pow_mul]

theorem spectralRadiusLim_pow [NormOneClass A] (a : A) (n : ℕ) :
    spectralRadiusLim (a ^ n) = spectralRadiusLim a ^ n := by
  by_cases hn : n = 0
  · simpa [hn, eq_comm] using tendsto_spectralRadiusLim (1 : A)
  · exact spectralRadiusLim_pow_of_ne_zero a n hn

theorem spectralRadiusLim_le' (a : A) (n : ℕ) (hn : n ≠ 0) :
    spectralRadiusLim a ≤ ‖a ^ n‖ ^ (n : ℝ)⁻¹ := by
  grw [← spectralRadiusLim_le_norm, spectralRadiusLim_pow_of_ne_zero a n hn,
    ← Real.rpow_natCast_mul, mul_inv_cancel₀ (by simpa), Real.rpow_one] <;>
    apply spectralRadiusLim_nonneg

theorem exists_le_spectralRadiusLim (a : A) (ε : ℝ) (hε0 : 0 < ε) :
    ∃ C > 0, ∀ n, ‖a ^ n‖ ≤ C * (spectralRadiusLim a + ε) ^ n := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp ((tendsto_spectralRadiusLim a).eventually_le_const
    ((lt_add_iff_pos_right (spectralRadiusLim a)).mpr hε0))
  use max 1 (⨆ k : Set.Iic n, ‖a ^ k.val‖ / (spectralRadiusLim a + ε) ^ k.val)
  constructor
  · positivity
  · intro k
    rcases le_or_gt k n with hk | hk
    · rw [← div_le_iff₀]
      · exact le_max_of_le_right (le_ciSup_of_le (Finite.bddAbove_range _) ⟨k, hk⟩ le_rfl)
      · apply pow_pos
        grind [spectralRadiusLim_nonneg]
    · grw [← hn k hk.le, ← le_max_left, one_mul, ← Real.rpow_mul_natCast (by positivity),
        inv_mul_cancel₀ (by simp; grind), Real.rpow_one]

theorem Set.Finite.lt_ciInf_iff' {ι α : Type*} [ConditionallyCompleteLinearOrder α] {a : α}
    {s : Set ι} {f : ι → α} (hs : s.Finite) (h : s.Nonempty) :
    a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := by
  sorry

theorem Finite.lt_ciInf_iff {ι α : Type*} [Finite ι] [Nonempty ι]
    [ConditionallyCompleteLinearOrder α] {a : α}
    {f : ι → α} : a < ⨅ i, f i ↔ ∀ x, a < f x := by
  simpa using Set.finite_univ.lt_ciInf_iff' (by simp)

theorem exists_spectralRadiusLim_le (a : A) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < spectralRadiusLim a) :
    ∃ C > 0, ∀ n, C * (spectralRadiusLim a - ε) ^ n ≤ ‖a ^ n‖ := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp ((tendsto_spectralRadiusLim a).eventually_const_le
    (sub_lt_self (spectralRadiusLim a) hε0))
  use min 1 (⨅ k : Set.Iic n, ‖a ^ k.val‖ / (spectralRadiusLim a - ε) ^ k.val)
  constructor
  · have h : 0 < spectralRadiusLim a := hε0.trans hε
    refine lt_min one_pos (Finite.lt_ciInf_iff.mpr fun x ↦ div_pos ?_ (by positivity))
    contrapose! h
    by_cases hx : x.val = 0
    · rw [hx, pow_zero] at h
      grw [spectralRadiusLim_le_norm, ← one_mul a, norm_mul_le, h, zero_mul]
    · grw [spectralRadiusLim_le' a x hx, h, Real.zero_rpow (by simpa)]
  · intro k
    rcases le_or_gt k n with hk | hk
    · rw [← le_div_iff₀ (by positivity)]
      exact min_le_of_right_le (ciInf_le_of_le (Finite.bddBelow_range _) ⟨k, hk⟩ le_rfl)
    · grw [min_le_left, one_mul, hn k hk.le, ← Real.rpow_mul_natCast (by positivity),
        inv_mul_cancel₀ (by simp; grind), Real.rpow_one] <;> positivity

theorem Commute.spectralRadiusLim_add_le {a b : A} (hc : Commute a b) :
    spectralRadiusLim (a + b) ≤ spectralRadiusLim a + spectralRadiusLim b := by
  have := spectralRadiusLim_nonneg a
  have := spectralRadiusLim_nonneg b
  suffices ∀ ε > 0, ε / 3 < spectralRadiusLim (a + b) → spectralRadiusLim (a + b) - ε / 3 ≤
      (spectralRadiusLim a + ε / 3) + (spectralRadiusLim b + ε / 3) from
    le_of_forall_pos_le_add fun ε hε ↦ by grind [spectralRadiusLim_nonneg]
  intro ε hε0 hε
  obtain ⟨Cx, hCx, hx⟩ := exists_le_spectralRadiusLim a (ε / 3) (by positivity)
  obtain ⟨Cy, hCy, hy⟩ := exists_le_spectralRadiusLim b (ε / 3) (by positivity)
  obtain ⟨Cxy, hCxy, hxy⟩ := exists_spectralRadiusLim_le (a + b) (ε / 3) (by positivity) hε
  let C := Cx * Cy * ‖(1 : A)‖
  have h (n : ℕ) : Cxy * (spectralRadiusLim (a + b) - ε / 3) ^ n ≤
      C * ((spectralRadiusLim a + ε / 3) + (spectralRadiusLim b + ε / 3)) ^ n := by
    specialize hxy n
    grw [hc.add_pow, norm_sum_le, norm_mul_le, norm_mul_le, hx, hy, Nat.norm_cast_le] at hxy
    grind [Finset.mul_sum, _root_.add_pow]
  replace h (n : ℕ) (hn : n ≠ 0) : Cxy ^ (n⁻¹ : ℝ) * (spectralRadiusLim (a + b) - ε / 3) ≤
      C ^ (n⁻¹ : ℝ) * ((spectralRadiusLim a + ε / 3) + (spectralRadiusLim b + ε / 3)) := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) hn, _root_.mul_pow, _root_.mul_pow,
      ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_mul_natCast (by positivity),
      inv_mul_cancel₀ (by simpa), Real.rpow_one, Real.rpow_one]
    exact h n
  replace h : ∀ᶠ (n : ℕ) in Filter.atTop, Cxy ^ (n⁻¹ : ℝ) * (spectralRadiusLim (a + b) - ε / 3) ≤
      C ^ (n⁻¹ : ℝ) * ((spectralRadiusLim a + ε / 3) + (spectralRadiusLim b + ε / 3)) :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ h n (by grind)⟩
  refine le_of_tendsto_of_tendsto ?_ ?_ h
  · have : Filter.atTop.Tendsto (fun n : ℕ ↦ Cxy ^ (n : ℝ)⁻¹) (𝓝 1) := by
      sorry
    sorry
  · sorry

theorem Commute.spectralRadiusLim_mul_le {a b : A} (h : Commute a b) :
    spectralRadiusLim (a * b) ≤ spectralRadiusLim a * spectralRadiusLim b := by
  refine le_of_tendsto_of_tendsto (tendsto_spectralRadiusLim (a * b))
    ((tendsto_spectralRadiusLim a).mul (tendsto_spectralRadiusLim b)) (.of_forall fun n ↦ ?_)
  simp_rw [h.mul_pow]
  grw [norm_mul_le, Real.mul_rpow] <;> positivity

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing A]

/-- `spectralRadiusLimit` is subadditive. -/
theorem spectralRadiusLim_add_le (a b : A) :
    spectralRadiusLim (a + b) ≤ spectralRadiusLim a + spectralRadiusLim b :=
  (Commute.all a b).spectralRadiusLim_add_le

/-- `spectralRadiusLimit` is submultiplicative. -/
theorem spectralRadiusLim_mul_le (a b : A) :
    spectralRadiusLim (a * b) ≤ spectralRadiusLim a * spectralRadiusLim b :=
  (Commute.all a b).spectralRadiusLim_mul_le

end SeminormedCommRing
