/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Subadditive

import Mathlib.Data.Fintype.Order

/-!
# The Gelfand radius in a normed ring

This file defines the Gelfand radius in a normed ring as the limit of `lim ‖a ^ k‖ ^ (1 / k)`
and proves basic properties.

## Main definitions

* `gelfandRadius a`: the limit of the sequence `‖a ^ k‖ ^ (1 / k)`.

## Main statements

* `tendsto_gelfandRadius`: the sequence `‖a ^ k‖ ^ (1 / k)` converges to `gelfandRadius`.
* `gelfandRadius_add_le`: `gelfandRadius` is subadditive.
* `gelfandRadius_mul_le`: `gelfandRadius` is submultiplicative.

-/

@[expose] public section

open Filter

open scoped Topology

variable {𝕜 A : Type*}

section SeminormedRing

variable [NormedField 𝕜] [SeminormedRing A] [NormedAlgebra 𝕜 A]

/-- The limit `‖a ^ k‖ ^ (1 / k)` of an element `a` in a normed ring.
We use `k : ℕ+` to ease the eventual generalization to `NonUnitalSeminormedRing`. -/
noncomputable def gelfandRadius (a : A) : ℝ :=
  atTop.limUnder fun k : ℕ+ ↦ ‖a ^ (k : ℕ)‖ ^ (k : ℝ)⁻¹

/-- `gelfandRadius a` is the limit of `‖a ^ k‖ ^ (1 / k)` over `k : ℕ+`.
See `tendsto_gelfandRadius` for the limit over `k : ℕ`. -/
theorem tendsto_gelfandRadius' (a : A) :
    atTop.Tendsto (fun k : ℕ+ ↦ ‖a ^ (k : ℕ)‖ ^ (k : ℝ)⁻¹) (𝓝 (gelfandRadius a)) := by
  have h : Submultiplicative fun k ↦ ‖a ^ k‖ :=
    fun m n ↦ by simpa [pow_add] using norm_mul_le (a ^ m) (a ^ n)
  exact tendsto_nhds_limUnder ⟨h.lim,
    (h.tendsto_lim fun n ↦ norm_nonneg (a ^ n)).comp tendsto_PNat_val_atTop_atTop⟩

/-- `gelfandRadius a` is the limit of `‖a ^ k‖ ^ (1 / k)` over `k : ℕ`.
See `tendsto_gelfandRadius'` for the limit over `k : ℕ+`. -/
theorem tendsto_gelfandRadius (a : A) :
    atTop.Tendsto (fun k : ℕ ↦ ‖a ^ k‖ ^ (k : ℝ)⁻¹) (𝓝 (gelfandRadius a)) :=
  PNat.tendsto_comp_val_iff.mp (tendsto_gelfandRadius' a)

theorem gelfandRadius_nonneg (a : A) : 0 ≤ gelfandRadius a :=
  ge_of_tendsto' (tendsto_gelfandRadius a) fun _ ↦ by positivity

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function
/-- The `positivity` extension which identifies expressions of the form `gelfandRadius a`. -/
@[positivity gelfandRadius _]
meta def evalgelfandRadius : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@gelfandRadius $A $KA $a) =>
    assertInstancesCommute
    pure (.nonnegative q(gelfandRadius_nonneg $a))
  | _, _, _ => throwError "not gelfandRadius"

end Mathlib.Meta.Positivity

theorem gelfandRadius_le_norm (a : A) : gelfandRadius a ≤ ‖a‖ := by
  refine le_of_tendsto (tendsto_gelfandRadius' a) (Eventually.of_forall fun k ↦ ?_)
  grw [Real.rpow_inv_le_iff_of_pos, Real.rpow_natCast, norm_pow_le'] <;> positivity

@[simp]
theorem gelfandRadius_zero : gelfandRadius (0 : A) = 0 :=
  le_antisymm (by simpa using gelfandRadius_le_norm (0 : A)) (gelfandRadius_nonneg 0)

@[simp]
theorem gelfandRadius_neg (a : A) : gelfandRadius (-a) = gelfandRadius a :=
  tendsto_nhds_unique (by simpa using tendsto_gelfandRadius (-a)) (tendsto_gelfandRadius a)

theorem gelfandRadius_smul (c : 𝕜) (a : A) :
    gelfandRadius (c • a) = ‖c‖ * gelfandRadius a := by
  refine tendsto_nhds_unique ((tendsto_gelfandRadius' (c • a)).congr fun k ↦ ?_)
    ((tendsto_gelfandRadius' a).const_mul ‖c‖)
  simp [smul_pow, norm_smul, Real.mul_rpow, ← Real.rpow_natCast_mul]

theorem gelfandRadius_pow_of_ne_zero (a : A) {n : ℕ} (hn : n ≠ 0) :
    gelfandRadius (a ^ n) = gelfandRadius a ^ n := by
  refine tendsto_nhds_unique ((tendsto_gelfandRadius (a ^ n)).congr fun k ↦ ?_)
    (((tendsto_gelfandRadius a).comp (strictMono_mul_left_of_pos hn.pos).tendsto_atTop).pow n)
  rw [Function.comp_apply, Nat.cast_mul, mul_inv_rev,
    ← Real.rpow_mul_natCast (by positivity), inv_mul_cancel_right₀ (by simpa), pow_mul]

theorem gelfandRadius_pow [NormOneClass A] (a : A) (n : ℕ) :
    gelfandRadius (a ^ n) = gelfandRadius a ^ n := by
  by_cases hn : n = 0
  · symm
    simpa [hn] using tendsto_gelfandRadius (1 : A)
  · exact gelfandRadius_pow_of_ne_zero a hn

@[simp]
theorem gelfandRadius_one [NormOneClass A] : gelfandRadius (1 : A) = 1 := by
  simpa using gelfandRadius_pow 1 0

theorem gelfandRadius_le_norm_pow (a : A) {n : ℕ} (hn : n ≠ 0) :
    gelfandRadius a ≤ ‖a ^ n‖ ^ (n : ℝ)⁻¹ := by
  grw [← gelfandRadius_le_norm, gelfandRadius_pow_of_ne_zero a hn,
    ← Real.rpow_natCast_mul (by positivity), mul_inv_cancel₀ (by simpa), Real.rpow_one]

theorem exists_le_gelfandRadius (a : A) (ε : ℝ) (hε0 : 0 < ε) :
    ∃ C > 0, ∀ n, ‖a ^ n‖ ≤ C * (gelfandRadius a + ε) ^ n := by
  obtain ⟨n, hn⟩ := eventually_atTop.mp ((tendsto_gelfandRadius a).eventually_le_const
    ((lt_add_iff_pos_right (gelfandRadius a)).mpr hε0))
  refine ⟨max 1 (⨆ k : Set.Iic n, ‖a ^ k.val‖ / (gelfandRadius a + ε) ^ k.val),
    by positivity, fun k ↦ ?_⟩
  rcases le_or_gt k n with hk | hk
  · grw [← div_le_iff₀ (by positivity), ← le_max_right]
    exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨k, hk⟩ le_rfl
  · grw [← le_max_left, one_mul, ← hn k hk.le, ← Real.rpow_mul_natCast (by positivity),
      inv_mul_cancel₀ (by grind [Nat.cast_eq_zero]), Real.rpow_one]

theorem exists_gelfandRadius_le (a : A) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < gelfandRadius a) :
    ∃ C > 0, ∀ n, C * (gelfandRadius a - ε) ^ n ≤ ‖a ^ n‖ := by
  obtain ⟨n, hn⟩ := eventually_atTop.mp ((tendsto_gelfandRadius a).eventually_const_le
    (sub_lt_self (gelfandRadius a) hε0))
  refine ⟨min 1 (⨅ k : Set.Iic n, ‖a ^ k.val‖ / (gelfandRadius a - ε) ^ k.val), ?_, fun k ↦ ?_⟩
  · have h : 0 < gelfandRadius a := hε0.trans hε
    refine lt_min one_pos (Finite.lt_ciInf_iff.mpr fun x ↦ div_pos ?_ (by positivity))
    contrapose! h
    by_cases hx : x.val = 0
    · rw [hx, pow_zero] at h
      grw [gelfandRadius_le_norm, ← one_mul a, norm_mul_le, h, zero_mul]
    · grw [gelfandRadius_le_norm_pow a hx, h, Real.zero_rpow (by simpa)]
  · rcases le_or_gt k n with hk | hk
    · grw [← le_div_iff₀ (by positivity), min_le_right]
      exact ciInf_le_of_le (Finite.bddBelow_range _) ⟨k, hk⟩ le_rfl
    · grw [min_le_left, one_mul, hn k hk.le, ← Real.rpow_mul_natCast (by positivity),
        inv_mul_cancel₀ (by simp; grind), Real.rpow_one] <;> positivity

theorem Commute.gelfandRadius_add_le {a b : A} (h : Commute a b) :
    gelfandRadius (a + b) ≤ gelfandRadius a + gelfandRadius b := by
  suffices ∀ ε > 0, ε / 3 < gelfandRadius (a + b) → gelfandRadius (a + b) - ε / 3 ≤
      (gelfandRadius a + ε / 3) + (gelfandRadius b + ε / 3) from
    le_of_forall_pos_le_add fun ε hε ↦ by grind [gelfandRadius_nonneg]
  intro ε hε0 hε
  obtain ⟨Cx, hCx, hx⟩ := exists_le_gelfandRadius a (ε / 3) (by positivity)
  obtain ⟨Cy, hCy, hy⟩ := exists_le_gelfandRadius b (ε / 3) (by positivity)
  obtain ⟨Cxy, hCxy, hxy⟩ := exists_gelfandRadius_le (a + b) (ε / 3) (by positivity) hε
  let C := Cx * Cy * ‖(1 : A)‖
  replace h (n : ℕ) : Cxy * (gelfandRadius (a + b) - ε / 3) ^ n ≤
      C * ((gelfandRadius a + ε / 3) + (gelfandRadius b + ε / 3)) ^ n := by
    specialize hxy n
    grw [h.add_pow, norm_sum_le, norm_mul_le, norm_mul_le, hx, hy, Nat.norm_cast_le] at hxy
    grind [Finset.mul_sum, _root_.add_pow]
  have hC : 0 < C := hCxy.trans_le (by simpa using h 0)
  replace h (n : ℕ) (hn : n ≠ 0) : Cxy ^ (n⁻¹ : ℝ) * (gelfandRadius (a + b) - ε / 3) ≤
      C ^ (n⁻¹ : ℝ) * ((gelfandRadius a + ε / 3) + (gelfandRadius b + ε / 3)) := by
    specialize h n
    rwa [← pow_le_pow_iff_left₀ (by positivity) (by positivity) hn, _root_.mul_pow, _root_.mul_pow,
      ← Cxy.rpow_mul_natCast (by positivity), ← C.rpow_mul_natCast (by positivity),
      inv_mul_cancel₀ (by simpa), Cxy.rpow_one, C.rpow_one]
  suffices ∀ C > (0 : ℝ), Tendsto (fun n : ℕ ↦ C ^ (n : ℝ)⁻¹) atTop (𝓝 1) from
    le_of_tendsto_of_tendsto (by simpa using (this Cxy hCxy).mul_const _)
      (by simpa using (this C hC).mul_const _) (eventually_atTop.mpr ⟨1, fun n hn ↦ h n (by grind)⟩)
  intro C hC
  rw [← C.rpow_zero]
  exact (C.continuous_const_rpow hC.ne').continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat

theorem Commute.gelfandRadius_mul_le {a b : A} (h : Commute a b) :
    gelfandRadius (a * b) ≤ gelfandRadius a * gelfandRadius b := by
  refine le_of_tendsto_of_tendsto (tendsto_gelfandRadius (a * b))
    ((tendsto_gelfandRadius a).mul (tendsto_gelfandRadius b)) (.of_forall fun n ↦ ?_)
  simp_rw [h.mul_pow]
  grw [norm_mul_le, Real.mul_rpow] <;> positivity

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing A]

/-- `gelfandRadius` is subadditive. -/
theorem gelfandRadius_add_le (a b : A) :
    gelfandRadius (a + b) ≤ gelfandRadius a + gelfandRadius b :=
  (Commute.all a b).gelfandRadius_add_le

/-- `gelfandRadius` is submultiplicative. -/
theorem gelfandRadius_mul_le (a b : A) :
    gelfandRadius (a * b) ≤ gelfandRadius a * gelfandRadius b :=
  (Commute.all a b).gelfandRadius_mul_le

end SeminormedCommRing

#min_imports
