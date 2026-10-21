/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Order.Group.DenselyOrdered
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

public section

open Filter

open scoped Topology

variable {𝕜 A : Type*}

section SeminormedRing

variable [NormedField 𝕜] [SeminormedRing A] [NormedAlgebra 𝕜 A]

/-- The limit `‖a ^ k‖ ^ (1 / k)` of an element `a` in a normed ring.
We use `k : ℕ+` to ease the eventual generalization to `NonUnitalSeminormedRing`.

This definition is not exposed. Use `tendsto_gelfandRadius` instead. -/
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
meta def evalGelfandRadius : PositivityExt where eval {u α} _ pα? e :=
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

theorem gelfandRadius_of_norm_nonpos {a : A} (ha : ‖a‖ ≤ 0) : gelfandRadius a = 0 :=
  le_antisymm ((gelfandRadius_le_norm a).trans ha) (gelfandRadius_nonneg a)

theorem gelfandRadius_le_of_norm_pow_le {B : Type*} [SeminormedRing B] {a : A} {b : B} (C : ℝ)
    (h : ∀ n, ‖a ^ n‖ ≤ C * ‖b ^ n‖) : gelfandRadius a ≤ gelfandRadius b := by
  by_cases! hC : C ≤ 0
  · specialize h 1
    grw [hC, zero_mul, pow_one] at h
    exact (gelfandRadius_of_norm_nonpos h).trans_le (gelfandRadius_nonneg b)
  · exact le_of_tendsto_of_tendsto' (tendsto_gelfandRadius a)
      (by simpa using (((C.continuous_const_rpow hC.ne').tendsto' 0 1 C.rpow_zero).comp
        tendsto_inv_atTop_nhds_zero_nat).mul (tendsto_gelfandRadius b))
          fun n ↦ by grw [h, Real.mul_rpow] <;> positivity

theorem gelfandRadius_eq_of_norm_pow {B : Type*} [SeminormedRing B] {a : A} {b : B}
    (h : ∀ n, ‖a ^ n‖ = ‖b ^ n‖) : gelfandRadius a = gelfandRadius b :=
  le_antisymm (gelfandRadius_le_of_norm_pow_le 1 (by grind))
    (gelfandRadius_le_of_norm_pow_le 1 (by grind))

@[simp]
theorem gelfandRadius_star [StarRing A] [NormedStarGroup A] (a : A) :
    gelfandRadius (star a) = gelfandRadius a :=
  gelfandRadius_eq_of_norm_pow <| by simp [← star_pow]

@[simp]
theorem gelfandRadius_op (a : A) : gelfandRadius (MulOpposite.op a) = gelfandRadius a :=
  gelfandRadius_eq_of_norm_pow <| by simp [← MulOpposite.op_pow, MulOpposite.norm_op]

theorem Isometry.gelfandRadius_map {B F : Type*} [SeminormedRing B] [FunLike F A B]
    [MonoidWithZeroHomClass F A B] {f : F} (hf : Isometry f) (a : A) :
    gelfandRadius (f a) = gelfandRadius a :=
  gelfandRadius_eq_of_norm_pow <| by simp [← map_pow, hf.norm_map_of_map_zero (map_zero f)]

@[simp]
theorem gelfandRadius_zero : gelfandRadius (0 : A) = 0 :=
  gelfandRadius_of_norm_nonpos norm_zero.le

@[simp]
theorem gelfandRadius_neg (a : A) : gelfandRadius (-a) = gelfandRadius a :=
  gelfandRadius_eq_of_norm_pow (by simp)

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

@[simp]
theorem gelfandRadius_one [NormOneClass A] : gelfandRadius (1 : A) = 1 :=
  tendsto_nhds_unique (tendsto_gelfandRadius 1) (by simp)

theorem gelfandRadius_pow [NormOneClass A] (a : A) (n : ℕ) :
    gelfandRadius (a ^ n) = gelfandRadius a ^ n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · exact gelfandRadius_pow_of_ne_zero a hn

theorem gelfandRadius_le_norm_pow (a : A) {n : ℕ} (hn : n ≠ 0) :
    gelfandRadius a ≤ ‖a ^ n‖ ^ (n : ℝ)⁻¹ := by
  grw [← gelfandRadius_le_norm, gelfandRadius_pow_of_ne_zero a hn,
    ← Real.rpow_natCast_mul (by positivity), mul_inv_cancel₀ (by simpa), Real.rpow_one]

theorem gelfandRadius_pow_le_norm_pow (a : A) {n : ℕ} (hn : n ≠ 0) :
    gelfandRadius a ^ n ≤ ‖a ^ n‖ :=
  gelfandRadius_pow_of_ne_zero a hn ▸ gelfandRadius_le_norm (a ^ n)

/-- If `gelfandRadius a < r`, then there is some `C` for which `‖a ^ n‖ ≤ C * r ^ n` for all `n`.
See `gelfandRadius_le_of_bound` for the converse. -/
theorem norm_pow_le_mul_pow_of_gelfandRadius_lt (a : A) {r : ℝ} (hr : gelfandRadius a < r) :
    ∃ C > 0, ∀ n, ‖a ^ n‖ ≤ C * r ^ n := by
  have hr0 : 0 < r := (gelfandRadius_nonneg a).trans_lt hr
  have h : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ / r ^ n ≤ 1 := by
    filter_upwards [(tendsto_gelfandRadius a).eventually_le_const hr, eventually_ne_atTop 0]
      with n hn hn0
    rwa [div_le_one (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_inv_le_iff_of_pos (by positivity) hr0.le (by positivity)]
  obtain ⟨C, hC⟩ := (isBoundedUnder_of_eventually_le h).bddAbove_range
  exact ⟨max C 1, by positivity, fun n ↦ by
    grw [← le_max_left, ← div_le_iff₀ (by positivity)]; exact hC ⟨n, rfl⟩⟩

/-- If `‖a ^ n‖ ≤ C * r ^ n` for all `n`, then `gelfandRadius a ≤ r`.
See `exists_le_gelfandRadius` for the converse. -/
theorem gelfandRadius_le_of_bound {a : A} {C r : ℝ} (hr : 0 ≤ r)
    (h : ∀ n, ‖a ^ n‖ ≤ C * r ^ n) : gelfandRadius a ≤ r := by
  have hC : 0 < max C 1 := by positivity
  replace h (n : ℕ) : ‖a ^ n‖ ≤ max C 1 * r ^ n := by grw [h n, ← le_max_left]
  have hlim : Tendsto (fun n : ℕ ↦ max C 1 ^ (n : ℝ)⁻¹ * r) atTop (𝓝 r) := by
    simpa using (((Real.continuous_const_rpow hC.ne').tendsto' 0 1 (Real.rpow_zero _)).comp
      tendsto_inv_atTop_nhds_zero_nat).mul_const r
  refine le_of_tendsto_of_tendsto (tendsto_gelfandRadius a) hlim ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  grw [h n, Real.mul_rpow hC.le (by positivity), Real.pow_rpow_inv_natCast hr hn]

theorem Commute.gelfandRadius_add_le {a b : A} (h : Commute a b) :
    gelfandRadius (a + b) ≤ gelfandRadius a + gelfandRadius b := by
  refine le_add_of_forall_lt fun x hx y hy ↦ ?_
  have hx0 := (gelfandRadius_nonneg a).trans_lt hx
  have hy0 := (gelfandRadius_nonneg b).trans_lt hy
  obtain ⟨Ca, hCa, ha⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt a hx
  obtain ⟨Cb, hCb, hb⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt b hy
  refine gelfandRadius_le_of_bound (C := Ca * Cb * ‖(1 : A)‖) (by positivity) fun n ↦ ?_
  grw [h.add_pow, norm_sum_le, norm_mul_le, norm_mul_le, ha, hb, Nat.norm_cast_le]
  grind [Finset.mul_sum, _root_.add_pow]

theorem Commute.gelfandRadius_mul_le {a b : A} (h : Commute a b) :
    gelfandRadius (a * b) ≤ gelfandRadius a * gelfandRadius b := by
  refine le_of_tendsto_of_tendsto (tendsto_gelfandRadius (a * b))
    ((tendsto_gelfandRadius a).mul (tendsto_gelfandRadius b)) (.of_forall fun n ↦ ?_)
  simp_rw [h.mul_pow]
  grw [norm_mul_le, Real.mul_rpow] <;> positivity

theorem Pi.gelfandRadius_eq {ι : Type*} [Fintype ι] {A : ι → Type*} [Π i, SeminormedRing (A i)]
    (a : Π i, A i) : gelfandRadius a = ⨆ i, gelfandRadius (a i) := by
  rcases isEmpty_or_nonempty ι
  · simp [Subsingleton.elim a 0]
  let s : Finset ι := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  rw [← Finset.sup'_univ_eq_ciSup]
  refine tendsto_nhds_unique_of_forall (tendsto_gelfandRadius a)
    (Filter.Tendsto.finset_sup'_nhds_apply hs fun i hi ↦ tendsto_gelfandRadius (a i)) fun k ↦ ?_
  have h (x y : NNReal) : max (x : ℝ) y ^ (k : ℝ)⁻¹ = max (x ^ (k : ℝ)⁻¹) (y ^ (k : ℝ)⁻¹) := by
    simp [Real.rpow_max]
  rw [Pi.pow_def, Pi.norm_def, ← s.sup'_eq_sup hs]
  exact s.apply_sup'_eq_sup'_comp hs (f := fun i ↦ ‖a i ^ k‖₊) (fun x ↦ (x : ℝ) ^ (k : ℝ)⁻¹) h

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
