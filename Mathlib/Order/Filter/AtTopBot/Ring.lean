/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Filter.AtTopBot.Group

/-!
# Convergence to ±infinity in ordered rings
-/

variable {α β : Type*}

namespace Filter

section OrderedSemiring

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] {l : Filter β} {f g : β → α}

theorem Tendsto.atTop_mul_atTop₀ (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ hg
  filter_upwards [hg.eventually (eventually_ge_atTop 0),
    hf.eventually (eventually_ge_atTop 1)] with _ using le_mul_of_one_le_left

theorem tendsto_mul_self_atTop : Tendsto (fun x : α => x * x) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ tendsto_id

/-- The monomial function `x^n` tends to `+∞` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_atTop`. -/
theorem tendsto_pow_atTop {n : ℕ} (hn : n ≠ 0) : Tendsto (fun x : α => x ^ n) atTop atTop :=
  tendsto_atTop_mono' _ ((eventually_ge_atTop 1).mono fun _x hx => le_self_pow₀ hx hn) tendsto_id

end OrderedSemiring

theorem zero_pow_eventuallyEq [MonoidWithZero α] :
    (fun n : ℕ => (0 : α) ^ n) =ᶠ[atTop] fun _ => 0 :=
  eventually_atTop.2 ⟨1, fun _n hn ↦ zero_pow <| Nat.one_le_iff_ne_zero.1 hn⟩

section OrderedRing

variable [Ring α] [PartialOrder α] [IsOrderedRing α] {l : Filter β} {f g : β → α}

theorem Tendsto.atTop_mul_atBot₀ (hf : Tendsto f l atTop) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot := by
  have := hf.atTop_mul_atTop₀ <| tendsto_neg_atBot_atTop.comp hg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

@[deprecated (since := "2025-02-13")]
alias Tendsto.atTop_mul_atBot := Tendsto.atTop_mul_atBot₀

theorem Tendsto.atBot_mul_atTop₀ (hf : Tendsto f l atBot) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atBot := by
  have : Tendsto (fun x => -f x * g x) l atTop :=
    (tendsto_neg_atBot_atTop.comp hf).atTop_mul_atTop₀ hg
  simpa only [Function.comp_def, neg_mul_eq_neg_mul, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

@[deprecated (since := "2025-02-13")]
alias Tendsto.atBot_mul_atTop := Tendsto.atBot_mul_atTop₀

theorem Tendsto.atBot_mul_atBot₀ (hf : Tendsto f l atBot) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atTop := by
  have : Tendsto (fun x => -f x * -g x) l atTop :=
    (tendsto_neg_atBot_atTop.comp hf).atTop_mul_atTop₀ (tendsto_neg_atBot_atTop.comp hg)
  simpa only [neg_mul_neg] using this

end OrderedRing

section LinearOrderedSemiring

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} {f : β → α}

theorem Tendsto.atTop_of_const_mul₀ {c : α} (hc : 0 < c) (hf : Tendsto (fun x => c * f x) l atTop) :
    Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (c * b)).mono
    fun _x hx => le_of_mul_le_mul_left hx hc

theorem Tendsto.atTop_of_mul_const₀ {c : α} (hc : 0 < c) (hf : Tendsto (fun x => f x * c) l atTop) :
    Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b * c)).mono
    fun _x hx => le_of_mul_le_mul_right hx hc

@[simp]
theorem tendsto_pow_atTop_iff {n : ℕ} : Tendsto (fun x : α => x ^ n) atTop atTop ↔ n ≠ 0 :=
  ⟨fun h hn => by simp only [hn, pow_zero, not_tendsto_const_atTop] at h, tendsto_pow_atTop⟩

end LinearOrderedSemiring

theorem not_tendsto_pow_atTop_atBot [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    ∀ {n : ℕ}, ¬Tendsto (fun x : α => x ^ n) atTop atBot
  | 0 => by simp [not_tendsto_const_atBot]
  | n + 1 => (tendsto_pow_atTop n.succ_ne_zero).not_tendsto disjoint_atTop_atBot

end Filter

open Filter

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

theorem exists_lt_mul_self (a : R) : ∃ x ≥ 0, a < x * x :=
  ((eventually_ge_atTop 0).and (tendsto_mul_self_atTop.eventually (eventually_gt_atTop a))).exists

theorem exists_le_mul_self (a : R) : ∃ x ≥ 0, a ≤ x * x :=
  let ⟨x, hx0, hxa⟩ := exists_lt_mul_self a
  ⟨x, hx0, hxa.le⟩
