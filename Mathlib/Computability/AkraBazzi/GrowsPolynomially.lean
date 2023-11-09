/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.EventuallyConst
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Akra-Bazzi theorem: The polynomial growth condition

This file defines and develops an API for the polynomial growth condition that appears in the
statement of the Akra-Bazzi theorem: for the Akra-Bazzi theorem to hold, the function `g` must
satisfy the condition that `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for u between b*n and n for any constant
`b ∈ (0,1)`.

## Implementation notes

Our definition states that the condition must hold for any `b ∈ (0,1)`. This is equivalent to
only requiring it for `b = 1/2` or any other particular value between 0 and 1. While this
could in principle make it harder to prove that a particular function grows polynomially,
this issue doesn't seem to arise in practice.

-/

set_option autoImplicit false

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

open Finset Real Filter Asymptotics BigOperators
open scoped Topology

@[gcongr] lemma Nat.floor_le_floor {α : Type*} [LinearOrderedSemiring α] [FloorSemiring α] :
  ∀ x y : α, x ≤ y → ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono

namespace AkraBazziRecurrence

/-- The growth condition that the function `g` must satisfy for the Akra-Bazzi theorem to apply.
It roughly states that `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for `u` between `b*n` and `n` for any
constant `b ∈ (0,1)`. -/
def GrowsPolynomially (f : ℝ → ℝ) : Prop :=
  ∀ b ∈ Set.Ioo 0 1, ∃ c₁ ∈ Set.Ioi 0, ∃ c₂ ∈ Set.Ioi 0,
    ∀ᶠ x in atTop, ∀ u ∈ Set.Icc (b * x) x, f u ∈ Set.Icc (c₁ * (f x)) (c₂ * f x)

namespace GrowsPolynomially

lemma congr_of_eventuallyEq {f g : ℝ → ℝ} (hfg : f =ᶠ[atTop] g) (hg : GrowsPolynomially g) :
    GrowsPolynomially f := by
  intro b hb
  have hg' := hg b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hg'⟩ := hg'
  refine ⟨c₁, hc₁_mem, c₂, hc₂_mem, ?_⟩
  filter_upwards [hg', (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hfg, hfg]
    with x hx₁ hx₂ hx₃
  intro u hu
  rw [hx₂ u hu.1, hx₃]
  exact hx₁ u hu

lemma iff_eventuallyEq {f g : ℝ → ℝ} (h : f =ᶠ[atTop] g) :
    GrowsPolynomially f ↔ GrowsPolynomially g :=
  ⟨fun hf => congr_of_eventuallyEq h.symm hf, fun hg => congr_of_eventuallyEq h hg⟩

theorem _root_.toIcoDiv_zsmul_eq_sub {α : Type*} [LinearOrderedAddCommGroup α] [hα : Archimedean α]
    {p : α} (hp : 0 < p) (a : α) (b : α) : toIcoDiv hp a b • p = b - toIcoMod hp a b := by
  apply eq_sub_of_add_eq
  simp only [toIcoDiv_zsmul_sub_toIcoMod]

@[gcongr]
lemma _root_.toIcoDiv_le_toIcoDiv {α : Type*} [LinearOrderedAddCommGroup α] [Archimedean α] {p : α}
    (hp : 0 < p) (a : α) (b₁ b₂ : α) (hb : b₁ ≤ b₂) : toIcoDiv hp a b₁ ≤ toIcoDiv hp a b₂ := by
  let n₁ := toIcoDiv hp a b₁
  let n₂ := toIcoDiv hp a b₂
  have hn₁ : b₁ - n₁ • p ∈ Set.Ico a (a + p) := sub_toIcoDiv_zsmul_mem_Ico hp a b₁
  have hn₂ : b₂ - n₂ • p ∈ Set.Ico a (a + p) := sub_toIcoDiv_zsmul_mem_Ico hp a b₂
  by_contra h
  have h' : b₂ - n₂ • p < a + p := hn₂.2
  have h'' : a + p ≤ b₂ - n₂ • p := calc
    a + p ≤ b₁ - n₁ • p + 1 • p := by have := hn₁.1; gcongr; simp
        _ = b₁ - (n₁ - 1) • p := by rw [sub_smul]; abel
        _ ≤ b₁ - n₂ • p := by gcongr; exact zsmul_le_zsmul (le_of_lt hp) (by linarith)
        _ ≤ b₂ - n₂ • p := by gcongr
  rw [←not_le] at h'
  exact h' h''

lemma _root_.monotone_toIcoDiv {α : Type*} [LinearOrderedAddCommGroup α] [Archimedean α] {p : α}
    (hp : 0 < p) (a : α) : Monotone (toIcoDiv hp a) := toIcoDiv_le_toIcoDiv hp a

--@[gcongr]
--lemma _root_.toIcoDiv_lt_toIcoDiv {α : Type*} [LinearOrderedAddCommGroup α] [Archimedean α] {p : α}
--    (hp : 0 < p) (a : α) (b₁ b₂ : α) (hb : b₁ + p ≤ b₂) : toIcoDiv hp a b₁ < toIcoDiv hp a b₂ := by
--  let n₁ := toIcoDiv hp a b₁
--  let n₂ := toIcoDiv hp a b₂
--  have hn₁ : b₁ - n₁ • p ∈ Set.Ico a (a + p) := sub_toIcoDiv_zsmul_mem_Ico hp a b₁
--  have hn₂ : b₂ - n₂ • p ∈ Set.Ico a (a + p) := sub_toIcoDiv_zsmul_mem_Ico hp a b₂
--  by_contra h
--  have h' : b₂ - n₂ • p < a + p := hn₂.2
--  have h'' : a + p ≤ b₂ - n₂ • p := calc
--    a + p ≤ b₁ - n₁ • p + p := by have := hn₁.1; gcongr
--        _ ≤ b₁ - n₂ • p + p := by gcongr; exact zsmul_le_zsmul (le_of_lt hp) (by linarith)
--        _ ≤ b₂ - p - n₂ • p + p := by gcongr; rwa [le_sub_iff_add_le]
--        _ = b₂ - n₂ • p := by abel
--  rw [←not_le] at h'
--  exact h' h''

-- Should go in Mathlib.Algebra.Order.ToIntervalMod
lemma _root_.induction_Ico_add {R : Type*} [LinearOrderedAddCommGroup R] [Archimedean R] {P : R → Prop}
    (x₀ r : R) (hr : 0 < r) (base : ∀ x ∈ Set.Ico x₀ (x₀ + r), P x)
    (step : ∀ n : ℤ, n ≥ 1 → (∀ z ∈ Set.Ico x₀ (x₀ + n • r), P z) →
      (∀ z ∈ Set.Ico (x₀ + n • r) (x₀ + (n+1) • r), P z)) :
    ∀ x ≥ x₀, P x :=
  fun x hx =>
    if hx' : x < x₀ + r then
      base x ⟨hx, hx'⟩
    else by
      push_neg at hx'
      refine step (toIcoDiv hr 0 (x - x₀)) ?ge_one ?main x ?memIco
      case ge_one =>
        calc 1 = toIcoDiv hr 0 (0 + r) := (toIcoDiv_apply_right hr 0).symm
             _ = toIcoDiv hr 0 (x₀ + r - x₀) := by
                    have : 0 + r = x₀ + r - x₀ := by abel
                    rw [this]
             _ ≤ _ := by gcongr
      case main =>
        intro z hz
        -- Needed by termination checker
        have toIcoDiv_nonneg_x : 0 ≤ toIcoDiv hr 0 (x - x₀) := by
          calc 0 = toIcoDiv hr 0 0 := (toIcoDiv_apply_left hr 0).symm
               _ ≤ _ := by gcongr; exact sub_nonneg_of_le hx
        have toIcoDiv_nonneg_z : 0 ≤ toIcoDiv hr 0 (z - x₀) := by
          calc 0 = toIcoDiv hr 0 0 := (toIcoDiv_apply_left hr 0).symm
               _ ≤ _ := by gcongr; exact sub_nonneg_of_le hz.1
        have _ : Int.natAbs (toIcoDiv hr 0 (z - x₀)) < Int.natAbs (toIcoDiv hr 0 (x - x₀)) := by
          zify
          rw [abs_of_nonneg toIcoDiv_nonneg_x, abs_of_nonneg toIcoDiv_nonneg_z]
          have hmain := calc
            toIcoDiv hr 0 (z - x₀) • r = 0 + toIcoDiv hr 0 (z - x₀) • r := by abel
            _ ≤ toIcoMod hr 0 (z - x₀) + toIcoDiv hr 0 (z - x₀) • r := by
                  gcongr
                  exact left_le_toIcoMod hr 0 (z - x₀)
            _ = z - x₀ := by rw [toIcoMod_add_toIcoDiv_zsmul hr 0]
            _ < toIcoDiv hr 0 (x - x₀) • r := by rw [sub_lt_iff_lt_add, add_comm]; exact hz.2
          rwa [zsmul_lt_zsmul_iff hr] at hmain
        exact induction_Ico_add x₀ r hr base step z hz.1
      case memIco =>
        refine ⟨?lb, ?ub⟩
        case lb =>
          refine add_le_of_le_sub_left ?_
          nth_rewrite 2 [←toIcoMod_add_toIcoDiv_zsmul hr 0 (x - x₀)]
          nth_rewrite 1 [←zero_add (toIcoDiv hr 0 (x - x₀) • r)]
          gcongr
          exact left_le_toIcoMod hr 0 _
        case ub =>
          refine lt_add_of_sub_left_lt ?_
          nth_rewrite 1 [←toIcoMod_add_toIcoDiv_zsmul hr 0 (x - x₀)]
          rw [add_zsmul, one_zsmul, add_comm _ r]
          gcongr
          conv_rhs => rw [←zero_add r]
          exact toIcoMod_lt_right hr _ (x - x₀)
  termination_by induction_Ico_add x₀ r hr base step x hx => Int.natAbs (toIcoDiv hr 0 (x - x₀))


--lemma _root_.induction_Ico_add {R : Type*} [LinearOrderedField R] [FloorSemiring R] {P : R → Prop}
--    (x₀ r : R) (hr : 0 < r) (base : ∀ x ∈ Set.Ico x₀ (x₀ + r), P x)
--    (step : ∀ n : ℕ, n ≥ 1 → (∀ z ∈ Set.Ico x₀ (x₀ + r*n), P z) →
--      (∀ z ∈ Set.Ico (x₀ + r*n) (x₀ + r*(n+1)), P z)) :
--    ∀ x ≥ x₀, P x :=
--  fun x hx =>
--    if hx' : x < x₀ + r then
--      base x ⟨hx, hx'⟩
--    else by
--      push_neg at hx'
--      refine step (Nat.floor ((x - x₀)/r)) ?ge_one ?main x ?memIco
--      case ge_one =>
--        calc 1 = Nat.floor ((x₀ + r - x₀)/r) := by simp [div_self (ne_of_lt hr).symm]
--             _ ≤ _ := by gcongr
--      case main =>
--        intro z hz
--        -- Needed by termination checker
--        have _ : Nat.floor ((z - x₀)/r) < Nat.floor ((x - x₀)/r) := by
--          let xtmp := x₀ + r * ↑⌊(x - x₀) / r⌋₊
--          have hz_nonneg : 0 ≤ (z - x₀)/r := by
--            have : 0 ≤ z - x₀ := sub_nonneg.mpr hz.1
--            positivity
--          rw [Nat.floor_lt hz_nonneg]
--          calc _ < (xtmp - x₀) / r := by have := hz.2; gcongr
--               _ = _ := by simp [mul_comm r, mul_div_assoc _ r, div_self (ne_of_lt hr).symm]
--        exact induction_Ico_add x₀ r hr base step z hz.1
--      case memIco =>
--        refine ⟨?lb, ?ub⟩
--        case lb =>
--          calc _ ≤ x₀ + r * ((x - x₀)/r) := by
--                  gcongr
--                  refine Nat.floor_le ?_
--                  have : 0 ≤ x - x₀ := sub_nonneg.mpr hx
--                  positivity
--               _ ≤ _ := by rw [mul_comm r, div_mul_cancel _ (ne_of_lt hr).symm]; simp
--        case ub =>
--          calc x ≤ x₀ + r * ((x - x₀)/r) := by
--                  rw [mul_comm r, div_mul_cancel _ (ne_of_lt hr).symm]; simp
--               _ < _ := by gcongr; exact Nat.lt_floor_add_one _
--  termination_by induction_Ico_add x₀ r hr base step x hx => Nat.floor ((x-x₀)/r)

open Real in
lemma _root_.Real.induction_Ico_mul {P : ℝ → Prop} (x₀ r : ℝ) (hr : 1 < r) (hx₀ : 0 < x₀)
    (base : ∀ x ∈ Set.Ico x₀ (r * x₀), P x)
    (step : ∀ n : ℤ, n ≥ 1 → (∀ z ∈ Set.Ico x₀ (r ^ n * x₀), P z) →
      (∀ z ∈ Set.Ico (r ^ n * x₀) (r ^ (n+1) * x₀), P z)) :
    ∀ x ≥ x₀, P x := by
  have hr_nonzero : r ≠ 0 := by positivity
  have hx₀r_pos : 0 < x₀ * r := by positivity
  intro x hx
  have x_pos : 0 < x :=
    calc 0 < x₀ := hx₀
         _ ≤ x := hx
  have h₁ : P x = P (exp (log x)) := by rw [exp_log x_pos]
  rw [h₁]
  refine induction_Ico_add (P := P ∘ exp) (log x₀) (log r) (log_pos hr) ?base ?step _ (by gcongr)
  case base =>
    refine fun z hz => base (exp z) ⟨by rw [←exp_log hx₀]; exact exp_monotone hz.1, ?_⟩
    have h₂ := exp_strictMono hz.2
    rwa [←log_mul (ne_of_lt hx₀).symm hr_nonzero, exp_log hx₀r_pos, mul_comm] at h₂
  case step =>
    intro n hn hyp_ind z hz
    have h₃ : r^n ≠ 0 := zpow_ne_zero _ hr_nonzero
    have h₄ : x₀ ≠ 0 := by positivity
    have h₅ : r^(n+1) ≠ 0 := zpow_ne_zero _ hr_nonzero
    refine step n hn ?main (exp z) ?z_prop
    case main =>
      intro z hz
      have z_pos : 0 < z := calc
        0 < x₀ := hx₀
        _ ≤ z := hz.1
      rw [←exp_log z_pos]
      refine hyp_ind (log z) ⟨log_le_log' hx₀ hz.1, ?_⟩
      have h₂ := by
        refine strictMonoOn_log z_pos ?_ hz.2
        simp only [Set.mem_Ioi, gt_iff_lt]
        refine mul_pos (zpow_pos_of_pos (by positivity) _) hx₀
      rwa [log_mul h₃ h₄, log_zpow, add_comm, ←zsmul_eq_mul] at h₂
    case z_prop =>
      refine ⟨?lb, ?ub⟩
      case lb =>
        have h₂ := exp_monotone hz.1
        have hrn : r * n ≠ 0 := by positivity
        have hrn' : 0 < r ^ n := zpow_pos_of_pos (by positivity) _
        have hmulpos₁ : 0 < x₀ * r ^ n := mul_pos hx₀ hrn'
        rwa [zsmul_eq_mul, ←log_zpow, ←log_mul h₄ h₃, exp_log hmulpos₁, mul_comm] at h₂
      case ub =>
        have h₂ := exp_strictMono hz.2
        have hcast : (n + 1 : ℝ) = Int.cast (n + 1) := by simp
        have hmulpos₂ : 0 < x₀ * r ^ (n+1) := mul_pos hx₀ (zpow_pos_of_pos (by positivity) _)
        rwa [zsmul_eq_mul, ←log_zpow, ←log_mul h₄ h₅, exp_log hmulpos₂, mul_comm] at h₂

variable {f : ℝ → ℝ}

lemma eventually_atTop_nonneg_or_nonpos (hf : GrowsPolynomially f) :
    (∀ᶠ x in atTop, 0 ≤ f x) ∨ (∀ᶠ x in atTop, f x ≤ 0) := by
  obtain ⟨c₁, _, c₂, _, h⟩ := hf (1/2) (by norm_num)
  rcases lt_trichotomy c₁ c₂ with hlt|heq|hgt
  case inl =>  -- c₁ < c₂
    left
    filter_upwards [h, eventually_ge_atTop 0] with x hx hx_nonneg
    have h' : 3 / 4 * x ∈ Set.Icc (1 / 2 * x) x := by
      rw [Set.mem_Icc]
      exact ⟨by gcongr ?_ * x; norm_num, by linarith⟩
    have hu := hx (3/4 * x) h'
    have hu := Set.nonempty_of_mem hu
    rw [Set.nonempty_Icc] at hu
    have hu' : 0 ≤ (c₂ - c₁) * f x := by linarith
    exact nonneg_of_mul_nonneg_right hu' (by linarith)
  case inr.inr =>   -- c₂ < c₁
    right
    filter_upwards [h, eventually_ge_atTop 0] with x hx hx_nonneg
    have h' : 3 / 4 * x ∈ Set.Icc (1 / 2 * x) x := by
      rw [Set.mem_Icc]
      exact ⟨by gcongr ?_ * x; norm_num, by linarith⟩
    have hu := hx (3/4 * x) h'
    have hu := Set.nonempty_of_mem hu
    rw [Set.nonempty_Icc] at hu
    have hu' : (c₁ - c₂) * f x ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right hu' (by linarith)
  case inr.inl =>   -- c₁ = c₂
    have hmain : ∃ c, ∀ᶠ x in atTop, f x = c := by
      simp only [heq, Set.Icc_self, Set.mem_singleton_iff, one_mul] at h
      rw [eventually_atTop] at h
      obtain ⟨n₀, hn₀⟩ := h
      refine ⟨f (max n₀ 2), ?_⟩
      rw [eventually_atTop]
      refine ⟨max n₀ 2, ?_⟩
      refine Real.induction_Ico_mul _ 2 (by norm_num) (by positivity) ?base ?step
      case base =>
        intro x ⟨hxlb, hxub⟩
        have h₁ := calc n₀ ≤ 1 * max n₀ 2 := by simp
                        _ ≤ 2 * max n₀ 2 := by gcongr; norm_num
        have h₂ := hn₀ (2 * max n₀ 2) h₁ (max n₀ 2) ⟨by simp [-max_le_iff, hxlb], by linarith⟩
        rw [h₂]
        exact hn₀ (2 * max n₀ 2) h₁ x ⟨by simp [-max_le_iff, hxlb], le_of_lt hxub⟩
      case step =>
        intro n hn hyp_ind z hz
        have z_nonneg : 0 ≤ z := by
          calc (0:ℝ) ≤ (2:ℝ)^n * max n₀ 2 := by
                        exact mul_nonneg (zpow_nonneg (by norm_num) _) (by norm_num)
                  _ ≤ z := hz.1
        have le_2n : max n₀ 2 ≤ (2:ℝ)^n * max n₀ 2 := by
          nth_rewrite 1 [←one_mul (max n₀ 2)]
          gcongr
          exact one_le_zpow_of_nonneg (by norm_num) (by linarith)
        have n₀_le_z : n₀ ≤ z := by
          calc n₀ ≤ max n₀ 2 := by simp
                _ ≤ (2:ℝ)^n * max n₀ 2 := le_2n
                _ ≤ _ := by exact_mod_cast hz.1
        have fz_eq_c₂fz : f z = c₂ * f z := hn₀ z n₀_le_z z ⟨by linarith, le_rfl⟩
        have z_to_half_z' : f (1/2 * z) = c₂ * f z := hn₀ z n₀_le_z (1/2 * z) ⟨le_rfl, by linarith⟩
        have z_to_half_z : f (1/2 * z) = f z := by rwa [←fz_eq_c₂fz] at z_to_half_z'
        have half_z_to_base : f (1/2 * z) = f (max n₀ 2) := by
          refine hyp_ind (1/2 * z) ⟨?lb, ?ub⟩
          case lb =>
            calc max n₀ 2 ≤ ((1:ℝ)/(2:ℝ)) * (2:ℝ) ^ (1:ℤ)  * max n₀ 2 := by simp
                        _ ≤ ((1:ℝ)/(2:ℝ)) * (2:ℝ) ^ n * max n₀ 2 := by gcongr; norm_num
                        _ ≤ _ := by rw [mul_assoc]; gcongr; exact_mod_cast hz.1
          case ub =>
            have h₁ : (2:ℝ)^n = ((1:ℝ)/(2:ℝ)) * (2:ℝ)^(n+1) := by
              rw [one_div, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]
              ring
            rw [h₁, mul_assoc]
            gcongr
            exact_mod_cast hz.2
        rw [←z_to_half_z, half_z_to_base]
    obtain ⟨c, hc⟩ := hmain
    rcases le_or_lt 0 c with hpos|hneg
    case inl =>
      exact Or.inl <| by filter_upwards [hc] with _ hc; simpa only [hc]
    case inr =>
      right
      filter_upwards [hc] with x hc
      exact le_of_lt <| by simpa only [hc]

protected lemma neg {f : ℝ → ℝ} (hf : GrowsPolynomially f) : GrowsPolynomially (-f) := by
  intro b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf b hb
  refine ⟨c₂, hc₂_mem, c₁, hc₁_mem, ?_⟩
  filter_upwards [hf] with x hx
  intro u hu
  simp only [Pi.neg_apply, Set.neg_mem_Icc_iff, neg_mul_eq_mul_neg, neg_neg]
  exact hx u hu

lemma neg_iff {f : ℝ → ℝ} : GrowsPolynomially f ↔ GrowsPolynomially (-f) :=
  ⟨fun hf => hf.neg, fun hf => by rw [←neg_neg f]; exact hf.neg⟩

protected lemma abs (hf : GrowsPolynomially f) : GrowsPolynomially (fun x => |f x|) := by
  rcases eventually_atTop_nonneg_or_nonpos hf with hf'|hf'
  case inl =>
    have hmain : f =ᶠ[atTop] fun x => |f x| := by
      filter_upwards [hf'] with x hx
      rw [abs_of_nonneg hx]
    rw [←iff_eventuallyEq hmain]
    exact hf
  case inr =>
    have hmain : -f =ᶠ[atTop] fun x => |f x| := by
      filter_upwards [hf'] with x hx
      simp only [Pi.neg_apply, abs_of_nonpos hx]

    rw [←iff_eventuallyEq hmain]
    exact hf.neg

protected lemma norm (hf : GrowsPolynomially f) : GrowsPolynomially (fun x => ‖f x‖) := by
  simp only [norm_eq_abs]
  exact hf.abs

lemma eventually_atTop_le {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c ∈ Set.Ioi 0, ∀ᶠ x in atTop, ∀ u ∈ Set.Icc (b * x) x, f u ≤ c * f x := by
  obtain ⟨c₁, _, c₂, hc₂, h⟩ := hf b hb
  refine ⟨c₂, hc₂, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).2

lemma eventually_atTop_le_nat {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c ∈ Set.Ioi 0, ∀ᶠ (n:ℕ) in atTop, ∀ u ∈ Set.Icc (b * n) n, f u ≤ c * f n := by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_le hb
  exact ⟨c, hc_mem, hc.nat_cast_atTop⟩

lemma eventually_atTop_ge {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c ∈ Set.Ioi 0, ∀ᶠ x in atTop, ∀ u ∈ Set.Icc (b * x) x, c * f x ≤ f u := by
  obtain ⟨c₁, hc₁, c₂, _, h⟩ := hf b hb
  refine ⟨c₁, hc₁, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).1

lemma eventually_atTop_ge_nat {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c ∈ Set.Ioi 0, ∀ᶠ (n:ℕ) in atTop, ∀ u ∈ Set.Icc (b * n) n, c * f n ≤ f u := by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_ge hb
  exact ⟨c, hc_mem, hc.nat_cast_atTop⟩

protected lemma const {c : ℝ} : GrowsPolynomially (fun _ => c) := by
  intro b _
  refine ⟨1, by norm_num, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [] with x
  intro u _
  simp

protected lemma mul {f g : ℝ → ℝ} (hf : GrowsPolynomially f) (hg : GrowsPolynomially g) :
    GrowsPolynomially fun x => f x * g x := by
  suffices : GrowsPolynomially fun x => |f x| * |g x|
  · rcases eventually_atTop_nonneg_or_nonpos hf with hf'|hf'
    case inl =>
      rcases eventually_atTop_nonneg_or_nonpos hg with hg'|hg'
      case inl =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => |f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          rw [abs_of_nonneg hx₁, abs_of_nonneg hx₂]
        rwa [iff_eventuallyEq hmain]
      case inr =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => -|f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          simp [abs_of_nonneg hx₁, abs_of_nonpos hx₂]
        simp only [iff_eventuallyEq hmain, neg_mul]
        exact this.neg
    case inr =>
      rcases eventually_atTop_nonneg_or_nonpos hg with hg'|hg'
      case inl =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => -|f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          rw [abs_of_nonpos hx₁, abs_of_nonneg hx₂, neg_neg]
        simp only [iff_eventuallyEq hmain, neg_mul]
        exact this.neg
      case inr =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => |f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          simp [abs_of_nonpos hx₁, abs_of_nonpos hx₂]
        simp only [iff_eventuallyEq hmain, neg_mul]
        exact this
  · intro b hb
    have hf := hf.abs b hb
    have hg := hg.abs b hb
    obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf
    obtain ⟨c₃, hc₃_mem, c₄, hc₄_mem, hg⟩ := hg
    have c₁_pos : 0 < c₁ := hc₁_mem
    have c₂_pos : 0 < c₂ := hc₂_mem
    have c₃_pos : 0 < c₃ := hc₃_mem
    have c₄_pos : 0 < c₄ := hc₄_mem
    refine ⟨c₁ * c₃, by show 0 < c₁ * c₃; positivity, ?_⟩
    refine ⟨c₂ * c₄, by show 0 < c₂ * c₄; positivity, ?_⟩
    filter_upwards [hf, hg] with x hf hg
    intro u hu
    refine ⟨?lb, ?ub⟩
    case lb => calc
      c₁ * c₃ * (|f x| * |g x|) = (c₁ * |f x|) * (c₃ * |g x|) := by ring
      _ ≤ |f u| * |g u| := by
             gcongr
             · exact (hf u hu).1
             · exact (hg u hu).1
    case ub => calc
      |f u| * |g u| ≤ (c₂ * |f x|) * (c₄ * |g x|) := by
             gcongr
             · exact (hf u hu).2
             · exact (hg u hu).2
      _ = c₂ * c₄ * (|f x| * |g x|) := by ring

protected lemma const_mul {f : ℝ → ℝ} {c : ℝ} (hf : GrowsPolynomially f) :
    GrowsPolynomially fun x => c * f x :=
  GrowsPolynomially.mul GrowsPolynomially.const hf

protected lemma add {f g : ℝ → ℝ} (hf : GrowsPolynomially f) (hg : GrowsPolynomially g)
    (hf' : 0 ≤ᶠ[atTop] f) (hg' : 0 ≤ᶠ[atTop] g) : GrowsPolynomially fun x => f x + g x := by
  intro b hb
  have hf := hf b hb
  have hg := hg b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf
  obtain ⟨c₃, hc₃_mem, c₄, _, hg⟩ := hg
  have c₁_pos : 0 < c₁ := hc₁_mem
  have c₂_pos : 0 < c₂ := hc₂_mem
  have c₃_pos : 0 < c₃ := hc₃_mem
  refine ⟨min c₁ c₃, by show 0 < min c₁ c₃; positivity, ?_⟩
  refine ⟨max c₂ c₄, by show 0 < max c₂ c₄; positivity, ?_⟩
  filter_upwards [hf, hg,
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf',
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hg',
                  eventually_ge_atTop 0] with x hf hg hf' hg' hx_pos
  intro u hu
  have hbx : b * x ≤ x := calc
    b * x ≤ 1 * x := by gcongr; exact le_of_lt hb.2
        _ = x := by ring
  have fx_nonneg : 0 ≤ f x := hf' x hbx
  have gx_nonneg : 0 ≤ g x := hg' x hbx
  refine ⟨?lb, ?ub⟩
  case lb => calc
    min c₁ c₃ * (f x + g x) = min c₁ c₃ * f x + min c₁ c₃ * g x := by simp only [mul_add]
      _ ≤ c₁ * f x + c₃ * g x := by
              gcongr
              · exact min_le_left _ _
              · exact min_le_right _ _
      _ ≤ f u + g u := by
              gcongr
              · exact (hf u hu).1
              · exact (hg u hu).1
  case ub => calc
    max c₂ c₄ * (f x + g x) = max c₂ c₄ * f x + max c₂ c₄ * g x := by simp only [mul_add]
      _ ≥ c₂ * f x + c₄ * g x := by gcongr
                                    · exact le_max_left _ _
                                    · exact le_max_right _ _
      _ ≥ f u + g u := by gcongr
                          · exact (hf u hu).2
                          · exact (hg u hu).2

protected lemma inv {f : ℝ → ℝ} (hf : GrowsPolynomially f) (hf' : ∀ᶠ x in atTop, f x ≠ 0) :
    GrowsPolynomially fun x => (f x)⁻¹ := by
  suffices : GrowsPolynomially fun x => |(f x)⁻¹|
  · rcases eventually_atTop_nonneg_or_nonpos hf with hf'|hf'
    case inl =>
      have hmain : (fun x => (f x)⁻¹) =ᶠ[atTop] fun x => |(f x)⁻¹| := by
        filter_upwards [hf'] with x hx₁
        rw [abs_of_nonneg (inv_nonneg_of_nonneg hx₁)]
      rwa [iff_eventuallyEq hmain]
    case inr =>
      have hmain : (fun x => (f x)⁻¹) =ᶠ[atTop] fun x => -|(f x)⁻¹| := by
        filter_upwards [hf'] with x hx₁
        simp [abs_of_nonpos (inv_nonpos.mpr hx₁)]
      rw [iff_eventuallyEq hmain]
      exact this.neg
  simp only [abs_inv]
  have hf := hf.abs
  intro b hb
  have hb_pos := hb.1
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf b hb
  have c₁_pos : 0 < c₁ := hc₁_mem
  have c₂_pos : 0 < c₂ := hc₂_mem
  refine ⟨c₂⁻¹, by show 0 < c₂⁻¹; positivity, ?_⟩
  refine ⟨c₁⁻¹, by show 0 < c₁⁻¹; positivity, ?_⟩
  filter_upwards [hf, hf', (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf']
    with x hx hx' hx''
  intro u hu
  have h₁ : 0 < |f u| := by rw [abs_pos]; exact hx'' u hu.1
  refine ⟨?lb, ?ub⟩
  case lb =>
    rw [←mul_inv]
    gcongr
    exact (hx u hu).2
  case ub =>
    rw [←mul_inv]
    gcongr
    exact (hx u hu).1

protected lemma div {f g : ℝ → ℝ} (hf : GrowsPolynomially f) (hg : GrowsPolynomially g)
    (hg' : ∀ᶠ x in atTop, g x ≠ 0) : GrowsPolynomially fun x => f x / g x := by
  have : (fun x => f x / g x) = fun x => f x * (g x)⁻¹ := by ext; rw [div_eq_mul_inv]
  rw [this]
  exact GrowsPolynomially.mul hf (GrowsPolynomially.inv hg hg')

protected lemma rpow (p : ℝ) : GrowsPolynomially fun x => x ^ p := by
  intro b hb
  have hb₀ : 0 < b := hb.1
  have hbp₀ : 0 < b ^ p := Real.rpow_pos_of_pos hb₀ _
  obtain _ | hp := le_or_lt 0 p
  case inl =>    -- 0 ≤ p
    refine ⟨b^p, hbp₀, ?_⟩
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with x hx
    intro u hu
    refine ⟨?lb, ?ub⟩
    case lb => calc
      b ^ p * x ^ p = (b * x)^p := by rw [←Real.mul_rpow] <;> positivity
                  _ ≤ u ^ p := by gcongr; exact hu.1
    case ub =>
      rw [one_mul]
      gcongr
      · calc 0 ≤ b * x := by positivity
             _ ≤ u := hu.1
      · exact hu.2
  case inr =>   -- p < 0
    refine ⟨1, by norm_num, ?_⟩
    refine ⟨b^p, hbp₀, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with x hx
    intro u hu
    refine ⟨?lb, ?ub⟩
    case lb =>
      rw [one_mul]
      refine rpow_le_rpow_of_exponent_nonpos ?_ hu.2 (le_of_lt hp)
      calc 0 < b * x := by positivity
           _ ≤ u := hu.1
    case ub => calc
      u ^ p ≤ (b * x) ^ p := by
              exact rpow_le_rpow_of_exponent_nonpos (by positivity) hu.1 (le_of_lt hp)
          _ = b ^ p * x ^ p := by rw [Real.mul_rpow] <;> positivity

protected lemma log : GrowsPolynomially Real.log := by
  intro b hb
  have hb₀ : 0 < b := hb.1
  refine ⟨1 / 2, by norm_num, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  have h_tendsto : Tendsto (fun x => 1 / 2 * Real.log x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1,
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop
                    <| h_tendsto.eventually (eventually_gt_atTop (-Real.log b)) ] with x hx_pos hx
  intro u hu
  refine ⟨?lb, ?ub⟩
  case lb => calc
    1 / 2 * Real.log x = Real.log x + (-1 / 2) * Real.log x := by ring
      _ ≤ Real.log x + Real.log b := by
              gcongr
              rw [neg_div, neg_mul, ←neg_le]
              refine le_of_lt (hx x ?_)
              calc b * x ≤ 1 * x := by gcongr; exact le_of_lt hb.2
                       _ = x := by rw [one_mul]
      _ = Real.log (b * x) := by rw [←Real.log_mul (by positivity) (by positivity), mul_comm]
      _ ≤ Real.log u := by gcongr; exact hu.1
  case ub =>
    rw [one_mul]
    gcongr
    · calc 0 < b * x := by positivity
         _ ≤ u := by exact hu.1
    · exact hu.2

protected lemma id : GrowsPolynomially (fun x => x) := by
  intro b hb
  refine ⟨b, hb.1, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  refine eventually_of_forall fun x u hu => ?_
  simp only [one_mul, ge_iff_le, gt_iff_lt, not_le, Set.mem_Icc]
  exact ⟨hu.1, hu.2⟩

lemma of_isTheta {f g : ℝ → ℝ} (hg : GrowsPolynomially g) (hf : f =Θ[atTop] g)
    (hf' : ∀ᶠ x in atTop, 0 ≤ f x) : GrowsPolynomially f := by
  intro b hb
  have hb_pos := hb.1
  have hf_lb := isBigO_iff''.mp hf.isBigO_symm
  have hf_ub := isBigO_iff'.mp hf.isBigO
  obtain ⟨c₁, hc₁_pos : 0 < c₁, hf_lb⟩ := hf_lb
  obtain ⟨c₂, hc₂_pos : 0 < c₂, hf_ub⟩ := hf_ub
  have hg := hg.norm b hb
  obtain ⟨c₃, hc₃_pos : 0 < c₃, hg⟩ := hg
  obtain ⟨c₄, hc₄_pos : 0 < c₄, hg⟩ := hg
  have h_lb_pos : 0 < c₁ * c₂⁻¹ * c₃ := by positivity
  have h_ub_pos : 0 < c₂ * c₄ * c₁⁻¹ := by positivity
  refine ⟨c₁ * c₂⁻¹ * c₃, h_lb_pos, ?_⟩
  refine ⟨c₂ * c₄ * c₁⁻¹, h_ub_pos, ?_⟩
  have c₂_cancel : c₂⁻¹ * c₂ = 1 := inv_mul_cancel (by positivity)
  have c₁_cancel : c₁⁻¹ * c₁ = 1 := inv_mul_cancel (by positivity)
  filter_upwards [(tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf',
                  (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf_lb,
                  (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf_ub,
                  (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hg,
                  eventually_ge_atTop 0]
    with x hf_pos h_lb h_ub hg_bound hx_pos
  intro u hu
  have hbx : b * x ≤ x :=
    calc b * x ≤ 1 * x    := by gcongr; exact le_of_lt hb.2
             _ = x        := by rw [one_mul]
  have hg_bound := hg_bound x hbx
  refine ⟨?lb, ?ub⟩
  case lb => calc
    c₁ * c₂⁻¹ * c₃ * f x ≤ c₁ * c₂⁻¹ * c₃ * (c₂ * ‖g x‖) := by
          rw [←Real.norm_of_nonneg (hf_pos x hbx)]; gcongr; exact h_ub x hbx
      _ = (c₂⁻¹ * c₂) * c₁ * (c₃ * ‖g x‖) := by ring
      _ = c₁ * (c₃ * ‖g x‖) := by simp [c₂_cancel]
      _ ≤ c₁ * ‖g u‖ := by gcongr; exact (hg_bound u hu).1
      _ ≤ f u := by
          rw [←Real.norm_of_nonneg (hf_pos u hu.1)]
          exact h_lb u hu.1
  case ub => calc
    f u ≤ c₂ * ‖g u‖ := by rw [←Real.norm_of_nonneg (hf_pos u hu.1)]; exact h_ub u hu.1
      _ ≤ c₂ * (c₄ * ‖g x‖) := by gcongr; exact (hg_bound u hu).2
      _ = c₂ * c₄ * (c₁⁻¹ * c₁) * ‖g x‖ := by simp [c₁_cancel]; ring
      _ = c₂ * c₄ * c₁⁻¹ * (c₁ * ‖g x‖) := by ring
      _ ≤ c₂ * c₄ * c₁⁻¹ * f x := by
                gcongr
                rw [←Real.norm_of_nonneg (hf_pos x hbx)]
                exact h_lb x hbx

lemma of_isEquivalent {f g : ℝ → ℝ}
    (hg : GrowsPolynomially g) (hf : f ~[atTop] g) (hf' : ∀ᶠ x in atTop, 0 ≤ f x) :
    GrowsPolynomially f :=
  of_isTheta hg hf.isTheta hf'

lemma of_isEquivalent_const {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hf : f ~[atTop] fun _ => c) :
    GrowsPolynomially f :=
  of_isEquivalent GrowsPolynomially.const hf (hf.tendsto_const.eventually (eventually_ge_nhds hc))

end GrowsPolynomially
end AkraBazziRecurrence
