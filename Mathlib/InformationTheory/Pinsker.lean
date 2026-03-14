/-
Copyright (c) 2026 Wei Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Lin
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Data.Fintype.Basic

/-!
# Pinsker's inequality for finite distributions

We prove Pinsker's inequality `2 * tvDistFin p q ^ 2 ≤ klDivFin p q` for finite probability
distributions `p q : X → ℝ` over a finite type `X`.

## Main definitions

* `klDivFin p q`: KL divergence for functions `p q : X → ℝ` on a finite type, defined as
  `∑ x, p x * log (p x / q x)`.
* `tvDistFin p q`: Total variation distance, defined as `(∑ x, |p x - q x|) / 2`.
* `binaryKL a b`: Binary KL divergence `a * log (a / b) + (1 - a) * log ((1 - a) / (1 - b))`.

## Main results

* `binaryKL_self`: `binaryKL a a = 0` for `a ∈ (0, 1)`.
* `two_mul_sq_le_binaryKL`: Binary Pinsker inequality `2 * (a - b) ^ 2 ≤ binaryKL a b`.
* `klDivFin_nonneg`: Gibbs' inequality (KL divergence is nonneg for probability distributions).
* `binaryKL_le_klDivFin`: Data processing inequality: `binaryKL (p(A)) (q(A)) ≤ klDivFin p q`.
* `pinsker_inequality`: Full Pinsker's inequality `2 * tvDistFin p q ^ 2 ≤ klDivFin p q`.
* `tvDistFin_le_one`: Total variation distance is at most 1.

## Proof strategy

The proof follows the standard route:
1. **Binary Pinsker** via the second derivative test: define `h(x) = binaryKL(x, b) - 2(x-b)²`,
   show `h'' ≥ 0` (by AM-GM), `h(b) = 0`, `h'(b) = 0`, hence `h ≥ 0`.
2. **Data processing inequality** via the log-sum inequality (proved from Gibbs' inequality on
   conditional distributions).
3. **Full Pinsker** by choosing the optimal partition `A = {x | q x ≤ p x}` and composing
   binary Pinsker with data processing.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][cover2006], Chapter 11.
* [Y. Polyanskiy, Y. Wu, *Information Theory: From Coding to Learning*][polyanskiy2024],
  Theorem 7.15.

## Implementation notes

These definitions use `X → ℝ` for probability distributions rather than `Measure`-based types.
The measure-theoretic KL divergence is defined separately in
`Mathlib.InformationTheory.KullbackLeibler.Basic` as `klDiv μ ν : ℝ≥0∞`.
The finite-space versions here are self-contained and avoid the `ℝ≥0∞` type conversion overhead.

-/

@[expose] public section

noncomputable section

open Real Finset BigOperators

namespace InformationTheory

variable {X : Type*}

/-! ### Definitions -/

/-- KL divergence for functions on a finite type.
`klDivFin p q = ∑ x, p x * log (p x / q x)`. -/
def klDivFin [Fintype X] (p q : X → ℝ) : ℝ :=
  ∑ x : X, p x * log (p x / q x)

/-- Total variation distance for functions on a finite type.
`tvDistFin p q = (∑ x, |p x - q x|) / 2`. -/
def tvDistFin [Fintype X] (p q : X → ℝ) : ℝ :=
  (∑ x : X, |p x - q x|) / 2

/-- Binary KL divergence.
`binaryKL a b = a * log (a / b) + (1 - a) * log ((1 - a) / (1 - b))`. -/
def binaryKL (a b : ℝ) : ℝ :=
  a * log (a / b) + (1 - a) * log ((1 - a) / (1 - b))

/-! ### Basic properties -/

/-- Binary KL divergence of equal arguments is zero. -/
@[simp]
theorem binaryKL_self (a : ℝ) (ha : 0 < a) (ha1 : a < 1) : binaryKL a a = 0 := by
  unfold binaryKL
  simp [div_self (ne_of_gt ha), div_self (ne_of_gt (show 0 < 1 - a by linarith)), log_one]

/-! ### Binary Pinsker inequality

The core technical result. We define `h(x) = binaryKL(x, b) - 2(x - b)²` and show `h ≥ 0`
by the second derivative test:
- `h''(x) = x⁻¹ + (1-x)⁻¹ - 4 ≥ 0` (by AM-GM: `x(1-x) ≤ 1/4`)
- `h(b) = 0` and `h'(b) = 0`
- `h'' ≥ 0` implies `h'` is monotone, combined with `h'(b) = 0` gives sign information,
  which in turn implies `h` is monotone/antitone on each side of `b`.
-/

/-- Rewrite binaryKL by splitting `log(a/b) = log a - log b`, eliminating division
for differentiation. -/
private lemma binaryKL_rewrite {a b : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) :
    binaryKL a b = (a * log a + (1 - a) * log (1 - a)) -
      (a * log b + (1 - a) * log (1 - b)) := by
  unfold binaryKL
  rw [log_div (ne_of_gt ha) (ne_of_gt hb),
      log_div (ne_of_gt (show 0 < 1 - a by linarith)) (ne_of_gt (show 0 < 1 - b by linarith))]
  ring

/-- The second derivative `x⁻¹ + (1-x)⁻¹ - 4` is nonneg on `(0, 1)`,
since `x(1-x) ≤ 1/4` by AM-GM. -/
private lemma pinskerAux_deriv2_nonneg {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    0 ≤ a⁻¹ + (1 - a)⁻¹ - 4 := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hprod : a * (1 - a) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * a - 1)]
  have hprod_pos : 0 < a * (1 - a) := mul_pos ha h1a
  rw [show a⁻¹ + (1 - a)⁻¹ - 4 = (1 - 4 * (a * (1 - a))) / (a * (1 - a)) from by
    field_simp; ring]
  exact div_nonneg (by linarith) (le_of_lt hprod_pos)

/-- First derivative of `h(x) = binaryKL(x, b) - 2(x - b)²` is
`log a - log(1 - a) - log b + log(1 - b) - 4(a - b)`. Composed from 5 sub-derivatives. -/
private lemma hasDerivAt_binaryKL_minus_sq {a b : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) :
    HasDerivAt (fun x => binaryKL x b - 2 * (x - b) ^ 2)
      (log a - log (1 - a) - log b + log (1 - b) - 4 * (a - b)) a := by
  have h1a_pos : (0 : ℝ) < 1 - a := by linarith
  have h1b_pos : (0 : ℝ) < 1 - b := by linarith
  -- d/dx[x * log x] = log a + 1
  have hd1 : HasDerivAt (fun x => x * log x) (log a + 1) a :=
    hasDerivAt_mul_log (ne_of_gt ha)
  -- d/dx[(1-x) * log(1-x)] = -(log(1-a) + 1) via chain rule
  have hd2 : HasDerivAt (fun x => (1 - x) * log (1 - x)) (-(log (1 - a) + 1)) a := by
    have hd_outer : HasDerivAt (fun u => u * log u) (log (1 - a) + 1) (1 - a) :=
      hasDerivAt_mul_log (ne_of_gt h1a_pos)
    have hd_inner : HasDerivAt (fun x => 1 - x) (-1) a := by
      convert (hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a) using 1; simp
    convert hd_outer.comp a hd_inner using 1; ring
  -- d/dx[x * log b] = log b
  have hd3 : HasDerivAt (fun x => x * log b) (log b) a := by
    convert (hasDerivAt_id a).mul_const (log b) using 1; simp
  -- d/dx[(1-x) * log(1-b)] = -log(1-b)
  have hd4 : HasDerivAt (fun x => (1 - x) * log (1 - b)) (-log (1 - b)) a := by
    have : HasDerivAt (fun x => 1 - x) (-1) a := by
      convert (hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a) using 1; simp
    convert this.mul_const (log (1 - b)) using 1; ring
  -- d/dx[2*(x-b)²] = 4*(a-b)
  have hd5 : HasDerivAt (fun x => 2 * (x - b) ^ 2) (4 * (a - b)) a := by
    have h_sub : HasDerivAt (fun x => x - b) 1 a := by
      convert (hasDerivAt_id a).sub (hasDerivAt_const a b) using 1; simp
    have h_sq : HasDerivAt (fun x => (x - b) ^ 2) (2 * (a - b)) a := by
      convert h_sub.pow 2 using 1
      simp [pow_succ, pow_zero, Nat.cast_ofNat, mul_comm]
    convert (h_sq.const_mul (2 : ℝ)) using 1; ring
  -- Rewrite binaryKL into differentiable form
  have hrew : ∀ x, binaryKL x b = (x * log x + (1 - x) * log (1 - x)) -
      (x * log b + (1 - x) * log (1 - b)) := by
    intro x; unfold binaryKL
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hx1 : 1 - x = 0
      · simp [show x = 1 from by linarith, sub_self]
      · rw [log_div hx (ne_of_gt hb), log_div hx1 (ne_of_gt h1b_pos)]; ring
  simp_rw [hrew]
  -- Compose all sub-derivatives
  have h_sum := ((hd1.add hd2).sub (hd3.add hd4)).sub hd5
  convert h_sum using 1; ring

/-- Second derivative chain: the derivative of
`t ↦ log t - log(1 - t) - log b + log(1 - b) - 4(t - b)` is `x⁻¹ + (1 - x)⁻¹ - 4`. -/
private lemma hasDerivAt_pinskerAux_deriv {x b : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (_hb : 0 < b) (_hb1 : b < 1) :
    HasDerivAt (fun t => log t - log (1 - t) - log b + log (1 - b) - 4 * (t - b))
      (x⁻¹ + (1 - x)⁻¹ - 4) x := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have hd1 : HasDerivAt log x⁻¹ x := hasDerivAt_log (ne_of_gt hx)
  -- d/dx[-log(1-x)] = (1-x)⁻¹ via chain rule
  have hd2 : HasDerivAt (fun t => -log (1 - t)) ((1 - x)⁻¹) x := by
    have hd_inner : HasDerivAt (fun t => 1 - t) (-1) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1; simp
    have hd_log := hd_inner.log (ne_of_gt h1x)
    have hd_neg : HasDerivAt (fun t => -log (1 - t)) (-(-1 / (1 - x))) x := hd_log.neg
    convert hd_neg using 1; field_simp
  -- d/dx[-4*(x-b)] = -4
  have hd3 : HasDerivAt (fun t => -4 * (t - b)) (-4) x := by
    have := ((hasDerivAt_id x).sub (hasDerivAt_const x b)).const_mul (-4 : ℝ)
    convert this using 1; simp
  have hd4 : HasDerivAt (fun _ : ℝ => -log b + log (1 - b)) 0 x := hasDerivAt_const x _
  have h_sum := ((hd1.add hd2).add hd3).add hd4
  convert h_sum using 1
  · ext t; simp [Pi.add_apply]; ring
  · ring

/-- Core lemma: `binaryKL a b - 2 * (a - b) ^ 2 ≥ 0`.
Proved via the second derivative test: `h'' ≥ 0` implies `h'` is monotone, combined with
`h(b) = 0` and `h'(b) = 0`, gives `h ≥ 0` on both sides of `b`. -/
private lemma pinskerAux_nonneg {a b : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) :
    0 ≤ binaryKL a b - 2 * (a - b) ^ 2 := by
  by_cases hab : a = b
  · rw [hab, binaryKL_self b hb hb1]; norm_num
  set h : ℝ → ℝ := fun x => binaryKL x b - 2 * (x - b) ^ 2
  set h' : ℝ → ℝ := fun x => log x - log (1 - x) - log b + log (1 - b) - 4 * (x - b)
  set h'' : ℝ → ℝ := fun x => x⁻¹ + (1 - x)⁻¹ - 4
  have hb_val : h b = 0 := by simp only [h]; rw [binaryKL_self b hb hb1]; norm_num
  have hb'_val : h' b = 0 := by simp only [h']; ring
  have hH : ∀ x, 0 < x → x < 1 → HasDerivAt h (h' x) x :=
    fun x hx hx1 => hasDerivAt_binaryKL_minus_sq hx hx1 hb hb1
  have hH' : ∀ x, 0 < x → x < 1 → HasDerivAt h' (h'' x) x :=
    fun x hx hx1 => hasDerivAt_pinskerAux_deriv hx hx1 hb hb1
  have hH''_nonneg : ∀ x, 0 < x → x < 1 → 0 ≤ h'' x :=
    fun x hx hx1 => pinskerAux_deriv2_nonneg hx hx1
  rcases lt_trichotomy a b with hab_lt | hab_eq | hab_gt
  · -- Case a < b: h' monotone on [a,b], h'(b) = 0 → h' ≤ 0 → h antitone → h(a) ≥ h(b) = 0
    have h'_mono : MonotoneOn h' (Set.Icc a b) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
        (fun x hx => (hH' x (by linarith [hx.1])
          (by linarith [hx.2])).continuousAt.continuousWithinAt)
        (fun x hx => by
          have hx_mem : x ∈ Set.Ioo a b := interior_Icc (a := a) (b := b) ▸ hx
          exact (hH' x (by linarith [hx_mem.1]) (by linarith [hx_mem.2])).hasDerivWithinAt)
        (fun x hx => by
          have hx_mem : x ∈ Set.Ioo a b := interior_Icc (a := a) (b := b) ▸ hx
          exact hH''_nonneg x (by linarith [hx_mem.1]) (by linarith [hx_mem.2]))
    have h_anti : AntitoneOn h (Set.Icc a b) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
        (fun x hx => (hH x (by linarith [hx.1])
          (by linarith [hx.2])).continuousAt.continuousWithinAt)
        (fun x hx => by
          have hx_mem : x ∈ Set.Ioo a b := interior_Icc (a := a) (b := b) ▸ hx
          exact (hH x (by linarith [hx_mem.1]) (by linarith [hx_mem.2])).hasDerivWithinAt)
        (fun x hx => by
          have hx_mem : x ∈ Set.Ioo a b := interior_Icc (a := a) (b := b) ▸ hx
          have hx_le_b : x ≤ b := le_of_lt hx_mem.2
          have : h' x ≤ h' b := h'_mono (Set.mem_Icc.mpr ⟨le_of_lt hx_mem.1, hx_le_b⟩)
            (Set.mem_Icc.mpr ⟨le_of_lt hab_lt, le_refl b⟩) hx_le_b
          linarith [hb'_val])
    have := h_anti (Set.mem_Icc.mpr ⟨le_refl a, le_of_lt hab_lt⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt hab_lt, le_refl b⟩) (le_of_lt hab_lt)
    linarith [hb_val]
  · exact absurd hab_eq hab
  · -- Case b < a: h' monotone on [b,a], h'(b) = 0 → h' ≥ 0 → h monotone → h(a) ≥ h(b) = 0
    have h'_mono : MonotoneOn h' (Set.Icc b a) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc b a)
        (fun x hx => (hH' x (by linarith [hx.1])
          (by linarith [hx.2])).continuousAt.continuousWithinAt)
        (fun x hx => by
          have hx_mem : x ∈ Set.Ioo b a := interior_Icc (a := b) (b := a) ▸ hx
          exact (hH' x (by linarith [hx_mem.1]) (by linarith [hx_mem.2])).hasDerivWithinAt)
        (fun x hx => by
          have hx_mem : x ∈ Set.Ioo b a := interior_Icc (a := b) (b := a) ▸ hx
          exact hH''_nonneg x (by linarith [hx_mem.1]) (by linarith [hx_mem.2]))
    have h_mono : MonotoneOn h (Set.Icc b a) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc b a)
        (fun x hx => (hH x (by linarith [hx.1])
          (by linarith [hx.2])).continuousAt.continuousWithinAt)
        (fun x hx => by
          have hx_mem : x ∈ Set.Ioo b a := interior_Icc (a := b) (b := a) ▸ hx
          exact (hH x (by linarith [hx_mem.1]) (by linarith [hx_mem.2])).hasDerivWithinAt)
        (fun x hx => by
          have hx_mem : x ∈ Set.Ioo b a := interior_Icc (a := b) (b := a) ▸ hx
          have hb_le_x : b ≤ x := le_of_lt hx_mem.1
          have : h' b ≤ h' x := h'_mono (Set.mem_Icc.mpr ⟨le_refl b, le_of_lt hab_gt⟩)
            (Set.mem_Icc.mpr ⟨hb_le_x, le_of_lt hx_mem.2⟩) hb_le_x
          linarith [hb'_val])
    have := h_mono (Set.mem_Icc.mpr ⟨le_refl b, le_of_lt hab_gt⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt hab_gt, le_refl a⟩) (le_of_lt hab_gt)
    linarith [hb_val]

/-- **Binary Pinsker inequality**: `2 * (a - b) ^ 2 ≤ binaryKL a b` for `a, b ∈ (0, 1)`. -/
theorem two_mul_sq_le_binaryKL
    {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binaryKL a b := by
  linarith [pinskerAux_nonneg ha ha1 hb hb1]

/-! ### KL divergence non-negativity (Gibbs' inequality) -/

/-- Auxiliary: `log x ≤ x - 1` for positive `x`. This is a direct consequence of the
concavity of `log`. -/
private theorem log_le_sub_one {x : ℝ} (hx : 0 < x) : log x ≤ x - 1 := by
  linarith [add_one_le_exp (log x), exp_log hx]

/-- Auxiliary: `1 - 1/x ≤ log x` for positive `x`, the reverse direction of `log x ≤ x - 1`
applied to `1/x`. -/
private theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - 1 / x ≤ log x := by
  have h1 : log (1 / x) ≤ 1 / x - 1 := log_le_sub_one (div_pos one_pos hx)
  rw [log_div one_ne_zero (ne_of_gt hx), log_one, zero_sub] at h1; linarith

/-- **Gibbs' inequality**: KL divergence is nonnegative for probability distributions. -/
theorem klDivFin_nonneg [Fintype X] (p q : X → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hq_pos : ∀ x, 0 < q x)
    (hp_sum : ∑ x : X, p x = 1) (hq_sum : ∑ x : X, q x = 1) :
    0 ≤ klDivFin p q := by
  unfold klDivFin
  suffices h : ∑ x : X, (p x - q x) ≤ ∑ x : X, p x * log (p x / q x) by
    have hsub : ∑ x : X, (p x - q x) = 0 := by
      simp only [Finset.sum_sub_distrib, hp_sum, hq_sum, sub_self]
    linarith
  apply Finset.sum_le_sum; intro x _
  by_cases hpx : p x = 0
  · simp [hpx]; linarith [hq_pos x]
  · have hpx_pos : 0 < p x := lt_of_le_of_ne (hp_nonneg x) (Ne.symm hpx)
    have h1 := log_le_sub_one (div_pos (hq_pos x) hpx_pos)
    have h2 : log (q x / p x) = -log (p x / q x) := by
      rw [log_div (ne_of_gt (hq_pos x)) (ne_of_gt hpx_pos),
          log_div (ne_of_gt hpx_pos) (ne_of_gt (hq_pos x))]; ring
    have h3 : 1 - q x / p x ≤ log (p x / q x) := by linarith [h2 ▸ h1]
    have h4 := mul_le_mul_of_nonneg_left h3 (le_of_lt hpx_pos)
    have h5 : p x * (1 - q x / p x) = p x - q x := by field_simp
    linarith [h4, h5]

/-! ### Data processing inequality -/

/-- **Data processing inequality**: `binaryKL (∑ x ∈ A, p x) (∑ x ∈ A, q x) ≤ klDivFin p q`
for any nonempty subset `A` with nonempty complement. This is proved via the log-sum inequality
(Gibbs' inequality applied to conditional distributions). -/
theorem binaryKL_le_klDivFin [Fintype X] [DecidableEq X]
    (p q : X → ℝ) (hp_pos : ∀ x, 0 < p x) (hq_pos : ∀ x, 0 < q x)
    (hp_sum : ∑ x : X, p x = 1) (hq_sum : ∑ x : X, q x = 1)
    (A : Finset X) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    binaryKL (∑ x ∈ A, p x) (∑ x ∈ A, q x) ≤ klDivFin p q := by
  set P_A := ∑ x ∈ A, p x
  set Q_A := ∑ x ∈ A, q x
  set P_Ac := ∑ x ∈ Aᶜ, p x
  set Q_Ac := ∑ x ∈ Aᶜ, q x
  -- Split KL over A and Aᶜ
  have hkl_split : klDivFin p q = (∑ x ∈ A, p x * log (p x / q x)) +
      (∑ x ∈ Aᶜ, p x * log (p x / q x)) := by
    unfold klDivFin
    linarith [Finset.sum_compl_add_sum A (fun x => p x * log (p x / q x))]
  have hPA_pos : 0 < P_A := Finset.sum_pos (fun x _ => hp_pos x) hA
  have hQA_pos : 0 < Q_A := Finset.sum_pos (fun x _ => hq_pos x) hA
  have hPAc_pos : 0 < P_Ac := Finset.sum_pos (fun x _ => hp_pos x) hAc
  have hQAc_pos : 0 < Q_Ac := Finset.sum_pos (fun x _ => hq_pos x) hAc
  have hP_total : P_A + P_Ac = 1 := by
    linarith [Finset.sum_compl_add_sum A p]
  have hQ_total : Q_A + Q_Ac = 1 := by
    linarith [Finset.sum_compl_add_sum A q]
  -- Log-sum inequality: ∑_S p log(p/q) ≥ (∑_S p) log((∑_S p)/(∑_S q))
  suffices h_ls : ∀ (S : Finset X), S.Nonempty → (hPS : 0 < ∑ x ∈ S, p x) →
      (hQS : 0 < ∑ x ∈ S, q x) →
      (∑ x ∈ S, p x) * log ((∑ x ∈ S, p x) / (∑ x ∈ S, q x)) ≤
        ∑ x ∈ S, p x * log (p x / q x) by
    have h_A := h_ls A hA hPA_pos hQA_pos
    have h_Ac := h_ls Aᶜ hAc hPAc_pos hQAc_pos
    unfold binaryKL
    have hPAc_eq : 1 - P_A = P_Ac := by linarith
    have hQAc_eq : 1 - Q_A = Q_Ac := by linarith
    rw [hPAc_eq, hQAc_eq]
    linarith
  -- Prove log-sum via Gibbs on conditional distributions
  intro S hS hPS hQS
  suffices h_gibbs :
      0 ≤ ∑ x ∈ S, p x * log (p x * (∑ y ∈ S, q y) / (q x * (∑ y ∈ S, p y))) by
    have h_rewrite : ∀ x ∈ S,
        p x * log (p x / q x) =
          p x * log (p x * (∑ y ∈ S, q y) / (q x * (∑ y ∈ S, p y))) +
          p x * log ((∑ y ∈ S, p y) / (∑ y ∈ S, q y)) := by
      intro x _
      rw [← mul_add, ← log_mul
          (ne_of_gt (div_pos (mul_pos (hp_pos x) hQS) (mul_pos (hq_pos x) hPS)))
          (ne_of_gt (div_pos hPS hQS))]
      congr 1; field_simp
    rw [Finset.sum_congr rfl h_rewrite, Finset.sum_add_distrib]
    have h_factor : ∑ x ∈ S, p x * log ((∑ y ∈ S, p y) / (∑ y ∈ S, q y)) =
        (∑ x ∈ S, p x) * log ((∑ y ∈ S, p y) / (∑ y ∈ S, q y)) := by
      rw [← Finset.sum_mul]
    linarith
  -- Termwise bound: p·log(pQ_S/(qP_S)) ≥ p - q·P_S/Q_S via log x ≥ 1 - 1/x
  have h_lb : ∀ x ∈ S, p x - q x * (∑ y ∈ S, p y) / (∑ y ∈ S, q y) ≤
      p x * log (p x * (∑ y ∈ S, q y) / (q x * (∑ y ∈ S, p y))) := by
    intro x _
    have hpx := hp_pos x; have hqx := hq_pos x
    have hr : 0 < p x * (∑ y ∈ S, q y) / (q x * (∑ y ∈ S, p y)) :=
      div_pos (mul_pos hpx hQS) (mul_pos hqx hPS)
    have h1 := one_sub_inv_le_log hr
    have h2 : 1 / (p x * (∑ y ∈ S, q y) / (q x * (∑ y ∈ S, p y))) =
        q x * (∑ y ∈ S, p y) / (p x * (∑ y ∈ S, q y)) := by field_simp
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hpx.le
    have h4 : p x * (1 - q x * (∑ y ∈ S, p y) / (p x * (∑ y ∈ S, q y))) =
        p x - q x * (∑ y ∈ S, p y) / (∑ y ∈ S, q y) := by field_simp
    linarith
  have h_sum_lb := Finset.sum_le_sum h_lb
  -- The lower bound sums to zero: ∑(p - q·P_S/Q_S) = P_S - Q_S·P_S/Q_S = 0
  have h_sum_zero :
      ∑ x ∈ S, (p x - q x * (∑ y ∈ S, p y) / (∑ y ∈ S, q y)) = 0 := by
    have hQS_ne : (∑ y ∈ S, q y) ≠ 0 := ne_of_gt hQS
    have h_rw : ∑ x ∈ S, (p x - q x * (∑ y ∈ S, p y) / (∑ y ∈ S, q y)) =
        ∑ x ∈ S, p x - (∑ x ∈ S, q x) * ((∑ y ∈ S, p y) / (∑ y ∈ S, q y)) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      have : ∀ x ∈ S, q x * (∑ y ∈ S, p y) / (∑ y ∈ S, q y) =
          q x * ((∑ y ∈ S, p y) / (∑ y ∈ S, q y)) := fun x _ => by rw [mul_div_assoc]
      rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
    rw [h_rw, mul_div_cancel₀ _ hQS_ne, sub_self]
  linarith

/-! ### Full Pinsker inequality -/

/-- **Pinsker's inequality**: `2 * tvDistFin p q ^ 2 ≤ klDivFin p q` for probability
distributions with strictly positive masses on a finite type with at least 2 elements. -/
theorem pinsker_inequality [Fintype X] [DecidableEq X]
    (p q : X → ℝ) (hp_pos : ∀ x, 0 < p x) (hq_pos : ∀ x, 0 < q x)
    (hp_sum : ∑ x : X, p x = 1) (hq_sum : ∑ x : X, q x = 1)
    (hcard : 2 ≤ Fintype.card X) :
    2 * tvDistFin p q ^ 2 ≤ klDivFin p q := by
  set A := Finset.univ.filter (fun x => q x ≤ p x) with hA_def
  by_cases hA_full : A = Finset.univ
  · -- p ≥ q everywhere implies p = q, so TV = 0
    have hge : ∀ x, q x ≤ p x := by
      intro x; have := hA_full ▸ Finset.mem_univ x; exact (Finset.mem_filter.mp this).2
    have hpq : ∀ x, p x = q x := by
      intro x; by_contra h_ne
      have hlt : q x < p x := lt_of_le_of_ne (hge x) (Ne.symm h_ne)
      linarith [Finset.sum_lt_sum (fun y _ => hge y) ⟨x, Finset.mem_univ _, hlt⟩,
        hp_sum, hq_sum]
    have hTV : tvDistFin p q = 0 := by
      unfold tvDistFin
      simp [show ∀ x, |p x - q x| = 0 from fun x => by rw [hpq x, sub_self, abs_zero]]
    rw [hTV];
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, ge_iff_le]
    exact klDivFin_nonneg p q (fun x => (hp_pos x).le) hq_pos hp_sum hq_sum
  · -- A and Aᶜ are both nonempty
    have hA_nempty : A.Nonempty := by
      by_contra h_empty; rw [Finset.not_nonempty_iff_eq_empty] at h_empty
      have hplt : ∀ x, p x < q x := by
        intro x; by_contra h; push_neg at h
        exact absurd (h_empty ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩ :
          x ∈ (∅ : Finset X)) (by simp)
      linarith [Finset.sum_lt_sum (fun x _ => (hplt x).le)
        ⟨(Fintype.card_pos_iff.mp (by linarith : 0 < Fintype.card X)).some,
         Finset.mem_univ _, hplt _⟩, hp_sum, hq_sum]
    have hAc_nempty : Aᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.compl_eq_empty_iff]; exact hA_full
    -- Apply data processing + binary Pinsker
    have h_dp := binaryKL_le_klDivFin p q hp_pos hq_pos hp_sum hq_sum A hA_nempty hAc_nempty
    have hPAc_pos : 0 < ∑ x ∈ Aᶜ, p x := Finset.sum_pos (fun x _ => hp_pos x) hAc_nempty
    have hPA_lt1 : ∑ x ∈ A, p x < 1 := by
      linarith [Finset.sum_compl_add_sum A p]
    have hQAc_pos : 0 < ∑ x ∈ Aᶜ, q x := Finset.sum_pos (fun x _ => hq_pos x) hAc_nempty
    have hQA_lt1 : ∑ x ∈ A, q x < 1 := by
      linarith [Finset.sum_compl_add_sum A q]
    have h_bp := two_mul_sq_le_binaryKL
      (Finset.sum_pos (fun x _ => hp_pos x) hA_nempty) hPA_lt1
      (Finset.sum_pos (fun x _ => hq_pos x) hA_nempty) hQA_lt1
    -- Show TV = p(A) - q(A) via the optimal partition
    have hTV_eq : tvDistFin p q = ∑ x ∈ A, p x - ∑ x ∈ A, q x := by
      unfold tvDistFin
      have h_abs_A : ∀ x ∈ A, |p x - q x| = p x - q x := by
        intro x hx; exact abs_of_nonneg (by linarith [(Finset.mem_filter.mp hx).2])
      have h_abs_Ac : ∀ x ∈ Aᶜ, |p x - q x| = q x - p x := by
        intro x hx
        have hle : p x - q x ≤ 0 := by
          have hx' : ¬ (q x ≤ p x) := by
            intro h_mem
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h_mem⟩)
              (Finset.mem_compl.mp hx)
          push_neg at hx'; linarith
        rw [abs_of_nonpos hle]; ring
      rw [show ∑ x : X, |p x - q x| =
          ∑ x ∈ A, |p x - q x| + ∑ x ∈ Aᶜ, |p x - q x| from by
            linarith [Finset.sum_compl_add_sum A (fun x => |p x - q x|)],
        Finset.sum_congr rfl h_abs_A, Finset.sum_congr rfl h_abs_Ac]
      have h1 : (∑ x ∈ A, p x) + (∑ x ∈ Aᶜ, p x) = 1 := by
        linarith [Finset.sum_compl_add_sum A p]
      have h2 : (∑ x ∈ A, q x) + (∑ x ∈ Aᶜ, q x) = 1 := by
        linarith [Finset.sum_compl_add_sum A q]
      have h3 : ∑ x ∈ A, (p x - q x) = (∑ x ∈ A, p x) - (∑ x ∈ A, q x) := by
        simp only [Finset.sum_sub_distrib]
      have h4 : ∑ x ∈ Aᶜ, (q x - p x) = (∑ x ∈ Aᶜ, q x) - (∑ x ∈ Aᶜ, p x) := by
        simp only [Finset.sum_sub_distrib]
      have h_balance : ∑ x ∈ A, (p x - q x) = ∑ x ∈ Aᶜ, (q x - p x) := by linarith
      linarith [h_balance]
    rw [hTV_eq]; linarith [h_dp, h_bp]

/-! ### Additional properties -/

/-- Total variation distance is at most 1 for probability distributions. -/
theorem tvDistFin_le_one [Fintype X]
    (p q : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hp_sum : ∑ x : X, p x = 1) (hq_sum : ∑ x : X, q x = 1) :
    tvDistFin p q ≤ 1 := by
  unfold tvDistFin
  rw [div_le_one (by norm_num : (0 : ℝ) < 2)]
  calc ∑ x : X, |p x - q x|
      ≤ ∑ x : X, (p x + q x) := Finset.sum_le_sum fun x _ =>
        abs_le.mpr ⟨by linarith [hp x, (hq x).le], by linarith [(hq x).le]⟩
    _ = ∑ x : X, p x + ∑ x : X, q x := Finset.sum_add_distrib
    _ = 2 := by rw [hp_sum, hq_sum]; ring

/-- KL divergence is zero iff it is nonpositive (consequence of Gibbs). -/
theorem klDivFin_eq_zero [Fintype X]
    (p q : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hp_sum : ∑ x : X, p x = 1) (hq_sum : ∑ x : X, q x = 1)
    (hkl : klDivFin p q ≤ 0) : klDivFin p q = 0 := by
  linarith [klDivFin_nonneg p q hp hq hp_sum hq_sum]

end InformationTheory
