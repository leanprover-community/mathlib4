/-
Copyright (c) 2026 Charles Swannack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charles Swannack
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# The roots of the Hermite polynomials

The `n`th probabilists' Hermite polynomial `Polynomial.hermite n` has `n` simple real roots.
In this file we prove this, together with the existence of an increasing enumeration of the roots
and of a family of `n + 1` points at which `hermite n` alternates in sign.

## Main results

* `Polynomial.card_aroots_hermite`: the real roots of `hermite n`, counted with multiplicities,
  are `n` in number;
* `Polynomial.nodup_aroots_hermite`: the real roots of `hermite n` are simple;
* `Polynomial.exists_strictMono_aeval_hermite_eq_zero`: there is a strictly monotone family
  `z : Fin n → ℝ` of roots of `hermite n`;
* `Polynomial.exists_strictMono_aeval_hermite_mul_neg`: there is a strictly monotone family
  `y : Fin (n + 1) → ℝ` of points at which `hermite n` alternates in sign.

## Implementation notes

The argument is the classical one. By the Rodrigues formula
`Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`, the zeros of `hermite n` are exactly the
zeros of the `n`th derivative of the Gaussian `fun x ↦ exp (-(x ^ 2 / 2))`, and this derivative
is a polynomial times the Gaussian, hence tends to zero at both infinities. Induction on `n`
therefore produces `n` distinct zeros: `n - 1` of them lie between consecutive zeros of the
previous derivative, by Rolle's Theorem, and the remaining two lie beyond the outermost zeros, by
the versions of Rolle's Theorem for unbounded intervals (`exists_deriv_eq_zero_Ioi` and
`exists_deriv_eq_zero_Iio`; for `n = 0` the version for the whole line is used instead). Since
`hermite n` has degree `n`, these `n` zeros are all of them, so the roots are simple and
`hermite n` splits over `ℝ`; evaluating the resulting product at points interlacing the roots
gives the sign alternation.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

public section

open Filter Set

open scoped Topology

namespace Polynomial

/-! ### Polynomials against a Gaussian -/

/-- A polynomial times the Gaussian `fun x ↦ exp (-(x ^ 2 / 2))` tends to zero at `+∞`. -/
theorem tendsto_eval_mul_gaussian_atTop (p : ℝ[X]) :
    Tendsto (fun x ↦ p.eval x * Real.exp (-(x ^ 2 / 2))) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ ↦ Real.exp (x - x ^ 2 / 2)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp (tendsto_atBot_mono' _ ?_ tendsto_neg_atTop_atBot)
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    nlinarith
  have key := p.tendsto_div_exp_atTop.mul h
  rw [mul_zero] at key
  refine key.congr fun x ↦ ?_
  rw [div_mul_eq_mul_div, mul_div_assoc, ← Real.exp_sub]
  congr 2
  ring

/-- A polynomial times the Gaussian `fun x ↦ exp (-(x ^ 2 / 2))` tends to zero at `-∞`. -/
theorem tendsto_eval_mul_gaussian_atBot (p : ℝ[X]) :
    Tendsto (fun x ↦ p.eval x * Real.exp (-(x ^ 2 / 2))) atBot (𝓝 0) := by
  refine ((tendsto_eval_mul_gaussian_atTop (p.comp (-X))).comp tendsto_neg_atBot_atTop).congr
    fun x ↦ ?_
  simp [eval_comp]

/-! ### The derivatives of a Gaussian -/

/-- The `n`th derivative of a Gaussian vanishes exactly at the roots of `hermite n`. -/
theorem deriv_gaussian_eq_zero_iff (n : ℕ) (x : ℝ) :
    deriv^[n] (fun y ↦ Real.exp (-(y ^ 2 / 2))) x = 0 ↔ aeval x (hermite n) = 0 := by
  have h : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [deriv_gaussian_eq_hermite_mul_gaussian, mul_eq_zero, mul_eq_zero]
  simp [h, Real.exp_ne_zero]

private theorem differentiable_deriv_gaussian (n : ℕ) :
    Differentiable ℝ (deriv^[n] fun y : ℝ ↦ Real.exp (-(y ^ 2 / 2))) := by
  have h : (deriv^[n] fun y : ℝ ↦ Real.exp (-(y ^ 2 / 2)))
      = fun x ↦ (-1 : ℝ) ^ n * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) :=
    _root_.funext (deriv_gaussian_eq_hermite_mul_gaussian n)
  rw [h]
  exact ((differentiable_const _).mul (Polynomial.differentiable_aeval _)).mul
    (Real.differentiable_exp.comp (by fun_prop))

private theorem tendsto_deriv_gaussian_atTop (n : ℕ) :
    Tendsto (deriv^[n] fun y : ℝ ↦ Real.exp (-(y ^ 2 / 2))) atTop (𝓝 0) := by
  have key := (tendsto_eval_mul_gaussian_atTop
    ((hermite n).map (algebraMap ℤ ℝ))).const_mul ((-1 : ℝ) ^ n)
  rw [mul_zero] at key
  refine key.congr fun x ↦ ?_
  rw [deriv_gaussian_eq_hermite_mul_gaussian, aeval_def, eval₂_eq_eval_map]
  ring

private theorem tendsto_deriv_gaussian_atBot (n : ℕ) :
    Tendsto (deriv^[n] fun y : ℝ ↦ Real.exp (-(y ^ 2 / 2))) atBot (𝓝 0) := by
  have key := (tendsto_eval_mul_gaussian_atBot
    ((hermite n).map (algebraMap ℤ ℝ))).const_mul ((-1 : ℝ) ^ n)
  rw [mul_zero] at key
  refine key.congr fun x ↦ ?_
  rw [deriv_gaussian_eq_hermite_mul_gaussian, aeval_def, eval₂_eq_eval_map]
  ring

/-! ### The roots -/

/-- The `n`th derivative of a Gaussian has `n` distinct zeros, listed in increasing order. -/
private theorem exists_strictMono_deriv_gaussian_eq_zero (n : ℕ) :
    ∃ z : Fin n → ℝ, StrictMono z ∧
      ∀ i, deriv^[n] (fun y : ℝ ↦ Real.exp (-(y ^ 2 / 2))) (z i) = 0 := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨z, hz, hz0⟩ := ih
    set F := deriv^[n] fun y : ℝ ↦ Real.exp (-(y ^ 2 / 2)) with hF
    have hcont : Continuous F := (differentiable_deriv_gaussian n).continuous
    have hderiv : deriv F = deriv^[n + 1] fun y : ℝ ↦ Real.exp (-(y ^ 2 / 2)) :=
      (Function.iterate_succ_apply' deriv n _).symm
    -- there is a zero of `deriv F` in each of the `n + 1` gaps between the zeros of `F`
    have key : ∀ i : Fin (n + 1), ∃ w : ℝ, deriv F w = 0 ∧
        (∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → w < z j) ∧
          ∀ j : Fin n, (j : ℕ) < (i : ℕ) → z j < w := by
      intro i
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · obtain ⟨w, hw⟩ := exists_deriv_eq_zero_of_tendsto (tendsto_deriv_gaussian_atBot _)
          (tendsto_deriv_gaussian_atTop _)
        exact ⟨w, hw, fun j ↦ j.elim0, fun j ↦ j.elim0⟩
      have hin : (i : ℕ) < n + 1 := i.isLt
      rcases eq_or_ne (i : ℕ) 0 with h0 | h0
      · -- to the left of the first zero of `F`
        have hb : Tendsto F (𝓝[<] z ⟨0, hn⟩) (𝓝 0) := by
          rw [← hz0 ⟨0, hn⟩]
          exact (hcont.tendsto _).mono_left nhdsWithin_le_nhds
        obtain ⟨w, hwmem, hw⟩ := exists_deriv_eq_zero_Iio (tendsto_deriv_gaussian_atBot n) hb
        exact ⟨w, hw, fun j _ ↦ hwmem.trans_le
            (hz.monotone (Fin.le_def.2 (show 0 ≤ (j : ℕ) from Nat.zero_le _))),
          fun j hj ↦ absurd hj (by omega)⟩
      rcases eq_or_ne (i : ℕ) n with hlast | hlast
      · -- to the right of the last zero of `F`
        have ha : Tendsto F (𝓝[>] z ⟨n - 1, by omega⟩) (𝓝 0) := by
          rw [← hz0 ⟨n - 1, by omega⟩]
          exact (hcont.tendsto _).mono_left nhdsWithin_le_nhds
        obtain ⟨w, hwmem, hw⟩ := exists_deriv_eq_zero_Ioi ha (tendsto_deriv_gaussian_atTop n)
        refine ⟨w, hw, fun j hj ↦ absurd hj (by have := j.isLt; omega), fun j _ ↦
          (hz.monotone (Fin.le_def.2 (show (j : ℕ) ≤ n - 1 by have := j.isLt; omega))).trans_lt
            hwmem⟩
      · -- between two consecutive zeros of `F`
        have h1 : (i : ℕ) - 1 < n := by omega
        have h2 : (i : ℕ) < n := by omega
        have hlt : (⟨(i : ℕ) - 1, h1⟩ : Fin n) < ⟨(i : ℕ), h2⟩ :=
          Fin.lt_def.2 (show (i : ℕ) - 1 < (i : ℕ) by omega)
        obtain ⟨w, hwmem, hw⟩ := exists_deriv_eq_zero (hz hlt) hcont.continuousOn
          ((hz0 _).trans (hz0 _).symm)
        exact ⟨w, hw, fun j hj ↦ hwmem.2.trans_le
            (hz.monotone (Fin.le_def.2 (show (i : ℕ) ≤ (j : ℕ) from hj))),
          fun j hj ↦ (hz.monotone
            (Fin.le_def.2 (show (j : ℕ) ≤ (i : ℕ) - 1 by omega))).trans_lt hwmem.1⟩
    choose w hw0 hwlt hwgt using key
    refine ⟨w, Fin.strictMono_iff_lt_succ.2 fun i ↦ ?_, fun i ↦ ?_⟩
    · exact (hwlt i.castSucc i (by simp)).trans (hwgt i.succ i (by simp))
    · rw [← hderiv]
      exact hw0 i

/-- The `n`th Hermite polynomial has `n` distinct real roots, listed in increasing order. -/
theorem exists_strictMono_aeval_hermite_eq_zero (n : ℕ) :
    ∃ z : Fin n → ℝ, StrictMono z ∧ ∀ i, aeval (z i) (hermite n) = 0 := by
  obtain ⟨z, hz, hz0⟩ := exists_strictMono_deriv_gaussian_eq_zero n
  exact ⟨z, hz, fun i ↦ (deriv_gaussian_eq_zero_iff n (z i)).1 (hz0 i)⟩

private theorem monic_hermite_map_real (n : ℕ) : ((hermite n).map (algebraMap ℤ ℝ)).Monic :=
  Monic.map _ (hermite_monic n)

private theorem natDegree_hermite_map_real (n : ℕ) :
    ((hermite n).map (algebraMap ℤ ℝ)).natDegree = n := by
  rw [natDegree_map_eq_of_injective (algebraMap ℤ ℝ).injective_int, natDegree_hermite]

/-- If `z : Fin n → ℝ` is a strictly monotone family of roots of `hermite n`, then it enumerates
all the real roots of `hermite n`, each of them once. -/
private theorem aroots_hermite_eq {n : ℕ} {z : Fin n → ℝ} (hz : StrictMono z)
    (hz0 : ∀ i, aeval (z i) (hermite n) = 0) :
    (hermite n).aroots ℝ = Finset.univ.val.map z := by
  classical
  have hnodup : (Finset.univ.val.map z).Nodup := Finset.univ.nodup.map hz.injective
  have hcard : Multiset.card (Finset.univ.val.map z) = n := by simp
  have hle : Finset.univ.val.map z ≤ (hermite n).aroots ℝ := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a ∈ Finset.univ.val.map z
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
      rw [Multiset.count_eq_one_of_mem hnodup ha]
      exact Multiset.count_pos.2 (mem_aroots.2 ⟨Monic.ne_zero (hermite_monic n), hz0 i⟩)
    · rw [Multiset.count_eq_zero_of_notMem ha]
      exact Nat.zero_le _
  refine (Multiset.eq_of_le_of_card_le hle ?_).symm
  rw [hcard, aroots_def]
  exact (card_roots' _).trans_eq (natDegree_hermite_map_real n)

/-- The `n`th Hermite polynomial has `n` real roots, counted with multiplicities. -/
theorem card_aroots_hermite (n : ℕ) : Multiset.card ((hermite n).aroots ℝ) = n := by
  obtain ⟨z, hz, hz0⟩ := exists_strictMono_aeval_hermite_eq_zero n
  rw [aroots_hermite_eq hz hz0]
  simp

/-- The real roots of the `n`th Hermite polynomial are simple. -/
theorem nodup_aroots_hermite (n : ℕ) : ((hermite n).aroots ℝ).Nodup := by
  obtain ⟨z, hz, hz0⟩ := exists_strictMono_aeval_hermite_eq_zero n
  rw [aroots_hermite_eq hz hz0]
  exact Finset.univ.nodup.map hz.injective

/-- If `z : Fin n → ℝ` is a strictly monotone family of roots of `hermite n`, then the value of
`hermite n` at `x` is the product of the `x - z i`. -/
private theorem aeval_hermite_eq_prod {n : ℕ} {z : Fin n → ℝ} (hz : StrictMono z)
    (hz0 : ∀ i, aeval (z i) (hermite n) = 0) (x : ℝ) :
    aeval x (hermite n) = ∏ i, (x - z i) := by
  have hcard : Multiset.card ((hermite n).map (algebraMap ℤ ℝ)).roots
      = ((hermite n).map (algebraMap ℤ ℝ)).natDegree := by
    rw [← aroots_def, card_aroots_hermite, natDegree_hermite_map_real]
  have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_hermite_map_real n) hcard
  rw [aeval_def, eval₂_eq_eval_map]
  conv_lhs => rw [← hfac]
  rw [eval_multiset_prod, Multiset.map_map, ← aroots_def, aroots_hermite_eq hz hz0,
    Multiset.map_map, Finset.prod_eq_multiset_prod]
  simp [Function.comp_def]

/-- The `n`th Hermite polynomial alternates in sign at `n + 1` points. -/
theorem exists_strictMono_aeval_hermite_mul_neg (n : ℕ) :
    ∃ y : Fin (n + 1) → ℝ, StrictMono y ∧
      ∀ i : Fin n, aeval (y i.castSucc) (hermite n) * aeval (y i.succ) (hermite n) < 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun _ ↦ 0, fun i j hij ↦ ?_, fun i ↦ i.elim0⟩
    exact absurd (Fin.lt_def.1 hij) (by have := i.isLt; have := j.isLt; omega)
  obtain ⟨z, hz, hz0⟩ := exists_strictMono_aeval_hermite_eq_zero n
  -- the points interlacing the roots
  set y : Fin (n + 1) → ℝ := fun i ↦
    if (i : ℕ) = 0 then z ⟨0, hn⟩ - 1
    else if h : (i : ℕ) = n then z ⟨n - 1, by omega⟩ + 1
    else (z ⟨(i : ℕ) - 1, by omega⟩ + z ⟨(i : ℕ), by omega⟩) / 2 with hy
  have hlt : ∀ (j : Fin n) (i : Fin (n + 1)), (j : ℕ) < (i : ℕ) → z j < y i := by
    intro j i hji
    have hjn : (j : ℕ) < n := j.isLt
    have hin : (i : ℕ) < n + 1 := i.isLt
    simp only [hy]
    split_ifs with h0 hlast
    · omega
    · have h : z j ≤ z ⟨n - 1, by omega⟩ :=
        hz.monotone (Fin.le_def.2 (show (j : ℕ) ≤ n - 1 by omega))
      linarith
    · have h1 : z j ≤ z ⟨(i : ℕ) - 1, by omega⟩ :=
        hz.monotone (Fin.le_def.2 (show (j : ℕ) ≤ (i : ℕ) - 1 by omega))
      have h2 : z ⟨(i : ℕ) - 1, by omega⟩ < z ⟨(i : ℕ), by omega⟩ :=
        hz (Fin.lt_def.2 (show (i : ℕ) - 1 < (i : ℕ) by omega))
      linarith
  have hgt : ∀ (j : Fin n) (i : Fin (n + 1)), (i : ℕ) ≤ (j : ℕ) → y i < z j := by
    intro j i hij
    have hjn : (j : ℕ) < n := j.isLt
    have hin : (i : ℕ) < n + 1 := i.isLt
    simp only [hy]
    split_ifs with h0 hlast
    · have h : z ⟨0, hn⟩ ≤ z j := hz.monotone (Fin.le_def.2 (show 0 ≤ (j : ℕ) from Nat.zero_le _))
      linarith
    · omega
    · have h1 : z ⟨(i : ℕ), by omega⟩ ≤ z j :=
        hz.monotone (Fin.le_def.2 (show (i : ℕ) ≤ (j : ℕ) from hij))
      have h2 : z ⟨(i : ℕ) - 1, by omega⟩ < z ⟨(i : ℕ), by omega⟩ :=
        hz (Fin.lt_def.2 (show (i : ℕ) - 1 < (i : ℕ) by omega))
      linarith
  refine ⟨y, Fin.strictMono_iff_lt_succ.2 fun i ↦
    (hgt i i.castSucc (by simp)).trans (hlt i i.succ (by simp)), fun i ↦ ?_⟩
  have h1 : y i.castSucc < z i := hgt i i.castSucc (by simp)
  have h2 : z i < y i.succ := hlt i i.succ (by simp)
  rw [aeval_hermite_eq_prod hz hz0, aeval_hermite_eq_prod hz hz0, ← Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  refine mul_neg_of_neg_of_pos (by nlinarith) (Finset.prod_pos fun j hj ↦ ?_)
  have hji : (j : ℕ) ≠ (i : ℕ) := fun h ↦ (Finset.mem_erase.1 hj).1 (Fin.ext h)
  rcases lt_or_gt_of_ne hji with h | h
  · have h3 : z j < y i.castSucc := hlt j i.castSucc (by simpa using h)
    have h4 : z j < y i.succ := hlt j i.succ (by simp only [Fin.val_succ]; omega)
    nlinarith
  · have h3 : y i.castSucc < z j := hgt j i.castSucc (by simpa using h.le)
    have h4 : y i.succ < z j := hgt j i.succ (by simp only [Fin.val_succ]; omega)
    nlinarith

end Polynomial
