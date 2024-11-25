/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Binomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The Mahler basis of continuous functions

In this file we introduce the Mahler basis function `mahler k`, for `k : ℕ`, which is the unique
continuous map `ℤ_[p] → ℚ_[p]` agreeing with `n ↦ n.choose k` for `n ∈ ℕ`.

We also show that for any continuous function `f` on `ℤ_[p]` (valued in a `p`-adic normed space),
the iterated forward differences `Δ^[n] f 0` tend to 0. For this, we follow the argument of
Bojanić [bojanic74].

In future PR's, we will show that the Mahler functions give a Banach basis for the space of
continuous maps `ℤ_[p] → ℚ_[p]`, with the basis coefficients of `f` given by the forward differences
`Δ^[n] f 0`.

## References

* [R. Bojanić, *A simple proof of Mahler's theorem on approximation of continuous functions of a
  p-adic variable by polynomials*][bojanic74]
* [P. Colmez, *Fonctions d'une variable p-adique*][colmez2010]

## Tags

Bojanic
-/

open Finset fwdDiff IsUltrametricDist NNReal Filter Topology

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt

/-- Bound for norms of ascending Pochhammer symbols. -/
lemma norm_ascPochhammer_le (k : ℕ) (x : ℤ_[p]) :
    ‖(ascPochhammer ℤ_[p] k).eval x‖ ≤ ‖(k.factorial : ℤ_[p])‖ := by
  let f := (ascPochhammer ℤ_[p] k).eval
  change ‖f x‖ ≤ ‖_‖
  have hC : (k.factorial : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hf : ContinuousAt f x := Polynomial.continuousAt _
  -- find `n : ℕ` such that `‖f x - f n‖ ≤ ‖k!‖`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖f x - f n‖ ≤ ‖(k.factorial : ℤ_[p])‖ := by
    obtain ⟨δ, hδp, hδ⟩ := Metric.continuousAt_iff.mp hf _ (norm_pos_iff.mpr hC)
    obtain ⟨n, hn'⟩ := PadicInt.denseRange_natCast.exists_dist_lt x hδp
    simpa only [← dist_eq_norm_sub'] using ⟨n, (hδ (dist_comm x n ▸ hn')).le⟩
  -- use ultrametric property to show that `‖f n‖ ≤ ‖k!‖` implies `‖f x‖ ≤ ‖k!‖`
  refine sub_add_cancel (f x) _ ▸ (IsUltrametricDist.norm_add_le_max _ (f n)).trans (max_le hn ?_)
  -- finish using the fact that `n.multichoose k ∈ ℤ`
  simp_rw [f, ← ascPochhammer_eval_cast, Polynomial.eval_eq_smeval,
    ← Ring.factorial_nsmul_multichoose_eq_ascPochhammer, smul_eq_mul, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one _)

/-- The p-adic integers are a binomial ring, i.e. a ring where binomial coefficients make sense. -/
noncomputable instance instBinomialRing : BinomialRing ℤ_[p] where
  nsmul_right_injective n hn := smul_right_injective ℤ_[p] hn
  -- We define `multichoose` as a fraction in `ℚ_[p]` together with a proof that its norm is `≤ 1`.
  multichoose x k := ⟨(ascPochhammer ℤ_[p] k).eval x / (k.factorial : ℚ_[p]), by
    rw [norm_div, div_le_one (by simpa using k.factorial_ne_zero)]
    exact x.norm_ascPochhammer_le k⟩
  factorial_nsmul_multichoose x k := by rw [← Subtype.coe_inj, nsmul_eq_mul, PadicInt.coe_mul,
    PadicInt.coe_natCast, mul_div_cancel₀ _ (mod_cast k.factorial_ne_zero), Subtype.coe_inj,
    Polynomial.eval_eq_smeval, Polynomial.ascPochhammer_smeval_cast]

@[fun_prop]
lemma continuous_multichoose (k : ℕ) : Continuous (fun x : ℤ_[p] ↦ Ring.multichoose x k) := by
  simp only [Ring.multichoose, BinomialRing.multichoose, continuous_induced_rng]
  fun_prop

@[fun_prop]
lemma continuous_choose (k : ℕ) : Continuous (fun x : ℤ_[p] ↦ Ring.choose x k) := by
  simp only [Ring.choose]
  fun_prop

end PadicInt

/--
The `k`-th Mahler basis function, i.e. the unique continuous function `ℤ_[p] → ℚ_[p]`
agreeing with `n ↦ n.choose k` for `n ∈ ℕ`. See [colmez2010], §1.2.1.
-/
noncomputable def mahler (k : ℕ) : C(ℤ_[p], ℚ_[p]) where
  toFun x := ↑(Ring.choose x k)
  continuous_toFun := continuous_induced_rng.mp (PadicInt.continuous_choose k)

lemma mahler_apply (k : ℕ) (x : ℤ_[p]) : mahler k x = Ring.choose x k := rfl

/-- The function `mahler k` extends `n ↦ n.choose k` on `ℕ`. -/
lemma mahler_natCast_eq (k n : ℕ) : mahler k (n : ℤ_[p]) = n.choose k := by
  simp only [mahler_apply, Ring.choose_natCast, PadicInt.coe_natCast]

/--
The uniform norm of the `k`-th Mahler basis function is 1, for every `k`.
-/
@[simp] lemma norm_mahler_eq (k : ℕ) : ‖(mahler k : C(ℤ_[p], ℚ_[p]))‖ = 1 := by
  apply le_antisymm
  · -- Show all values have norm ≤ 1
    exact (mahler k).norm_le_of_nonempty.mpr (fun _ ↦ PadicInt.norm_le_one _)
  · -- Show norm 1 is attained at `x = k`
    refine (le_of_eq ?_).trans ((mahler k).norm_coe_le_norm k)
    rw [mahler_natCast_eq, Nat.choose_self, Nat.cast_one, norm_one]

section fwdDiff

variable {M G : Type*}

/-- Bound for iterated forward differences of a continuous function from a compact space to a
nonarchimedean seminormed group. -/
lemma IsUltrametricDist.norm_fwdDiff_iter_apply_le [TopologicalSpace M] [CompactSpace M]
    [AddCommMonoid M] [SeminormedAddCommGroup G] [IsUltrametricDist G]
    (h : M) (f : C(M, G)) (m : M) (n : ℕ) : ‖Δ_[h]^[n] f m‖ ≤ ‖f‖ := by
  -- A proof by induction on `n` would be possible but would involve some messing around to
  -- define `Δ_[h]` as an operator on continuous maps (not just on bare functions). So instead we
  -- use the formula for `Δ_[h]^[n] f` as a sum.
  rw [fwdDiff_iter_eq_sum_shift]
  refine norm_sum_le_of_forall_le_of_nonneg (norm_nonneg f) fun i _ ↦ ?_
  exact (norm_zsmul_le _ _).trans (f.norm_coe_le_norm _)

/-- First step in Bojanić's proof of Mahler's theorem (equation (10) of [bojanic74]): rewrite
`Δ^[n + R] f 0` in a shape that makes it easy to bound `p`-adically. -/
private lemma bojanic_mahler_step1 [AddCommMonoidWithOne M] [AddCommGroup G] (f : M → G)
    (n : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    Δ_[1]^[n + R] f 0 = -∑ j ∈ range (R - 1), R.choose (j + 1) • Δ_[1]^[n + (j + 1)] f 0 +
      ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • (f (k + R) - f k) := by
  have aux : Δ_[1]^[n + R] f 0 = R.choose (R - 1 + 1) • Δ_[1]^[n + R] f 0 := by
    rw [Nat.sub_add_cancel hR, Nat.choose_self, one_smul]
  rw [neg_add_eq_sub, eq_sub_iff_add_eq, add_comm, aux, (by omega : n + R = (n + ((R - 1) + 1))),
    ← sum_range_succ, Nat.sub_add_cancel hR,
    ← sub_eq_iff_eq_add.mpr (sum_range_succ' (fun x ↦ R.choose x • Δ_[1]^[n + x] f 0) R), add_zero,
    Nat.choose_zero_right, one_smul]
  have : ∑ k ∈ Finset.range (R + 1), R.choose k • Δ_[1]^[n + k] f 0 = Δ_[1]^[n] f R := by
    simpa only [← Function.iterate_add_apply, add_comm, nsmul_one, add_zero] using
      (shift_eq_sum_fwdDiff_iter 1 (Δ_[1]^[n] f) R 0).symm
  simp only [this, fwdDiff_iter_eq_sum_shift (1 : M) f n, mul_comm, nsmul_one, mul_smul, add_comm,
    add_zero, smul_sub, sum_sub_distrib]

end fwdDiff

namespace PadicInt

section norm_fwdDiff

variable {p : ℕ} [hp : Fact p.Prime] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℚ_[p] E] [IsUltrametricDist E]

/--
Second step in Bojanić's proof of Mahler's theorem (equation (11) of [bojanic74]): show that values
`Δ_[1]^[n + p ^ t] f 0` for large enough `n` are bounded by the max of `(‖f‖ / p ^ s)` and `1 / p`
times a sup over values for smaller `n`.

We use `nnnorm`s on the RHS since `Finset.sup` requires an order with a bottom element.
-/
private lemma bojanic_mahler_step2 {f : C(ℤ_[p], E)} {s t : ℕ}
    (hst : ∀ x y : ℤ_[p], ‖x - y‖ ≤ p ^ (-t : ℤ) → ‖f x - f y‖ ≤ ‖f‖ / p ^ s) (n : ℕ) :
    ‖Δ_[1]^[n + p ^ t] f 0‖ ≤ max ↑((Finset.range (p ^ t - 1)).sup
      fun j ↦ ‖Δ_[1]^[n + (j + 1)] f 0‖₊ / p) (‖f‖ / p ^ s) := by
  -- Use previous lemma to rewrite in a convenient form.
  rw [bojanic_mahler_step1 _ _ (one_le_pow₀ hp.out.one_le)]
  -- Now use ultrametric property and bound each term separately.
  refine (norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · -- Bounding the sum over `range (p ^ t - 1)`: every term involves a value `Δ_[1]^[·] f 0` and
    -- a binomial coefficient which is divisible by `p`
    rw [norm_neg, ← coe_nnnorm, coe_le_coe]
    refine nnnorm_sum_le_of_forall_le (fun i hi ↦ Finset.le_sup_of_le hi ?_)
    rw [mem_range] at hi
    rw [← Nat.cast_smul_eq_nsmul ℚ_[p], nnnorm_smul, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by simp only [zero_le])
    -- remains to show norm of binomial coeff is `≤ p⁻¹`
    have : 0 < (p ^ t).choose (i + 1) := Nat.choose_pos (by omega)
    rw [← zpow_neg_one, ← coe_le_coe, coe_nnnorm, Padic.norm_eq_pow_val (mod_cast this.ne'),
      coe_zpow, NNReal.coe_natCast, (zpow_right_strictMono₀ (mod_cast hp.out.one_lt)).le_iff_le,
      neg_le_neg_iff, Padic.valuation_natCast, Nat.one_le_cast]
    exact one_le_padicValNat_of_dvd this <| hp.out.dvd_choose_pow (by omega) (by omega)
  · -- Bounding the sum over `range (n + 1)`: every term is small by the choice of `t`
    refine norm_sum_le_of_forall_le_of_nonempty nonempty_range_succ (fun i _ ↦ ?_)
    calc ‖((-1 : ℤ) ^ (n - i) * n.choose i) • (f (i + ↑(p ^ t)) - f i)‖
    _ ≤ ‖f (i + ↑(p ^ t)) - f i‖ := by
      rw [← Int.cast_smul_eq_zsmul ℚ_[p], norm_smul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      simpa only [← coe_intCast] using norm_le_one _
    _ ≤ ‖f‖ / p ^ s := by
      apply hst
      rw [Nat.cast_pow, add_sub_cancel_left, norm_pow, norm_p, inv_pow, zpow_neg, zpow_natCast]

/--
Explicit bound for the decay rate of the Mahler coefficients of a continuous function on `ℤ_[p]`.
This will be used to prove Mahler's theorem.
 -/
lemma fwdDiff_iter_le_of_forall_le {f : C(ℤ_[p], E)} {s t : ℕ}
    (hst : ∀ x y : ℤ_[p], ‖x - y‖ ≤ p ^ (-t : ℤ) → ‖f x - f y‖ ≤ ‖f‖ / p ^ s) (n : ℕ) :
    ‖Δ_[1]^[n + s * p ^ t] f 0‖ ≤ ‖f‖ / p ^ s := by
  -- We show the following more general statement by induction on `k`:
  suffices ∀ {k : ℕ}, k ≤ s → ‖Δ_[1]^[n + k * p ^ t] f 0‖ ≤ ‖f‖ / p ^ k from this le_rfl
  intro k hk
  induction' k with k IH generalizing n
  · -- base case just says that `‖Δ^[·] (⇑f) 0‖` is bounded by `‖f‖`
    simpa only [zero_mul, pow_zero, add_zero, div_one] using norm_fwdDiff_iter_apply_le 1 f 0 n
  · -- induction is the "step 2" lemma above
    rw [add_mul, one_mul, ← add_assoc]
    refine (bojanic_mahler_step2 hst (n + k * p ^ t)).trans (max_le ?_ ?_)
    · rw [← coe_nnnorm, ← NNReal.coe_natCast, ← NNReal.coe_pow, ← NNReal.coe_div, NNReal.coe_le_coe]
      refine Finset.sup_le fun j _ ↦ ?_
      rw [pow_succ, ← div_div, div_le_div_iff_of_pos_right (mod_cast hp.out.pos), add_right_comm]
      exact_mod_cast IH (n + (j + 1)) (by omega)
    · exact div_le_div_of_nonneg_left (norm_nonneg _)
        (mod_cast pow_pos hp.out.pos _) (mod_cast pow_le_pow_right₀ hp.out.one_le hk)

/-- Key lemma for Mahler's theorem: for `f` a continuous function on `ℤ_[p]`, the sequence
`n ↦ Δ^[n] f 0` tends to 0. See `PadicInt.fwdDiff_iter_le_of_forall_le` for an explicit
estimate of the decay rate. -/
lemma fwdDiff_tendsto_zero (f : C(ℤ_[p], E)) : Tendsto (Δ_[1]^[·] f 0) atTop (𝓝 0) := by
  -- first extract an `s`
  refine NormedAddCommGroup.tendsto_nhds_zero.mpr (fun ε hε ↦ ?_)
  have : Tendsto (fun s ↦ ‖f‖ / p ^ s) _ _ := tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (mod_cast hp.out.one_lt))
  obtain ⟨s, hs⟩ := (this.eventually_lt_const hε).exists
  refine .mp ?_ (.of_forall fun x hx ↦ lt_of_le_of_lt hx hs)
  -- use uniform continuity to find `t`
  obtain ⟨t, ht⟩ : ∃ t : ℕ, ∀ x y, ‖x - y‖ ≤ p ^ (-t : ℤ) → ‖f x - f y‖ ≤ ‖f‖ / p ^ s := by
    rcases eq_or_ne f 0 with rfl | hf
    · -- silly case : f = 0
      simp
    have : 0 < ‖f‖ / p ^ s := div_pos (norm_pos_iff.mpr hf) (mod_cast pow_pos hp.out.pos _)
    obtain ⟨δ, hδpos, hδf⟩ := f.uniform_continuity _ this
    obtain ⟨t, ht⟩ := PadicInt.exists_pow_neg_lt p hδpos
    exact ⟨t, fun x y hxy ↦  by simpa only [dist_eq_norm_sub] using (hδf (hxy.trans_lt ht)).le⟩
  filter_upwards [eventually_ge_atTop (s * p ^ t)] with m hm
  simpa only [Nat.sub_add_cancel hm] using fwdDiff_iter_le_of_forall_le ht (m - s * p ^ t)

end norm_fwdDiff

end PadicInt
