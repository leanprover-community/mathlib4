/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Definition of the Riemann zeta function

## Main definitions:

* `riemannZeta`: the Riemann zeta function `ζ : ℂ → ℂ`.
* `completedRiemannZeta`: the completed zeta function `Λ : ℂ → ℂ`, which satisfies
  `Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (away from the poles of `Γ(s / 2)`).
* `completedRiemannZeta₀`: the entire function `Λ₀` satisfying
  `Λ₀(s) = Λ(s) + 1 / (s - 1) - 1 / s` wherever the RHS is defined.

Note that mathematically `ζ(s)` is undefined at `s = 1`, while `Λ(s)` is undefined at both `s = 0`
and `s = 1`. Our construction assigns some values at these points; exact formulae involving the
Euler-Mascheroni constant will follow in a subsequent PR.

## Main results:

* `differentiable_completedZeta₀` : the function `Λ₀(s)` is entire.
* `differentiableAt_completedZeta` : the function `Λ(s)` is differentiable away from `s = 0` and
  `s = 1`.
* `differentiableAt_riemannZeta` : the function `ζ(s)` is differentiable away from `s = 1`.
* `zeta_eq_tsum_one_div_nat_add_one_cpow` : for `1 < re s`, we have
  `ζ(s) = ∑' (n : ℕ), 1 / (n + 1) ^ s`.
* `completedRiemannZeta₀_one_sub`, `completedRiemannZeta_one_sub`, and `riemannZeta_one_sub` :
  functional equation relating values at `s` and `1 - s`
* `completedRiemannZeta₀_conj` and `completedRiemannZeta_conj` : Schwarz reflection identities
  `Λ₀(conj s) = conj (Λ₀ s)` and `Λ(conj s) = conj (Λ s)`

For special-value formulae expressing `ζ (2 * k)` and `ζ (1 - 2 * k)` in terms of Bernoulli numbers
see `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`. For computation of the constant term as
`s → 1`, see `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`.

## Outline of proofs:

These results are mostly special cases of more general results for even Hurwitz zeta functions
proved in `Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean`.
-/

@[expose] public section


open CharZero Set Filter HurwitzZeta

open Complex hiding exp continuous_exp

open scoped Topology Real ComplexConjugate

noncomputable section

/-!
## Definition of the completed Riemann zeta
-/

/-- The completed Riemann zeta function with its poles removed, `Λ(s) + 1 / s - 1 / (s - 1)`. -/
def completedRiemannZeta₀ (s : ℂ) : ℂ := completedHurwitzZetaEven₀ 0 s

/-- The completed Riemann zeta function, `Λ(s)`, which satisfies
`Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (up to a minor correction at `s = 0`). -/
def completedRiemannZeta (s : ℂ) : ℂ := completedHurwitzZetaEven 0 s

lemma HurwitzZeta.completedHurwitzZetaEven_zero (s : ℂ) :
    completedHurwitzZetaEven 0 s = completedRiemannZeta s := rfl

lemma HurwitzZeta.completedHurwitzZetaEven₀_zero (s : ℂ) :
    completedHurwitzZetaEven₀ 0 s = completedRiemannZeta₀ s := rfl

lemma HurwitzZeta.completedCosZeta_zero (s : ℂ) :
    completedCosZeta 0 s = completedRiemannZeta s := by
  rw [completedRiemannZeta, completedHurwitzZetaEven, completedCosZeta, hurwitzEvenFEPair_zero_symm]

lemma HurwitzZeta.completedCosZeta₀_zero (s : ℂ) :
    completedCosZeta₀ 0 s = completedRiemannZeta₀ s := by
  rw [completedRiemannZeta₀, completedHurwitzZetaEven₀, completedCosZeta₀,
    hurwitzEvenFEPair_zero_symm]

lemma completedRiemannZeta_eq (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  simp_rw [completedRiemannZeta, completedRiemannZeta₀, completedHurwitzZetaEven_eq, if_true]

/-- The modified completed Riemann zeta function `Λ(s) + 1 / s + 1 / (1 - s)` is entire. -/
theorem differentiable_completedZeta₀ : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedHurwitzZetaEven₀ 0

/-- The completed Riemann zeta function `Λ(s)` is differentiable away from `s = 0` and `s = 1`. -/
theorem differentiableAt_completedZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s :=
  differentiableAt_completedHurwitzZetaEven 0 (Or.inl hs) hs'

/-- Riemann zeta functional equation, formulated for `Λ₀`: for any complex `s` we have
`Λ₀(1 - s) = Λ₀ s`. -/
theorem completedRiemannZeta₀_one_sub (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s := by
  rw [← completedHurwitzZetaEven₀_zero, ← completedCosZeta₀_zero, completedHurwitzZetaEven₀_one_sub]

/-- Riemann zeta functional equation, formulated for `Λ`: for any complex `s` we have
`Λ (1 - s) = Λ s`. -/
theorem completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  rw [← completedHurwitzZetaEven_zero, ← completedCosZeta_zero, completedHurwitzZetaEven_one_sub]

/-- The residue of `Λ(s)` at `s = 1` is equal to `1`. -/
lemma completedRiemannZeta_residue_one :
    Tendsto (fun s ↦ (s - 1) * completedRiemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  completedHurwitzZetaEven_residue_one 0

/-!
## The un-completed Riemann zeta function
-/

/-- The Riemann zeta function `ζ(s)`. -/
def riemannZeta := hurwitzZetaEven 0

lemma HurwitzZeta.hurwitzZetaEven_zero : hurwitzZetaEven 0 = riemannZeta := rfl

lemma HurwitzZeta.cosZeta_zero : cosZeta 0 = riemannZeta := by
  simp_rw [cosZeta, riemannZeta, hurwitzZetaEven, if_true, completedHurwitzZetaEven_zero,
    completedCosZeta_zero]

lemma HurwitzZeta.hurwitzZeta_zero : hurwitzZeta 0 = riemannZeta := by
  ext1 s
  simpa [hurwitzZeta, hurwitzZetaEven_zero] using hurwitzZetaOdd_neg 0 s

lemma HurwitzZeta.expZeta_zero : expZeta 0 = riemannZeta := by
  ext1 s
  rw [expZeta, cosZeta_zero, add_eq_left, mul_eq_zero, eq_false_intro I_ne_zero, false_or,
    ← eq_neg_self_iff, ← sinZeta_neg, neg_zero]

/-- The Riemann zeta function is differentiable away from `s = 1`. -/
theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_hurwitzZetaEven _ hs'

lemma differentiableOn_riemannZeta :
    DifferentiableOn ℂ riemannZeta {1}ᶜ :=
  fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt

lemma analyticOn_riemannZeta :
    AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
  differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton

/-- We have `ζ(0) = -1 / 2`. -/
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
  simp_rw [riemannZeta, hurwitzZetaEven, Function.update_self, if_true]

lemma riemannZeta_def_of_ne_zero {s : ℂ} (hs : s ≠ 0) :
    riemannZeta s = completedRiemannZeta s / Gammaℝ s := by
  rw [riemannZeta, hurwitzZetaEven, Function.update_of_ne hs, completedHurwitzZetaEven_zero]

/-- The trivial zeroes of the zeta function. -/
theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
  hurwitzZetaEven_neg_two_mul_nat_add_one 0 n

/-- Riemann zeta functional equation, formulated for `ζ`: if `1 - s ∉ ℕ`, then we have
`ζ (1 - s) = 2 ^ (1 - s) * π ^ (-s) * Γ s * sin (π * (1 - s) / 2) * ζ s`. -/
theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s := by
  rw [riemannZeta, hurwitzZetaEven_one_sub 0 hs (Or.inr hs'), cosZeta_zero, hurwitzZetaEven_zero]

/-- A formal statement of the **Riemann hypothesis** – constructing a term of this type is worth a
million dollars. -/
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2

/-!
## Relating the Mellin transform to the Dirichlet series
-/

theorem completedZeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    completedRiemannZeta s =
      (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  have := (hasSum_nat_completedCosZeta 0 hs).tsum_eq.symm
  simp only [QuotientAddGroup.mk_zero, completedCosZeta_zero] at this
  simp only [this, Gammaℝ_def, mul_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one, mul_one_div,
    ← tsum_mul_left]
  congr 1 with n
  split_ifs with h
  · simp only [h, Nat.cast_zero, zero_cpow (Complex.ne_zero_of_one_lt_re hs), div_zero]
  · rfl

/-- The Riemann zeta function agrees with the naive Dirichlet-series definition when the latter
converges. (Note that this is false without the assumption: when `re s ≤ 1` the sum is divergent,
and we use a different definition to obtain the analytic continuation to all `s`.) -/
theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  simpa only [QuotientAddGroup.mk_zero, cosZeta_zero, mul_zero, zero_mul, Real.cos_zero,
    ofReal_one] using (hasSum_nat_cosZeta 0 hs).tsum_eq.symm

/-- Alternate formulation of `zeta_eq_tsum_one_div_nat_cpow` with a `+ 1` (to avoid relying
on mathlib's conventions for `0 ^ s`). -/
theorem zeta_eq_tsum_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s := by
  have := zeta_eq_tsum_one_div_nat_cpow hs
  rw [Summable.tsum_eq_zero_add] at this
  · simpa [zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · rwa [Complex.summable_one_div_nat_cpow]

/-- Special case of `zeta_eq_tsum_one_div_nat_cpow` when the argument is in `ℕ`, so the power
function can be expressed using naïve `pow` rather than `cpow`. -/
theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) :
    riemannZeta k = ∑' n : ℕ, 1 / (n : ℂ) ^ k := by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_natCast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_natCast]

lemma two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even {k : ℕ} (hk : 2 ≤ k) (hk2 : Even k) :
    2 * riemannZeta k = ∑' (n : ℤ), ((n : ℂ) ^ k)⁻¹ := by
  have hkk : 1 < k := by linarith
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
  · have h0 : (0 ^ k : ℂ)⁻¹ = 0 := by simp; lia
    norm_cast
    simp [h0, zeta_eq_tsum_one_div_nat_add_one_cpow (s := k) (by simp [hkk]),
      tsum_pnat_eq_tsum_succ (f := fun n => ((n : ℂ) ^ k)⁻¹)]
  · intro n
    simp [Even.neg_pow hk2]
  · exact (Summable.of_nat_of_neg (by simp [hkk]) (by simp [hkk])).of_norm

/-- The residue of `ζ(s)` at `s = 1` is equal to 1. -/
lemma riemannZeta_residue_one : Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by
  exact hurwitzZetaEven_residue_one 0

/-- The residue of `ζ(s)` at `s = 1` is equal to 1, expressed using `tsum`. -/
theorem tendsto_sub_mul_tsum_nat_cpow :
    Tendsto (fun s : ℂ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℂ) ^ s) (𝓝[{s | 1 < re s}] 1) (𝓝 1) := by
  refine (tendsto_nhdsWithin_mono_left ?_ riemannZeta_residue_one).congr' ?_
  · simp
  · filter_upwards [eventually_mem_nhdsWithin] with s hs using
      congr_arg _ <| zeta_eq_tsum_one_div_nat_cpow hs

/-- The residue of `ζ(s)` at `s = 1` is equal to 1 expressed using `tsum` and for a
real variable. -/
theorem tendsto_sub_mul_tsum_nat_rpow :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℝ) ^ s) (𝓝[>] 1) (𝓝 1) := by
  rw [← tendsto_ofReal_iff, ofReal_one]
  have : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[{s | 1 < re s}] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ ↦ by simp_all)
  apply (tendsto_sub_mul_tsum_nat_cpow.comp this).congr fun s ↦ ?_
  simp only [one_div, Function.comp_apply, ofReal_mul, ofReal_sub, ofReal_one, ofReal_tsum,
    ofReal_inv, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]

/-!
## Conjugation symmetry of the completed Riemann zeta function

We prove `completedRiemannZeta_conj : Λ(conj s) = conj (Λ s)`, the analogue
of `Complex.Gamma_conj` for the completed zeta. Combined with `completedRiemannZeta_one_sub`
this makes the symmetry group of `Λ` on `ℂ` explicit. The proof works in two steps:

1. On the open half-plane `{Re s > 1}`, the Dirichlet series for `Λ`
   converges absolutely and conjugation commutes term-by-term with the
   series, with `Complex.Gamma_conj`, and with `cpow` of the positive real
   bases `π` and `n : ℕ` (via `Complex.conj_cpow`).
2. Both sides extend to entire (resp. meromorphic-with-explicit-poles)
   functions of `s`; the identity principle (`AnalyticOnNhd.eq_of_eventuallyEq`)
   propagates the equality from `{Re s > 1}` to all of `ℂ`.

The pole-decomposition `completedRiemannZeta_eq` is used to transfer the
result from `Λ₀` (entire) to the full `Λ` (which has simple poles at `0` and `1`).
-/

/-- Helper: conjugation acts equivariantly on `(↑n : ℂ) ^ s`. -/
private lemma conj_natCast_cpow (n : ℕ) (s : ℂ) :
    conj ((n : ℂ) ^ s) = (n : ℂ) ^ (conj s) := by
  by_cases h : n = 0
  · subst h
    simp_rw [Nat.cast_zero]
    by_cases hs : s = 0
    · simp [hs]
    · have hcs : conj s ≠ 0 := by simp [hs]
      rw [zero_cpow hs, zero_cpow hcs, map_zero]
  · have harg : (n : ℂ).arg ≠ Real.pi := by
      rw [natCast_arg]
      exact ne_of_lt Real.pi_pos
    have hcn : conj ((n : ℂ)) = (n : ℂ) := by
      rw [show ((n : ℂ) : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.conj_ofReal]
    have key := Complex.conj_cpow (n : ℂ) (conj s) harg
    rw [hcn] at key
    rw [key, Complex.conj_conj]

/-- Helper: conjugation acts equivariantly on `(↑(π : ℝ) : ℂ) ^ s`. -/
private lemma conj_pi_cpow (s : ℂ) :
    conj ((Real.pi : ℂ) ^ s) = (Real.pi : ℂ) ^ (conj s) := by
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact ne_of_lt Real.pi_pos
  have hcpi : conj ((Real.pi : ℂ)) = (Real.pi : ℂ) := Complex.conj_ofReal _
  have key := Complex.conj_cpow (Real.pi : ℂ) (conj s) harg
  rw [hcpi] at key
  rw [key, Complex.conj_conj]

/-- The Dirichlet series for `completedRiemannZeta` is conj-equivariant on `{Re s > 1}`. -/
private lemma completedRiemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hcs : 1 < re (conj s) := by rw [Complex.conj_re]; exact hs
  rw [completedZeta_eq_tsum_of_one_lt_re hs, completedZeta_eq_tsum_of_one_lt_re hcs]
  rw [map_mul, map_mul]
  rw [conj_pi_cpow, ← Complex.Gamma_conj, Complex.conj_tsum]
  congr 1
  · congr 1
    · congr 1
      rw [map_div₀, map_neg, Complex.conj_ofNat]
    · congr 1
      rw [map_div₀, Complex.conj_ofNat]
  · apply tsum_congr
    intro n
    simp only [one_div, map_inv₀]
    rw [conj_natCast_cpow]

/-- `completedRiemannZeta₀` is conj-equivariant on `{Re s > 1}`. Derived from the
identity on `Λ` via the pole-decomposition `completedRiemannZeta_eq`. -/
private lemma completedRiemannZeta₀_conj_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  have hcs : 1 < re (conj s) := by rw [Complex.conj_re]; exact hs
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; norm_num at hs
  have hcs0 : conj s ≠ 0 := fun h => by
    apply hs0
    have := congrArg conj h
    rwa [Complex.conj_conj, map_zero] at this
  have hcs1 : conj s ≠ 1 := fun h => by
    apply hs1
    have := congrArg conj h
    rwa [Complex.conj_conj, map_one] at this
  have ce1 : completedRiemannZeta (conj s) =
      completedRiemannZeta₀ (conj s) - 1 / (conj s) - 1 / (1 - conj s) :=
    completedRiemannZeta_eq (conj s)
  have ce2 : completedRiemannZeta s =
      completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
    completedRiemannZeta_eq s
  have key := completedRiemannZeta_conj_of_one_lt_re hs
  rw [ce1, ce2] at key
  rw [show conj (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) =
      conj (completedRiemannZeta₀ s) - conj (1 / s) - conj (1 / (1 - s)) by
    rw [map_sub, map_sub]] at key
  have c1 : conj ((1 : ℂ) / s) = 1 / conj s := by rw [map_div₀, map_one]
  have c2 : conj ((1 : ℂ) / (1 - s)) = 1 / (1 - conj s) := by
    rw [map_div₀, map_one, map_sub, map_one]
  rw [c1, c2] at key
  linear_combination key

/-- The function `s ↦ conj (completedRiemannZeta₀ (conj s))` is entire. -/
private lemma differentiable_conj_completedZeta₀_conj :
    Differentiable ℂ (fun s => conj (completedRiemannZeta₀ (conj s))) := by
  intro s
  have := (differentiable_completedZeta₀ (conj s)).conj_conj
  rw [Complex.conj_conj] at this
  exact this

/-- **Schwarz reflection for the entire piece `completedRiemannZeta₀`**: for every `s : ℂ`,
`completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s)`. This is the
conj-equivariance counterpart of the functional equation `completedRiemannZeta₀_one_sub`,
and the analogue of `Complex.Gamma_conj` for the completed zeta. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  suffices h_eq :
      (fun z => conj (completedRiemannZeta₀ (conj z))) = completedRiemannZeta₀ by
    have := congrFun h_eq (conj s)
    rw [Complex.conj_conj] at this
    exact this.symm
  have hf : AnalyticOnNhd ℂ (fun z => conj (completedRiemannZeta₀ (conj z))) Set.univ :=
    fun z _ => differentiable_conj_completedZeta₀_conj.analyticAt z
  have hg : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    fun z _ => differentiable_completedZeta₀.analyticAt z
  have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < re z} := by
    rw [Set.mem_setOf_eq, show ((2 : ℂ).re = 2) by norm_num]; norm_num
  have hopen : IsOpen {z : ℂ | 1 < re z} :=
    isOpen_lt continuous_const Complex.continuous_re
  refine AnalyticOnNhd.eq_of_eventuallyEq hf hg (z₀ := 2) ?_
  filter_upwards [hopen.mem_nhds h2] with z hz
  have key := completedRiemannZeta₀_conj_of_one_lt_re hz
  have := congrArg conj key
  rw [Complex.conj_conj] at this
  exact this

/-- **Schwarz reflection for the completed Riemann zeta function**: for every `s : ℂ`,
`completedRiemannZeta (conj s) = conj (completedRiemannZeta s)`. This is the
conj-equivariance counterpart of the functional equation `completedRiemannZeta_one_sub`.
The proof reduces to `completedRiemannZeta₀_conj` via the pole-decomposition
`completedRiemannZeta_eq`. -/
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq (conj s), completedRiemannZeta₀_conj]
  rw [completedRiemannZeta_eq s, map_sub, map_sub]
  congr 1
  · congr 1
    rw [map_div₀, map_one]
  · rw [map_div₀, map_one, map_sub, map_one]
