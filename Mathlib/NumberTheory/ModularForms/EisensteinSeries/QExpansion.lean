/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Ring.Commute
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Complex.Asymptotics
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.ArithMult.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Neighborhoods

/-!
# Eisenstein series q-expansions

We give the q-expansion of Eisenstein series of weight `k` and level 1. In particular, we prove
`EisensteinSeries.q_expansion_bernoulli` which says that for even `k` with `3 ≤ k`
Eisenstein series can be written as `1 - (2k / bernoulli k) ∑' n, σ_{k-1}(n) q^n` where
`q = exp(2πiz)` and `σ_{k-1}(n)` is the sum of the `(k-1)`-th powers of the divisors of `n`.
We need `k` to be even so that the Eisenstein series are non-zero and we require `k ≥ 3` so that
the series converges absolutely.

We also identify the q-expansion coefficients as a `PowerSeries` via
`EisensteinSeries.E_qExpansion_coeff`, and use this to prove that the normalised Eisenstein series
is non-zero (`EisensteinSeries.E_ne_zero`).

The proof relies on the identity
`∑' n : ℤ, 1 / (z + n) ^ (k + 1) = ((-2πi)^(k+1) / k!) ∑' n : ℕ, n^k q^n` which comes from
differentiating the expansion of `π cot(πz)` in terms of exponentials. Since our Eisenstein series
are defined as sums over coprime integer pairs, we also need to relate these to sums over all pairs
of integers, which is done in `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`. This then
gives the q-expansion with a Riemann zeta factor, which we simplify using the formula for
`ζ(k)` in terms of Bernoulli numbers to get the final result.

-/

public section

open Set Metric TopologicalSpace Function Filter Complex ArithmeticFunction
  ModularForm EisensteinSeries

open scoped Topology Real Nat Complex Pointwise ArithmeticFunction.sigma

open _root_.UpperHalfPlane hiding I

local notation "ℍₒ" => upperHalfPlaneSet

private lemma iteratedDerivWithin_cexp_aux (k m : ℕ) (p : ℝ) {S : Set ℂ} (hs : IsOpen S) :
    EqOn (iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * m * s / p)) S)
    (fun s ↦ (2 * π * I * m / p) ^ k * cexp (2 * π * I * m * s / p)) S := by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  intro x hx
  have : (fun s ↦ cexp (2 * π * I * m * s / p)) = fun s ↦ cexp (((2 * π * I * m) / p) * s) := by
    ext z
    ring_nf
  simp only [this, iteratedDeriv_cexp_const_mul]
  ring_nf

private lemma aux_IsBigO_mul (k l : ℕ) (p : ℝ) {f : ℕ → ℂ}
    (hf : f =O[atTop] fun n ↦ ((n ^ l) : ℝ)) :
    (fun n ↦ f n * (2 * π * I * n / p) ^ k) =O[atTop] fun n ↦ (↑(n ^ (l + k)) : ℝ) := by
  have h0 : (fun n : ℕ ↦ (2 * π * I * n / p) ^ k) =O[atTop] fun n ↦ ((n ^ k) : ℝ) := by
    have h1 : (fun n : ℕ ↦ (2 * π * I * n / p) ^ k) =
        fun n : ℕ ↦ ((2 * π * I / p) ^ k) * n ^ k := by
      ext z
      ring
    simpa [h1] using isBigO_ofReal_right.mp (Asymptotics.isBigO_const_mul_self
      ((2 * π * I / p) ^ k) (fun (n : ℕ) ↦ (↑(n ^ k) : ℝ)) atTop)
  simp only [Nat.cast_pow]
  convert hf.mul h0
  ring

open BoundedContinuousFunction in
/-- The infinite sum of `k`-th iterated derivative of the complex exponential multiplied by a
function that grows polynomially is absolutely and uniformly convergent. -/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp (k l : ℕ) {f : ℕ → ℂ} {p : ℝ}
    (hp : 0 < p) (hf : f =O[atTop] (fun n ↦ ((n ^ l) : ℝ))) :
    SummableLocallyUniformlyOn (fun n ↦ (f n) •
      iteratedDerivWithin k (fun z ↦ cexp (2 * π * I * z / p) ^ n) ℍₒ) ℍₒ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  have : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hKc)
  let c : ContinuousMap K ℂ := ⟨fun r : K ↦ Complex.exp (2 * π * I * r / p), by fun_prop⟩
  let r : ℝ := ‖mkOfCompact c‖
  have hr : ‖r‖ < 1 := by
    simp only [norm_norm, r, norm_lt_iff_of_compact Real.zero_lt_one, mkOfCompact_apply,
      ContinuousMap.coe_mk, c]
    intro x
    have h1 : cexp (2 * π * I * (x / p)) = cexp (2 * π * I * x / p) := by
      ring_nf
    simpa using h1 ▸ norm_exp_two_pi_I_lt_one ⟨((x : ℂ) / p), by aesop⟩
  refine ⟨_, by simpa using (summable_norm_mul_geometric_of_norm_lt_one' hr
    (Asymptotics.isBigO_norm_left.mpr (aux_IsBigO_mul k l p hf))), fun n z hz ↦ ?_⟩
  have h0 := pow_le_pow_left₀ (norm_nonneg _) (norm_coe_le_norm (mkOfCompact c) ⟨z, hz⟩) n
  simp only [norm_mkOfCompact, mkOfCompact_apply, ContinuousMap.coe_mk, ← exp_nsmul', Pi.smul_apply,
    iteratedDerivWithin_cexp_aux k n p isOpen_upperHalfPlaneSet (hK hz), smul_eq_mul,
    norm_mul, norm_pow, Complex.norm_div, norm_ofNat, norm_real, Real.norm_eq_abs, norm_I, mul_one,
    norm_natCast, abs_norm, ge_iff_le, r, c] at *
  rw [← mul_assoc]
  gcongr
  convert h0
  rw [← norm_pow, ← exp_nsmul']

/-- This is a version of `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp` for level one
and q-expansion coefficients all `1`. -/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_cexp (k : ℕ) :
    SummableLocallyUniformlyOn
      (fun n ↦ iteratedDerivWithin k (fun z ↦ cexp (2 * π * I * z) ^ n) ℍₒ) ℍₒ := by
  have h0 : (fun n : ℕ ↦ (1 : ℂ)) =O[atTop] fun n ↦ ((n ^ 1) : ℝ) := by
    simp only [Asymptotics.isBigO_iff, norm_one, norm_pow, Real.norm_natCast,
      eventually_atTop, ge_iff_le]
    exact ⟨1, 1, fun b hb ↦ by norm_cast; simp [hb]⟩
  simpa using summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp k 1 (p := 1)
    (by norm_num) h0

lemma differentiableAt_iteratedDerivWithin_cexp (n a : ℕ) {s : Set ℂ} (hs : IsOpen s)
    {r : ℂ} (hr : r ∈ s) : DifferentiableAt ℂ
      (iteratedDerivWithin a (fun z ↦ cexp (2 * π * I * z) ^ n) s) r := by
  apply DifferentiableOn.differentiableAt _ (hs.mem_nhds hr)
  suffices DifferentiableOn ℂ (iteratedDeriv a (fun z ↦ cexp (2 * π * I * z) ^ n)) s by
    apply this.congr (iteratedDerivWithin_of_isOpen hs)
  fun_prop

lemma iteratedDerivWithin_tsum_cexp_eq (k : ℕ) (z : ℍ) :
    iteratedDerivWithin k (fun z ↦ ∑' n : ℕ, cexp (2 * π * I * z) ^ n) ℍₒ z =
    ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * s) ^ n) ℍₒ z := by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet (by simpa using z.2)]
  · exact fun x hx ↦ summable_geometric_iff_norm_lt_one.mpr
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩)
  · exact fun n _ _ ↦ summableLocallyUniformlyOn_iteratedDerivWithin_cexp n
  · exact fun n l z hl hz ↦ differentiableAt_iteratedDerivWithin_cexp n l
      isOpen_upperHalfPlaneSet hz

lemma contDiffOn_tsum_cexp (k : ℕ∞) :
    ContDiffOn ℂ k (fun z : ℂ ↦ ∑' n : ℕ, cexp (2 * π * I * z) ^ n) ℍₒ :=
  contDiffOn_of_differentiableOn_deriv fun m _ z hz ↦
  (((summableLocallyUniformlyOn_iteratedDerivWithin_cexp m).differentiableOn
  isOpen_upperHalfPlaneSet (fun n _ hz ↦ differentiableAt_iteratedDerivWithin_cexp n m
  isOpen_upperHalfPlaneSet hz)) z hz).congr (fun z hz ↦ iteratedDerivWithin_tsum_cexp_eq m ⟨z, hz⟩)
  (iteratedDerivWithin_tsum_cexp_eq m ⟨z, hz⟩)

private lemma iteratedDerivWithin_tsum_exp_aux_eq {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    iteratedDerivWithin k (fun z ↦ ((π * I) -
    (2 * π * I) * ∑' n : ℕ, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) ^ (k + 1) * ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
  have : iteratedDerivWithin k (fun z ↦ ((π * I) -
    (2 * π * I) * ∑' n : ℕ, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) * ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * s) ^ n) ℍₒ z := by
    rw [iteratedDerivWithin_const_sub hk, iteratedDerivWithin_fun_neg,
      iteratedDerivWithin_const_mul (by simpa using z.2) (isOpen_upperHalfPlaneSet.uniqueDiffOn)]
    · simp only [iteratedDerivWithin_tsum_cexp_eq, neg_mul]
    · exact (contDiffOn_tsum_cexp k).contDiffWithinAt (by simpa using z.2)
  have h : -(2 * π * I * (2 * π * I) ^ k) * ∑' (n : ℕ), n ^ k * cexp (2 * π * I * z) ^ n =
        -(2 * π * I) * ∑' n : ℕ, (2 * π * I * n) ^ k * cexp (2 * π * I * z) ^ n := by
    simp_rw [← tsum_mul_left]
    congr
    ext y
    ring
  simp only [this, neg_mul, pow_succ', h, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
    OfNat.ofNat_ne_zero, ofReal_eq_zero, Real.pi_ne_zero, or_self, I_ne_zero, or_false]
  congr
  ext n
  have := exp_nsmul' (p := 1) (a := 2 * π * I) (n := n)
  simp_rw [div_one] at this
  simpa [this, UpperHalfPlane.coe] using
    iteratedDerivWithin_cexp_aux k n 1 isOpen_upperHalfPlaneSet z.2

/-- This is one key identity relating infinite series to q-expansions which shows that
`∑' n, 1 / (z + n) ^ (k + 1) = ((-2 π I) ^ (k + 1) / k !) * ∑' n, n ^ k q ^n` where
`q = cexp (2 π I z)`. -/
theorem EisensteinSeries.qExpansion_identity {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) = ((-2 * π * I) ^ (k + 1) / k !) *
    ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
  have : (-1) ^ k * k ! * ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) =
    -(2 * π * I) ^ (k + 1) * ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
    rw [← iteratedDerivWithin_tsum_exp_aux_eq hk z,
      ← iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow hk (by simpa using z.2)]
    exact iteratedDerivWithin_congr (fun x hx ↦ by (simpa using pi_mul_cot_pi_q_exp ⟨x, hx⟩))
      (by simpa using z.2)
  simp_rw [(eq_inv_mul_iff_mul_eq₀ (by simp [Nat.factorial_ne_zero])).mpr this, ← tsum_mul_left]
  congr
  ext n
  rw [show (-2 * π * I) ^ (k + 1) = (-1) ^ (k + 1) * (2 * π * I) ^ (k + 1) by rw [← neg_pow]; ring]
  field_simp
  ring_nf
  simp [Nat.mul_two]

lemma summable_pow_mul_cexp (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ ↦ (c : ℂ) ^ k * cexp (2 * π * I * e * z) ^ c := by
  have he : 0 < (e * (z : ℂ)).im := by
    simpa using z.2
  apply ((summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp 0 k (p := 1)
    (f := fun n ↦ (n ^ k : ℂ)) (by norm_num)
    (by simp [← Complex.isBigO_ofReal_right, Asymptotics.isBigO_refl])).summable he).congr
  grind [ofReal_one, iteratedDerivWithin_zero, Pi.smul_apply, smul_eq_mul]

/-- This is a version of `EisensteinSeries.qExpansion_identity` for positive naturals,
which shows that  `∑' n, 1 / (z + n) ^ (k + 1) = ((-2 π I) ^ (k + 1) / k !) * ∑' n : ℕ+, n ^ k q ^n`
where `q = cexp (2 π I z)`. -/
theorem EisensteinSeries.qExpansion_identity_pnat {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) = ((-2 * π * I) ^ (k + 1) / k !) *
    ∑' n : ℕ+, n ^ k * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [EisensteinSeries.qExpansion_identity hk z, ← tsum_zero_pnat_eq_tsum_nat]
  · simp [show k ≠ 0 by grind]
  · apply (summable_pow_mul_cexp k 1 z).congr
    simp

lemma summable_eisSummand {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    Summable (eisSummand k · z) :=
  summable_norm_iff.mp <| summable_norm_eisSummand (Int.toNat_le.mp hk) z

lemma summable_prod_eisSummand {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    Summable fun x : ℤ × ℤ ↦ eisSummand k ![x.1, x.2] z := by
  refine (finTwoArrowEquiv ℤ).summable_iff.mp <| (summable_eisSummand hk z).congr (fun v ↦ ?_)
  simp [show ![v 0, v 1] = v from List.ofFn_inj.mp rfl]

lemma tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    ∑' v, eisSummand k v z = 2 * riemannZeta k + 2 * ((-2 * π * I) ^ k / (k - 1)!) *
    ∑' (n : ℕ+), σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq, finTwoArrowEquiv_symm_apply,
    Summable.tsum_prod (summable_prod_eisSummand hk z),
    tsum_int_eq_zero_add_two_mul_tsum_pnat (fun n ↦ ?h₁)
      (by simpa using (summable_prod_eisSummand hk z).prod)]
  case h₁ =>
    nth_rewrite 1 [← tsum_comp_neg]
    exact tsum_congr fun y ↦ by simp [eisSummand, ← neg_add _ (y : ℂ), -neg_add_rev, hk2.neg_pow]
  have H (b : ℕ+) := qExpansion_identity_pnat (k := k - 1) (by grind) ⟨b * z, by simpa using z.2⟩
  simp_rw [show k - 1 + 1 = k by grind, one_div] at H
  simp only [neg_mul] at H
  rw [nsmul_eq_mul, mul_assoc]
  congr
  · simp [eisSummand, two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by grind) hk2]
  · suffices ∑' (m : ℕ+) (n : ℕ+), (n : ℕ) ^ (k - 1) * cexp (2 * π * I * (m * z)) ^ (n : ℕ) =
        ∑' (m : ℕ+) (n : ℕ+), (n : ℕ) ^ (k - 1) * cexp (2 * π * I * z) ^ (m * n : ℕ) by
      simp [eisSummand, H, tsum_mul_left,
        ← tsum_prod_pow_eq_tsum_sigma (k - 1) (norm_exp_two_pi_I_lt_one z), this]
    simp_rw [← Complex.exp_nat_mul]
    exact tsum_congr₂ (fun m n ↦ by push_cast; ring_nf)

lemma eisSummand_of_gammaSet_eq_divIntMap (k : ℤ) (z : ℍ) {n : ℕ} (v : gammaSet 1 n 0) :
    eisSummand k v z = ((n : ℂ) ^ k)⁻¹ * eisSummand k (divIntMap n v) z := by
  simp_rw [eisSummand]
  nth_rw 1 2 [gammaSet_eq_gcd_mul_divIntMap v.2]
  simp [← mul_inv, ← mul_zpow, mul_add, mul_assoc]

lemma tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    ∑' v : Fin 2 → ℤ, eisSummand k v z = riemannZeta k * eisensteinSeries (N := 1) 0 k z := by
  have hk1 : 1 < k := by grind
  have hk2 : 3 ≤ (k : ℤ) := mod_cast hk
  simp_rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq, gammaSetDivGcdSigmaEquiv_symm_eq]
  rw [eisensteinSeries, Summable.tsum_sigma ?hsumm, zeta_nat_eq_tsum_of_gt_one hk1,
    tsum_mul_tsum_of_summable_norm (by simp [hk1]) ((summable_norm_eisSummand hk2 z).subtype _)]
  case hsumm =>
    exact gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr (summable_norm_eisSummand hk2 z).of_norm
      |>.congr <| by simp
  simp_rw [one_div]
  rw [Summable.tsum_prod' ?h₁ fun b ↦ ?h₂]
  case h₁ =>
    exact summable_mul_of_summable_norm (f := fun (n : ℕ) ↦ ((n : ℂ) ^ k)⁻¹)
      (g := fun (v : gammaSet 1 1 0) ↦ eisSummand k v z) (by simp [hk1])
      ((summable_norm_eisSummand hk2 z).subtype _)
  case h₂ =>
    simpa using ((summable_norm_eisSummand hk2 z).subtype _).of_norm.mul_left (a := ((b : ℂ) ^ k)⁻¹)
  refine tsum_congr fun b ↦ ?_
  rcases eq_or_ne b 0 with rfl | hb
  · simp [show ((0 : ℂ) ^ k)⁻¹ = 0 by aesop, eisSummand_of_gammaSet_eq_divIntMap]
  · have : NeZero b := ⟨hb⟩
    simpa [eisSummand_of_gammaSet_eq_divIntMap k z, tsum_mul_left, hb]
      using (gammaSetDivGcdEquiv b).tsum_eq (eisSummand k · z)

/-- The q-Expansion of normalised Eisenstein series of level one with `riemannZeta` term. -/
lemma EisensteinSeries.q_expansion_riemannZeta {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    E hk z = 1 + (riemannZeta k)⁻¹ * (-2 * π * I) ^ k / (k - 1)! *
    ∑' n : ℕ+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℤ) := by
  have : eisensteinSeriesMF (Int.toNat_le.mp hk) 0 z = eisensteinSeriesSIF (N := 1) 0 k z := rfl
  rw [E, ModularForm.IsGLPos.smul_apply, this, eisensteinSeriesSIF_apply 0 k z, eisensteinSeries]
  have HE1 := tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow hk hk2 z
  have HE2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z
  have z2 : riemannZeta k ≠ 0 := riemannZeta_ne_zero_of_one_lt_re <| by norm_cast; grind
  simp [eisSummand, eisensteinSeries, ← inv_mul_eq_iff_eq_mul₀ z2] at HE1 HE2 ⊢
  grind

private lemma eisensteinSeries_coeff_identity {k : ℕ} (hk2 : Even k) (hkn0 : k ≠ 0) :
    (riemannZeta k)⁻¹ * (-2 * π * I) ^ k / (k - 1)! = -(2 * k / bernoulli k) := by
  have h2 : k = 2 * (k / 2 - 1 + 1) := by grind
  set m := k / 2 - 1
  rw [h2, Nat.cast_mul 2 (m + 1), Nat.cast_two, riemannZeta_two_mul_nat (show m + 1 ≠ 0 by grind),
    show (2 * (m + 1))! = 2 * (m + 1) * (2 * m + 1)! by grind [Nat.factorial_succ],
    show 2 * (m + 1) - 1 = 2 * m + 1 by grind, mul_pow, mul_pow, pow_mul I, I_sq]
  norm_cast
  simp [field]
  grind

/-- The q-Expansion of normalised Eisenstein series of level one with `bernoulli` term. -/
lemma EisensteinSeries.q_expansion_bernoulli {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    E hk z = 1 - (2 * k / bernoulli k) *
    ∑' n : ℕ+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℤ) := by
  convert q_expansion_riemannZeta hk hk2 z using 1
  rw [eisensteinSeries_coeff_identity hk2 (by grind), neg_mul, ← sub_eq_add_neg]

section NonZero

open ModularFormClass

local notation "𝕢" => Periodic.qParam

/-- Summability of the divisor-sum q-expansion series `∑ σ_{k-1}(n) q^n`. -/
private lemma summable_sigma_mul_cexp_pow {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    Summable fun n : ℕ ↦ (σ (k - 1) n : ℂ) * cexp (2 * π * I * z) ^ n := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one k (norm_exp_two_pi_I_lt_one z))
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ (k - 1) n).trans_eq (by congr 1; omega)

/-- The q-expansion coefficients of the normalised Eisenstein series `E k`: the constant term is
`1` and for `m ≥ 1` the `m`-th coefficient is `-(2k / B_k) * σ_{k-1}(m)` where `B_k` is the
`k`-th Bernoulli number. -/
lemma EisensteinSeries.E_qExpansion_coeff {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (m : ℕ) :
    (qExpansion 1 (E hk)).coeff m =
    if m = 0 then 1 else -(2 * k / bernoulli k : ℂ) * (σ (k - 1) m) := by
  set β : ℂ := -(2 * k / bernoulli k : ℂ)
  set c : ℕ → ℂ := fun m ↦ if m = 0 then 1 else β * ↑(σ (k - 1) m)
  suffices ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 (1 : ℝ) τ ^ m) (E hk τ) from
    (qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL2Z this m).symm
  intro τ
  have hS : Summable fun n : ℕ ↦ (σ (k - 1) (n + 1) : ℂ) * cexp (2 * π * I * τ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow (by omega) τ)
  rw [← hasSum_nat_add_iff' 1]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, smul_eq_mul, Finset.range_one,
    ite_mul, one_mul, Finset.sum_singleton, pow_zero, c]
  have hval : E hk τ - 1 = β * ∑' n : ℕ, (σ (k - 1) (n + 1)) * cexp (2 * π * I * τ) ^ (n + 1) := by
    have := q_expansion_bernoulli hk hk2 τ
    simp_rw [zpow_natCast] at this
    rw [this, ← tsum_pnat_eq_tsum_succ (f := fun n ↦ (σ (k - 1) n : ℂ) * cexp (2 * π * I * τ) ^ n)]
    ring
  rw [hval]
  convert (hS.mul_left β).hasSum using 1
  · grind [Periodic.qParam, ofReal_one, div_one]
  · rw [tsum_mul_left]

/-- The q-expansion constant coefficient of the normalised Eisenstein series `E k` is `1`. -/
lemma EisensteinSeries.E_qExpansion_coeff_zero {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    (qExpansion 1 (E hk)).coeff 0 = 1 := by
  simpa using E_qExpansion_coeff hk hk2 0

/-- Normalised Eisenstein series of even weight `k ≥ 3` are non-zero. -/
theorem EisensteinSeries.E_ne_zero {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : E hk ≠ 0 :=
  fun h ↦ one_ne_zero <| (E_qExpansion_coeff_zero hk hk2).symm.trans (by simp [h, qExpansion_zero])

end NonZero
