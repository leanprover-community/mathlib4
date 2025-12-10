/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Meromorphic.Order

/-!

# Weierstrass `℘` functions

## Main definitions and results
- `PeriodPair.weierstrassP`: The Weierstrass `℘`-function associated to a pair of periods.
- `PeriodPair.hasSumLocallyUniformly_weierstrassP`:
  The summands of `℘` sums to `℘` locally uniformly.
- `PeriodPair.differentiableOn_weierstrassP`: `℘` is differentiable away from the lattice points.
- `PeriodPair.weierstrassP_add_coe`: The Weierstrass `℘`-function is periodic.
- `PeriodPair.weierstrassP_neg`: The Weierstrass `℘`-function is even.

- `PeriodPair.derivWeierstrassP`:
  The derivative of the Weierstrass `℘`-function associated to a pair of periods.
- `PeriodPair.hasSumLocallyUniformly_derivWeierstrassP`:
  The summands of `℘'` sums to `℘'` locally uniformly.
- `PeriodPair.differentiableOn_derivWeierstrassP`:
  `℘'` is differentiable away from the lattice points.
- `PeriodPair.derivWeierstrassP_add_coe`: `℘'` is periodic.
- `PeriodPair.weierstrassP_neg`: `℘'` is odd.
- `PeriodPair.deriv_weierstrassP`: `deriv ℘ = ℘'`. This is true globally because of junk values.

## tags

Weierstrass p-functions, Weierstrass p functions

-/

@[expose] public section

open Module

section

open scoped NNReal

theorem Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a : ℂ) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x) ^ a)
      (.ofScalars ℂ fun n ↦ Ring.choose (a + n - 1) n) 0 1 := by
  have H : ((binomialSeries ℂ (-a)).compContinuousLinearMap (-1)) =
      .ofScalars ℂ fun n ↦ Ring.choose (a + n - 1) n := by
    ext n; simp [FormalMultilinearSeries.compContinuousLinearMap, binomialSeries, Ring.choose_neg,
      Units.smul_def, Int.coe_negOnePow_natCast, ← pow_add, ← mul_assoc]
  have : HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ (-a)) (binomialSeries ℂ (-a : ℂ)) (-0) 1 := by
    simpa using one_add_cpow_hasFPowerSeriesOnBall_zero
  simpa [Complex.cpow_neg, Function.comp_def, ← sub_eq_add_neg, H] using
    this.compContinuousLinearMap (u := -1) (x := (0 : ℂ))

theorem Complex.one_div_one_sub_pow_hasFPowerSeriesOnBall_zero (a : ℕ) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x) ^ (a + 1))
      (.ofScalars ℂ (𝕜 := ℂ) fun n ↦ ↑(Nat.choose (a + n) a)) 0 1 := by
  convert one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a + 1) using 3 with z n
  · norm_cast
  · rw [eq_comm, add_right_comm, add_sub_cancel_right, ← Nat.cast_add,
      Ring.choose_natCast, Nat.choose_symm_add]

theorem Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero (a : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (z - x) ^ (a + 1))
      (.ofScalars ℂ (𝕜 := ℂ) fun n ↦ (z ^ (n + a + 1))⁻¹ * ↑(Nat.choose (a + n) a)) 0 ‖z‖ₑ := by
  have := one_div_one_sub_pow_hasFPowerSeriesOnBall_zero a
  rw [← map_zero (z⁻¹ • 1 : ℂ →L[ℂ] ℂ)] at this
  have := this.compContinuousLinearMap
  have H : 1 / ‖(z⁻¹ • 1 : ℂ →L[ℂ] ℂ)‖ₑ = ‖z‖ₑ := by simp [enorm_smul, enorm_inv, hz]
  simp only [one_div, ContinuousLinearMap.coe_smul', H, Function.comp_def] at this
  convert (this.const_smul (c := (z ^ (a + 1))⁻¹)).congr ?_ using 2
  · ext n
    simp only [FormalMultilinearSeries.smul_apply, ContinuousMultilinearMap.smul_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp [add_assoc, pow_add _ _ (a + 1), mul_assoc]
  · intro w hw
    simp [← mul_inv_rev, ← mul_pow, sub_mul, mul_right_comm _ w, hz]

theorem Complex.one_div_sub_hasFPowerSeriesOnBall_zero {z : ℂ} (hz : z ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (z - x)) (.ofScalars ℂ fun n ↦ (z ^ (n + 1))⁻¹) 0 ‖z‖ₑ := by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hz

theorem Complex.one_div_sub_sq_hasFPowerSeriesOnBall_zero {z : ℂ} (hz : z ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (z - x) ^ 2)
      (.ofScalars ℂ fun n ↦ (z ^ (n + 2))⁻¹ * (n + 1)) 0 ‖z‖ₑ := by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hz

theorem Complex.one_div_one_sub_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x : ℂ)) (.ofScalars (𝕜 := ℂ) ℂ 1) 0 1 := by
  simpa using one_div_sub_hasFPowerSeriesOnBall_zero (z := 1)

theorem Complex.one_div_one_sub_sq_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x : ℂ) ^ 2) (.ofScalars ℂ fun n ↦ (n + 1 : ℂ)) 0 1 := by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (z := 1)

/-- `∑ (ai + b) zⁱ = (b - a) / (1 - z) + a / (1 - z)²` -/
theorem Complex.hasFPowerSeriesOnBall_linear_zero (a b : ℂ) :
    HasFPowerSeriesOnBall (fun x ↦ (b - a) / (1 - x) + a / (1 - x) ^ 2)
      (.ofScalars ℂ (a * · + b)) 0 1 := by
  convert (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
    (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a)) using 2
  · simp [div_eq_mul_inv]
  · ext; simp; ring

theorem Real.one_div_sub_pow_hasFPowerSeriesOnBall_zero (a : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (r - x) ^ (a + 1))
      (.ofScalars ℝ (𝕜 := ℝ) fun n ↦ (r ^ (n + a + 1))⁻¹ * ↑(Nat.choose (a + n) a)) 0 ‖r‖ₑ := by
  have := (Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero a (z := r)
    (by simpa)).restrictScalars (𝕜 := ℝ)
  rw [← Complex.ofRealCLM.map_zero] at this
  convert (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap) using 2
  · simp [-Complex.inv_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_sub]
  · ext n
    simp [Function.comp_def, -FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    simp [-Complex.inv_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  · simp [enorm_eq_nnnorm]

theorem Real.one_div_sub_hasFPowerSeriesOnBall_zero {r : ℝ} (hr : r ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (r - x)) (.ofScalars ℝ fun n ↦ (r ^ (n + 1))⁻¹) 0 ‖r‖ₑ := by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hr

theorem Real.one_div_sub_sq_hasFPowerSeriesOnBall_zero {r : ℝ} (hr : r ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (r - x) ^ 2)
      (.ofScalars ℝ fun n ↦ (r ^ (n + 2))⁻¹ * (n + 1)) 0 ‖r‖ₑ := by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hr

theorem Real.one_div_one_sub_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x)) (.ofScalars (𝕜 := ℝ) ℝ 1) 0 1 := by
  simpa using one_div_sub_hasFPowerSeriesOnBall_zero (r := 1)

theorem Real.one_div_one_sub_sq_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x) ^ 2) (.ofScalars ℝ fun n ↦ (n + 1 : ℝ)) 0 1 := by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (r := 1)

/-- `∑ (ai + b) zⁱ = (b - a) / (1 - z) + a / (1 - z)²` -/
theorem Real.hasFPowerSeriesOnBall_linear_zero (a b : ℝ) :
    HasFPowerSeriesOnBall (fun x ↦ (b - a) / (1 - x) + a / (1 - x) ^ 2)
      (.ofScalars ℝ (a * · + b)) 0 1 := by
  convert (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
    (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a)) using 2
  · simp [div_eq_mul_inv]
  · ext; simp; ring

lemma FormalMultilinearSeries.ofScalars_sub {𝕜 : Type*} (E : Type*) [Field 𝕜] [Ring E] [Algebra 𝕜 E]
    [TopologicalSpace E] [IsTopologicalRing E] (c c' : ℕ → 𝕜) :
    ofScalars E (c - c') = ofScalars E c - ofScalars E c' := by ext; simp [ofScalars, sub_smul]

lemma Complex.one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero (w x : ℂ) (hw : w ≠ x) :
    HasFPowerSeriesOnBall (fun z ↦ 1 / (z - w) ^ 2 - 1 / w ^ 2) (.ofScalars ℂ
      fun i ↦ (i + 1) * (w - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (w ^ (-2 : ℤ)) 0) x ‖w - x‖ₑ := by
  rw [← Pi.sub_def, ← Pi.sub_def, FormalMultilinearSeries.ofScalars_sub]
  refine .sub ?_ ?_
  · simpa only [sub_sub_sub_cancel_right, zero_add, sub_sq_comm w, zpow_neg, zpow_natCast, mul_comm]
      using (Complex.one_div_sub_sq_hasFPowerSeriesOnBall_zero
        (z := w - x) (by simp [sub_eq_zero, hw])).comp_sub x
  · convert hasFPowerSeriesOnBall_const.mono _ le_top
    · ext (_|_) <;> simp [zpow_ofNat]
    · simpa [sub_eq_zero]

end

noncomputable section

/-- A pair of `ℝ`-linearly independent complex numbers.
They span the period lattice in `lattice`,
and are the periods of the elliptic functions we shall construct. -/
structure PeriodPair : Type where
  /-- The first period in a `PeriodPair`. -/
  ω₁ : ℂ
  /-- The second period in a `PeriodPair`. -/
  ω₂ : ℂ
  indep : LinearIndependent ℝ ![ω₁, ω₂]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (L : PeriodPair)

namespace PeriodPair

/-- The `ℝ`-basis of `ℂ` determined by a pair of periods. -/
protected def basis : Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank L.indep (by simp)

@[simp] lemma basis_zero : L.basis 0 = L.ω₁ := by simp [PeriodPair.basis]
@[simp] lemma basis_one : L.basis 1 = L.ω₂ := by simp [PeriodPair.basis]

/-- The lattice spanned by a pair of periods. -/
def lattice : Submodule ℤ ℂ := Submodule.span ℤ {L.ω₁, L.ω₂}

lemma mem_lattice {L : PeriodPair} {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, m * L.ω₁ + n * L.ω₂ = x := by
  simp only [lattice, Submodule.mem_span_pair, zsmul_eq_mul]

lemma ω₁_mem_lattice : L.ω₁ ∈ L.lattice := Submodule.subset_span (by simp)
lemma ω₂_mem_lattice : L.ω₂ ∈ L.lattice := Submodule.subset_span (by simp)

lemma mul_ω₁_add_mul_ω₂_mem_lattice {L : PeriodPair} {α β : ℚ} :
    α * L.ω₁ + β * L.ω₂ ∈ L.lattice ↔ α.den = 1 ∧ β.den = 1 := by
  refine ⟨fun H ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · obtain ⟨m, n, e⟩ := mem_lattice.mp H
    have := LinearIndependent.pair_iff.mp L.indep (m - α) (n - β)
      (by simpa using by linear_combination e)
    simp only [sub_eq_zero] at this
    norm_cast at this
    aesop
  · lift α to ℤ using h₁
    lift β to ℤ using h₂
    simp only [Rat.cast_intCast, ← zsmul_eq_mul]
    exact add_mem (Submodule.smul_mem _ _ L.ω₁_mem_lattice)
      (Submodule.smul_mem _ _ L.ω₂_mem_lattice)

lemma ω₁_div_two_notMem_lattice : L.ω₁ / 2 ∉ L.lattice := by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1/2) (β := 0)).not.mpr (by norm_num)

lemma ω₂_div_two_notMem_lattice : L.ω₂ / 2 ∉ L.lattice := by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := 1/2)).not.mpr (by norm_num)

-- helper lemma to connect to the ZLattice API
lemma lattice_eq_span_range_basis :
    L.lattice = Submodule.span ℤ (Set.range L.basis) := by
  have : Finset.univ (α := Fin 2) = {0, 1} := rfl
  rw [lattice, ← Set.image_univ, ← Finset.coe_univ, this]
  simp [Set.image_insert_eq]

instance : DiscreteTopology L.lattice := L.lattice_eq_span_range_basis ▸ inferInstance

instance : IsZLattice ℝ L.lattice := by
  simp_rw [L.lattice_eq_span_range_basis]
  infer_instance

lemma isClosed_lattice : IsClosed (X := ℂ) L.lattice :=
  @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.lattice.toAddSubgroup
    (inferInstanceAs (DiscreteTopology L.lattice))

lemma isClosed_of_subset_lattice {s : Set ℂ} (hs : s ⊆ L.lattice) : IsClosed s := by
  convert L.isClosed_lattice.isClosedMap_subtype_val _
    (isClosed_discrete (α := L.lattice) ((↑) ⁻¹' s))
  convert Set.image_preimage_eq_inter_range.symm using 1
  simpa

lemma isOpen_compl_lattice_diff {s : Set ℂ} : IsOpen (L.lattice \ s)ᶜ :=
  (L.isClosed_of_subset_lattice Set.diff_subset).isOpen_compl

instance : ProperSpace L.lattice := .of_isClosed L.isClosed_lattice

/-- The `ℤ`-basis of the lattice determined by a pair of periods. -/
def latticeBasis : Basis (Fin 2) ℤ L.lattice :=
  (Basis.span (v := ![L.ω₁, L.ω₂]) (L.indep.restrict_scalars' _)).map
    (.ofEq _ _ (by simp [lattice, Set.pair_comm L.ω₂ L.ω₁]))

@[simp] lemma latticeBasis_zero : L.latticeBasis 0 = L.ω₁ := by simp [latticeBasis]
@[simp] lemma latticeBasis_one : L.latticeBasis 1 = L.ω₂ := by simp [latticeBasis]

@[simp] lemma finrank_lattice : finrank ℤ L.lattice = 2 := finrank_eq_card_basis L.latticeBasis

/-- The equivalence from the lattice generated by a pair of periods to `ℤ × ℤ`. -/
def latticeEquivProd : L.lattice ≃ₗ[ℤ] ℤ × ℤ :=
  L.latticeBasis.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _ ≪≫ₗ .finTwoArrow ℤ ℤ

lemma latticeEquiv_symm_apply (x : ℤ × ℤ) :
    (L.latticeEquivProd.symm x).1 = x.1 * L.ω₁ + x.2 * L.ω₂ := by
  simp [latticeEquivProd, Finsupp.linearCombination]
  rfl

open Topology Filter in
lemma hasSumLocallyUniformly_aux (f : L.lattice → ℂ → ℂ)
    (u : ℝ → L.lattice → ℝ) (hu : ∀ r > 0, Summable (u r))
    (hf : ∀ r > 0, ∀ᶠ R in atTop, ∀ x, ‖x‖ < r → ∀ l : L.lattice, ‖l.1‖ = R → ‖f l x‖ ≤ u r l) :
    HasSumLocallyUniformly f (∑' j, f j ·) := by
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_filter]
  intro x
  obtain ⟨r, hr, hr'⟩ : ∃ r, 0 < r ∧ 𝓝 x ≤ 𝓟 (Metric.ball 0 r) :=
    ⟨‖x‖ + 1, by positivity, Filter.le_principal_iff.mpr (Metric.isOpen_ball.mem_nhds (by simp))⟩
  refine .mono_right ?_ hr'
  rw [← tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  refine tendstoUniformlyOn_tsum_of_cofinite_eventually (hu r hr) ?_
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hf r hr)
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intros l hl
  obtain ⟨s, hs, hs'⟩ : ∃ x, ‖x‖ < r ∧ u r l < ‖f l x‖ := by simpa using hl
  simp only [Metric.mem_closedBall, dist_zero_right, AddSubgroupClass.coe_norm]
  contrapose! hs'
  exact hR _ hs'.le _ hs _ rfl

-- Only the asymptotics matter and `10` is just a convenient constant to pick.
lemma weierstrassP_bound (r : ℝ) (hr : r > 0) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) ^ 2 - 1 / l ^ 2‖ ≤ 10 * r * ‖l‖ ^ (-3 : ℝ) := by
  have : s ≠ ↑l := by rintro rfl; exfalso; linarith
  have : 0 < ‖l‖ := by
    suffices l ≠ 0 by simpa
    rintro rfl
    simp only [norm_zero] at h
    linarith
  calc
    _ = ‖(↑l ^ 2 - (s - ↑l) ^ 2) / ((s - ↑l) ^ 2 * ↑l ^ 2)‖ := by
      rw [div_sub_div, one_mul, mul_one]
      · simpa [sub_eq_zero]
      · simpa
    _ = ‖l ^ 2 - (s - l) ^ 2‖ / (‖s - l‖ ^ 2 * ‖l‖ ^ 2) := by simp
    _ ≤ ‖l ^ 2 - (s - l) ^ 2‖ / ((‖l‖ / 2) ^ 2 * ‖l‖ ^ 2) := by
      gcongr
      rw [norm_sub_rev]
      exact .trans (by linarith) (norm_sub_norm_le l s)
    _ = ‖s * (2 * l - s)‖ / (‖l‖ ^ 4 / 4) := by
      congr 1
      · rw [sq_sub_sq]; simp [← sub_add, two_mul, sub_add_eq_add_sub]
      · ring
    _ = (‖s‖ * ‖2 * l - s‖) / (‖l‖ ^ 4 / 4) := by simp
    _ = (4 * ‖s‖ * ‖2 * l - s‖) / ‖l‖ ^ 4 := by field
    _ ≤ (4 * r * (2.5 * ‖l‖)) / ‖l‖ ^ 4 := by
      gcongr (4 * ?_ * ?_) / ‖l‖ ^ 4
      refine (norm_sub_le _ _).trans ?_
      simp only [Complex.norm_mul, Complex.norm_ofNat]
      linarith
    _ = 10 * r / ‖l‖ ^ 3 := by field
    _ = _ := by norm_cast

section weierstrassPExcept

/-- The Weierstrass `℘` function with the `l₀`-term missing.
This is mainly a tool for calculations where one would want to omit a diverging term.
This has the notation `℘[L - l₀]` in the namespace `PeriodPairs`. -/
def weierstrassPExcept (l₀ : ℂ) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2)

@[inherit_doc weierstrassPExcept]
scoped notation3 "℘[" L:max " - " l₀ "]" => weierstrassPExcept L l₀

lemma hasSumLocallyUniformly_weierstrassPExcept (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ if l.1 = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2))
      ℘[L - l₀] := by
  refine L.hasSumLocallyUniformly_aux (u := (10 * · * ‖·‖ ^ (-3 : ℝ))) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simpa using show 0 ≤ 10 * r * (‖↑l‖ ^ 3)⁻¹ by positivity
  · exact weierstrassP_bound r hr s hs l h

lemma hasSum_weierstrassPExcept (l₀ : ℂ) (z : ℂ) :
    HasSum (fun l : L.lattice ↦ if l = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2))
      (℘[L - l₀] z) :=
  (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSum

/- `weierstrassPExcept l₀` is differentiable on non-lattice points and `l₀`. -/
lemma differentiableOn_weierstrassPExcept (l₀ : ℂ) :
    DifferentiableOn ℂ ℘[L - l₀] (L.lattice \ {l₀})ᶜ := by
  refine (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun i hi ↦ ?_) L.isOpen_compl_lattice_diff
  split_ifs
  · simp
  · exact .sub (.div (by fun_prop) (by fun_prop) (by aesop (add simp sub_eq_zero))) (by fun_prop)

lemma weierstrassPExcept_neg (l₀ : ℂ) (z : ℂ) :
    ℘[L - l₀] (-z) = ℘[L - -l₀] z := by
  simp only [weierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  simp
  ring

end weierstrassPExcept

section weierstrassP

/-- The Weierstrass `℘` function. This has the notation `℘[L]` in the namespace `PeriodPairs`. -/
def weierstrassP (z : ℂ) : ℂ := ∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / l ^ 2)

@[inherit_doc weierstrassP] scoped notation3 "℘[" L "]" => weierstrassP L

lemma weierstrassPExcept_add (l₀ : L.lattice) (z : ℂ) :
    ℘[L - l₀] z + (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) = ℘[L] z := by
  trans ℘[L - l₀] z + ∑' i : L.lattice, if i = l₀.1 then (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) else 0
  · simp
  rw [weierstrassPExcept, ← Summable.tsum_add]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *]
  · exact ⟨_, L.hasSum_weierstrassPExcept _ _⟩
  · exact summable_of_finite_support ((Set.finite_singleton l₀).subset (by simp_all))

lemma weierstrassPExcept_def (l₀ : L.lattice) (z : ℂ) :
    ℘[L - l₀] z = ℘[L] z + (1 / l₀.1 ^ 2 - 1 / (z - l₀.1) ^ 2) := by
  rw [← L.weierstrassPExcept_add l₀]
  abel

lemma weierstrassPExcept_of_notMem (l₀ : ℂ) (hl : l₀ ∉ L.lattice) :
    ℘[L - l₀] = ℘[L] := by
  delta weierstrassPExcept weierstrassP
  congr! 3 with z l
  have : l.1 ≠ l₀ := by rintro rfl; simp at hl
  simp [this]

lemma hasSumLocallyUniformly_weierstrassP :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - ↑l) ^ 2 - 1 / l ^ 2) ℘[L] := by
  convert L.hasSumLocallyUniformly_weierstrassPExcept (L.ω₁ / 2) using 3 with l
  · rw [if_neg]; exact fun e ↦ L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]

lemma hasSum_weierstrassP (z : ℂ) :
    HasSum (fun l : L.lattice ↦ (1 / (z - l) ^ 2 - 1 / l ^ 2)) (℘[L] z) :=
  L.hasSumLocallyUniformly_weierstrassP.hasSum

lemma differentiableOn_weierstrassP :
    DifferentiableOn ℂ ℘[L] L.latticeᶜ := by
  rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  convert L.differentiableOn_weierstrassPExcept _
  simp [L.ω₁_div_two_notMem_lattice]

@[simp]
lemma weierstrassP_neg (z : ℂ) : ℘[L] (-z) = ℘[L] z := by
  simp only [weierstrassP]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr with l
  simp
  ring

lemma not_continuousAt_weierstrassP (x : ℂ) (hx : x ∈ L.lattice) : ¬ ContinuousAt ℘[L] x := by
  eta_expand
  simp_rw [← L.weierstrassPExcept_add ⟨x, hx⟩]
  intro H
  apply (NormedField.continuousAt_zpow (n := -2) (x := (0 : ℂ))).not.mpr (by simp)
  simpa [Function.comp_def] using
    (((H.sub ((L.differentiableOn_weierstrassPExcept x).differentiableAt (x := x)
      (L.isOpen_compl_lattice_diff.mem_nhds (by simp))).continuousAt).add
      (continuous_const (y := 1 / x ^ 2)).continuousAt).comp_of_eq
      (continuous_add_left x).continuousAt (add_zero _):)

end weierstrassP

section derivWeierstrassPExcept

/-- The derivative of Weierstrass `℘` function with the `l₀`-term missing.
This is mainly a tool for calculations where one would want to omit a diverging term.
This has the notation `℘'[L - l₀]` in the namespace `PeriodPairs`. -/
def derivWeierstrassPExcept (l₀ : ℂ) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l.1 = l₀ then 0 else -2 / (z - l) ^ 3

@[inherit_doc derivWeierstrassPExcept]
scoped notation3 "℘'[" L:max " - " l₀ "]" => derivWeierstrassPExcept L l₀

lemma hasSumLocallyUniformly_derivWeierstrassPExcept (l₀ : ℂ) :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ if l.1 = l₀ then 0 else -2 / (z - l) ^ 3)
      ℘'[L - l₀] := by
  refine L.hasSumLocallyUniformly_aux (u := fun _ ↦ (16 * ‖·‖ ^ (-3 : ℝ))) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simpa using show 0 ≤ ‖↑l‖ ^ 3 by positivity
  have : s ≠ ↑l := by rintro rfl; exfalso; linarith
  have : l ≠ 0 := by rintro rfl; simp_all; linarith
  simp only [Complex.norm_div, norm_neg, Complex.norm_ofNat, norm_pow, AddSubgroupClass.coe_norm]
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, div_le_div_iff₀, norm_sub_rev]
  · refine LE.le.trans_eq (b := 2 * (2 * ‖l - s‖) ^ 3) ?_ (by ring)
    norm_cast
    gcongr
    refine le_trans ?_ (mul_le_mul le_rfl (norm_sub_norm_le _ _) (by linarith) (by linarith))
    norm_cast at *
    linarith
  · exact pow_pos (by simpa [sub_eq_zero]) _
  · exact Real.rpow_pos_of_pos (by simpa) _

lemma hasSum_derivWeierstrassPExcept (l₀ : ℂ) (z : ℂ) :
    HasSum (fun l : L.lattice ↦ if l.1 = l₀ then 0 else -2 / (z - l) ^ 3) (℘'[L - l₀] z) :=
  (L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀).tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ z)

lemma differentiableOn_derivWeierstrassPExcept (l₀ : ℂ) :
    DifferentiableOn ℂ ℘'[L - l₀] (L.lattice \ {l₀})ᶜ := by
  refine L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀
    |>.tendstoLocallyUniformlyOn.differentiableOn
      (.of_forall fun s ↦ .fun_sum fun i hi ↦ ?_) L.isOpen_compl_lattice_diff
  split_ifs
  · simp
  refine .div (by fun_prop) (by fun_prop) fun x hx ↦ ?_
  have : x ≠ i := by rintro rfl; simp_all
  simpa [sub_eq_zero]

lemma eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept (l₀ : ℂ) :
    Set.EqOn (deriv ℘[L - l₀]) ℘'[L - l₀] (L.lattice \ {l₀})ᶜ := by
  refine ((L.hasSumLocallyUniformly_weierstrassPExcept l₀).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s ↦ ?_) L.isOpen_compl_lattice_diff).unique ?_
  · refine .fun_sum fun i hi ↦ ?_
    split_ifs
    · simp
    refine .sub (.div (by fun_prop) (by fun_prop) fun x hx ↦ ?_) (by fun_prop)
    have : x ≠ i := by rintro rfl; simp_all
    simpa [sub_eq_zero]
  · refine (L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀).tendstoLocallyUniformlyOn.congr ?_
    intro s l hl
    simp only [Function.comp_apply]
    rw [deriv_fun_sum]
    · congr with x
      split_ifs with hl₁
      · simp
      have hl₁ : l - x ≠ 0 := fun e ↦ hl₁ (by
        obtain rfl := sub_eq_zero.mp e
        simpa using hl)
      rw [deriv_fun_sub (.fun_div (by fun_prop) (by fun_prop) (by simpa)) (by fun_prop),
        deriv_const]
      simp_rw [← zpow_natCast, one_div, ← zpow_neg, Nat.cast_ofNat]
      rw [deriv_comp_sub_const (f := (· ^ (-2 : ℤ))), deriv_zpow]
      simp
      field_simp
    · intros x hxs
      split_ifs with hl₁
      · simp
      have hl₁ : l - x ≠ 0 := fun e ↦ hl₁ (by
        obtain rfl := sub_eq_zero.mp e
        simpa using hl)
      exact .sub (.div (by fun_prop) (by fun_prop) (by simpa)) (by fun_prop)

lemma derivWeierstrassPExcept_neg (l₀ : ℂ) (z : ℂ) :
    ℘'[L - l₀] (-z) = - ℘'[L - (-l₀)] z := by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub,
    ← div_neg, ← tsum_neg, apply_ite, neg_zero]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  ring

end derivWeierstrassPExcept

section Periodicity

lemma derivWeierstrassPExcept_add_coe (l₀ : ℂ) (z : ℂ) (l : L.lattice) :
    ℘'[L - l₀] (z + l) = ℘'[L - (l₀ - l)] z := by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub, eq_sub_iff_add_eq]

-- Subsumed by `weierstrassP_add_coe`
private lemma weierstrassPExcept_add_coe_aux
    (l₀ : ℂ) (hl₀ : l₀ ∈ L.lattice) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice) :
    Set.EqOn (℘[L - l₀] <| · + l) (℘[L - (l₀ - l)] · + (1 / l₀ ^ 2 - 1 / (l₀ - ↑l) ^ 2))
      (L.lattice \ {l₀ - l})ᶜ := by
  apply IsOpen.eqOn_of_deriv_eq (𝕜 := ℂ) L.isOpen_compl_lattice_diff
    ?_ ?_ ?_ ?_ (x := - (l / 2)) ?_ ?_
  · refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact .mono sdiff_le (countable_of_Lindelof_of_discrete (X := L.lattice))
  · refine (L.differentiableOn_weierstrassPExcept l₀).comp (f := (· + l.1)) (by fun_prop) ?_
    rintro x h₁ ⟨h₂ : x + l ∈ _, h₃ : x + l ≠ l₀⟩
    exact h₁ ⟨by simpa using sub_mem h₂ l.2, by rintro rfl; simp at h₃⟩
  · refine .add (L.differentiableOn_weierstrassPExcept _) (by simp)
  · intro x hx
    simp only [deriv_add_const', deriv_comp_add_const]
    rw [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept,
      L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept, L.derivWeierstrassPExcept_add_coe]
    · simpa using hx
    · simp only [Set.mem_compl_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff, not_and,
        Decidable.not_not, eq_sub_iff_add_eq] at hx ⊢
      exact fun H ↦ hx (by simpa using sub_mem H l.2)
  · simp [hl]
  · rw [L.weierstrassPExcept_neg, L.weierstrassPExcept_def ⟨l₀, hl₀⟩,
      L.weierstrassPExcept_def ⟨_, neg_mem (sub_mem hl₀ l.2)⟩, add_assoc]
    congr 2 <;> ring

-- Subsumed by `weierstrassP_add_coe`
private lemma weierstrassP_add_coe_aux (z : ℂ) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice) :
    ℘[L] (z + l) = ℘[L] z := by
  have hl0 : l ≠ 0 := by rintro rfl; simp at hl
  by_cases hz : z ∈ L.lattice
  · have := L.weierstrassPExcept_add_coe_aux (z + l) (add_mem hz l.2) l hl (x := z) (by simp)
    dsimp at this
    rw [← L.weierstrassPExcept_add ⟨z + l, add_mem hz l.2⟩, this,
      ← L.weierstrassPExcept_add ⟨z, hz⟩]
    simp
    ring
  · have := L.weierstrassPExcept_add_coe_aux 0 (zero_mem _) l hl (x := z) (by simp [hz])
    simp only [zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      even_two, Even.neg_pow, one_div] at this
    rw [← L.weierstrassPExcept_add 0, Submodule.coe_zero, this, ← L.weierstrassPExcept_add (-l)]
    simp
    ring

@[simp]
lemma weierstrassP_add_coe (z : ℂ) (l : L.lattice) : ℘[L] (z + l) = ℘[L] z := by
  let G : AddSubgroup ℂ :=
    { carrier := { z | (℘[L] <| · + z) = ℘[L] }
      add_mem' := by simp_all [funext_iff, ← add_assoc]
      zero_mem' := by simp
      neg_mem' {z} hz := funext fun i ↦ by conv_lhs => rw [← hz]; simp }
  have : L.lattice ≤ G.toIntSubmodule := by
    rw [lattice, Submodule.span_le]
    rintro _ (rfl|rfl)
    · ext i
      exact L.weierstrassP_add_coe_aux _ ⟨_, L.ω₁_mem_lattice⟩ L.ω₁_div_two_notMem_lattice
    · ext i
      exact L.weierstrassP_add_coe_aux _ ⟨_, L.ω₂_mem_lattice⟩ L.ω₂_div_two_notMem_lattice
  exact congr_fun (this l.2) _

lemma periodic_weierstrassP (l : L.lattice) : ℘[L].Periodic l :=
  (L.weierstrassP_add_coe · l)

@[simp]
lemma weierstrassP_zero : ℘[L] 0 = 0 := by simp [weierstrassP]

@[simp]
lemma weierstrassP_coe (l : L.lattice) : ℘[L] l = 0 := by
  rw [← zero_add l.1, L.weierstrassP_add_coe, L.weierstrassP_zero]

@[simp]
lemma weierstrassP_sub_coe (z : ℂ) (l : L.lattice) : ℘[L] (z - l) = ℘[L] z := by
  rw [← L.weierstrassP_add_coe _ l, sub_add_cancel]

end Periodicity

section derivWeierstrassP

/-- The derivative of Weierstrass `℘` function.
This has the notation `℘'[L]` in the namespace `PeriodPairs`. -/
def derivWeierstrassP (z : ℂ) : ℂ := - ∑' l : L.lattice, 2 / (z - l) ^ 3

@[inherit_doc weierstrassP] scoped notation3 "℘'[" L "]" => derivWeierstrassP L

lemma derivWeierstrassPExcept_sub (l₀ : L.lattice) (z : ℂ) :
    ℘'[L - l₀] z - 2 / (z - l₀) ^ 3 = ℘'[L] z := by
  trans ℘'[L - l₀] z + ∑' i : L.lattice, if i.1 = l₀.1 then (- 2 / (z - l₀) ^ 3) else 0
  · simp [sub_eq_add_neg, neg_div]
  rw [derivWeierstrassP, derivWeierstrassPExcept, ← Summable.tsum_add, ← tsum_neg]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *, neg_div]
  · exact ⟨_, L.hasSum_derivWeierstrassPExcept _ _⟩
  · exact summable_of_finite_support ((Set.finite_singleton l₀).subset (by simp_all))

lemma derivWeierstrassPExcept_def (l₀ : L.lattice) (z : ℂ) :
    ℘'[L - l₀] z = ℘'[L] z + 2 / (z - l₀) ^ 3 := by
  rw [← L.derivWeierstrassPExcept_sub l₀, sub_add_cancel]

lemma derivWeierstrassPExcept_of_notMem (l₀ : ℂ) (hl : l₀ ∉ L.lattice) :
    ℘'[L - l₀] = ℘'[L] := by
  delta derivWeierstrassPExcept derivWeierstrassP
  simp_rw [← tsum_neg]
  congr! 3 with z l
  have : l.1 ≠ l₀ := by rintro rfl; simp at hl
  simp [this, neg_div]

lemma hasSumLocallyUniformly_derivWeierstrassP :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ - 2 / (z - l) ^ 3) ℘'[L] := by
  convert L.hasSumLocallyUniformly_derivWeierstrassPExcept (L.ω₁ / 2) using 3 with l z
  · rw [if_neg, neg_div]; exact fun e ↦ L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]

lemma hasSum_derivWeierstrassP (z : ℂ) :
    HasSum (fun l : L.lattice ↦ - 2 / (z - l) ^ 3) (℘'[L] z) :=
  L.hasSumLocallyUniformly_derivWeierstrassP.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)

lemma differentiableOn_derivWeierstrassP :
    DifferentiableOn ℂ ℘'[L] L.latticeᶜ := by
  rw [← L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  convert L.differentiableOn_derivWeierstrassPExcept _
  simp [L.ω₁_div_two_notMem_lattice]

@[simp]
lemma derivWeierstrassP_neg (z : ℂ) : ℘'[L] (-z) = - ℘'[L] z := by
  simp only [derivWeierstrassP]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub, neg_neg,
    ← div_neg, ← tsum_neg]
  congr! with l
  ring

@[simp]
lemma derivWeierstrassP_add_coe (z : ℂ) (l : L.lattice) :
    ℘'[L] (z + l) = ℘'[L] z := by
  simp only [derivWeierstrassP]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [← tsum_neg, ← div_neg, Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub]

lemma periodic_derivWeierstrassP (l : L.lattice) : ℘'[L].Periodic l :=
  (L.derivWeierstrassP_add_coe · l)

@[simp]
lemma derivWeierstrassP_zero : ℘'[L] 0 = 0 := by
  rw [← CharZero.eq_neg_self_iff, ← L.derivWeierstrassP_neg, neg_zero]

@[simp]
lemma derivWeierstrassP_coe (l : L.lattice) : ℘'[L] l = 0 := by
  rw [← zero_add l.1, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_zero]

@[simp]
lemma derivWeierstrassP_sub_coe (z : ℂ) (l : L.lattice) :
    ℘'[L] (z - l) = ℘'[L] z := by
  rw [← L.derivWeierstrassP_add_coe _ l, sub_add_cancel]

/-- `deriv ℘ = ℘'`. This is true globally because of junk values. -/
@[simp] lemma deriv_weierstrassP : deriv ℘[L] = ℘'[L] := by
  ext x
  by_cases hx : x ∈ L.lattice
  · rw [deriv_zero_of_not_differentiableAt, L.derivWeierstrassP_coe ⟨x, hx⟩]
    exact fun H ↦ L.not_continuousAt_weierstrassP x hx H.continuousAt
  · rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice,
      ← L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice,
      L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept (L.ω₁/2) (x := x) (by simp [hx])]

end derivWeierstrassP

section AnalyticweierstrassPExcept
def sumInvPow (x : ℂ) (r : ℕ) : ℂ := ∑' l : L.lattice, ((l - x) ^ r)⁻¹

def weierstrassPExceptSummand (l₀ x : ℂ) (i : ℕ) (l : L.lattice) : ℂ :=
  if l.1 = l₀ then 0 else ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0)

def weierstrassPExceptSeries (l₀ x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  letI := Classical.propDecidable
  .ofScalars _ fun i ↦ i.casesOn (℘[L - l₀] x) fun i ↦ (i + 2) *
    (L.sumInvPow x (i + 3) - if l₀ ∈ L.lattice then ((l₀ - x) ^ (i + 3))⁻¹ else 0)

lemma coeff_weierstrassPExceptSeries (l₀ x : ℂ) (i : ℕ) :
    (L.weierstrassPExceptSeries l₀ x).coeff i =
      ∑' l : L.lattice, L.weierstrassPExceptSummand l₀ x i l := by
  delta weierstrassPExceptSummand
  rw [weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars]
  cases i with
  | zero => simp [weierstrassPExcept, sub_sq_comm x, zpow_ofNat]
  | succ i =>
    dsimp
    split_ifs with hl₀
    · trans (i + 2) * (L.sumInvPow x (i + 3) -
        ∑' l : L.lattice, if l = ⟨l₀, hl₀⟩ then (l₀ - x) ^ (-↑(i + 3) : ℤ) else 0)
      · congr 2
        rw [tsum_ite_eq, zpow_neg, zpow_natCast]
      · rw [sumInvPow, ← Summable.tsum_sub]
        · rw [← tsum_mul_left]
          simp_rw [Subtype.ext_iff, zpow_neg]
          congr with l
          split_ifs with e
          · simp only [e, zpow_natCast, sub_self, mul_zero]
          · norm_cast; ring
        · refine .of_norm_bounded (ZLattice.summable_norm_sub_zpow _ (-↑(i + 3)) ?_ x) fun l ↦ ?_
          · simp; linarith
          · rw [← zpow_natCast, ← zpow_neg, ← norm_zpow]
        · exact summable_of_finite_support ((Set.finite_singleton ⟨l₀, hl₀⟩).subset (by simp_all))
    · have (l : L.lattice) : l.1 ≠ l₀ := fun e ↦ hl₀ (e ▸ l.2)
      simp only [this, if_false, sub_zero, tsum_mul_left, sumInvPow]
      congr 1
      simp [add_assoc, one_add_one_eq_two]

def _root_.optionProdEquiv {α β : Type*} : Option α × β ≃ β ⊕ α × β where
  toFun x := x.1.casesOn (.inl x.2) (fun a ↦ .inr (a, x.2))
  invFun x := x.casesOn (Prod.mk none) (Prod.map some id)
  left_inv
  | (none, _) => rfl
  | (some _, _) => rfl
  right_inv
  | .inl _ => rfl
  | .inr (_, _) => rfl

lemma summable_weierstrassPExceptSummand (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    Summable (Function.uncurry fun b c ↦ L.weierstrassPExceptSummand l₀ x b c * (z - x) ^ b) := by
  obtain ⟨ε, hε, hε'⟩ : ∃ ε : ℝ, 1 < ε ∧ ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ * ε < ‖l - x‖ := by
    obtain ⟨δ, hδ, h⟩ := Disjoint.exists_cthickenings (by
      simp only [Set.disjoint_iff_inter_eq_empty, Set.mem_diff, Set.mem_inter_iff, not_lt, not_and,
        Metric.mem_closedBall, Complex.dist_eq, Set.ext_iff, SetLike.mem_coe, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, Decidable.not_not, not_imp_comm (a := _ = _)] at hx ⊢
      exact fun x h₁ h₂ ↦ hx ⟨x, h₂⟩ h₁) (isCompact_closedBall x ‖z - x‖)
      (L.isClosed_of_subset_lattice (Set.diff_subset (t := {l₀})))
    by_cases hz : z = x
    · refine ⟨2, one_lt_two, fun l hl ↦ by simpa [hz] using hx l hl⟩
    have : 0 < ‖z - x‖ := by simp [sub_eq_zero, hz]
    refine ⟨δ / ‖z - x‖ + 1, by simpa using show 0 < δ / ‖z - x‖ by positivity, fun l hl ↦ ?_⟩
    rw [mul_add, mul_one, mul_div, mul_div_cancel_left₀ _ this.ne']
    rw [cthickening_closedBall hδ.le (by positivity)] at h
    have := Set.subset_compl_iff_disjoint_left.mpr h (Metric.self_subset_cthickening _ ⟨l.2, hl⟩)
    simpa [Complex.dist_eq] using this
  let e : ℕ × L.lattice ≃ L.lattice ⊕ (ℕ × L.lattice) :=
    (Equiv.prodCongrLeft fun _ ↦ (Denumerable.eqv (Option ℕ)).symm).trans optionProdEquiv
  have he₁ : e.symm ∘ Sum.inl = Prod.mk 0 := rfl
  have he₂ : e.symm ∘ Sum.inr = Prod.map Nat.succ id := rfl
  rw [← e.symm.summable_iff]
  apply Summable.sum
  · simp only [Function.comp_assoc, he₁, weierstrassPExceptSummand]
    simpa [Function.comp_def, sub_sq_comm x] using (L.hasSum_weierstrassPExcept l₀ x).summable
  · simp only [Function.comp_assoc, he₂, Function.uncurry_def]
    simp only [Function.comp_def, Prod.map_fst, Nat.succ_eq_add_one, Prod.map_snd, id_eq]
    refine Summable.of_norm_bounded (g := fun p : ℕ × L.lattice ↦
        ((p.1 + 2) * ε ^ (- p.1 : ℤ)) * (‖p.2 - x‖ ^ (-3 : ℤ) * ‖z - x‖)) ?_ ?_
    · refine Summable.mul_of_nonneg (f := fun p : ℕ ↦ ((p + 2) * ε ^ (- p : ℤ)))
        (g := fun p : L.lattice ↦ ‖p - x‖ ^ (-3 : ℤ) * ‖z - x‖) ?_ ?_ ?_ ?_
      · have : |ε⁻¹| < 1 := by
          rw [abs_inv, abs_eq_self.mpr (by positivity), inv_lt_one_iff₀]; exact .inr hε
        convert ((Real.hasFPowerSeriesOnBall_linear_zero 1 2).hasSum (y := ε⁻¹)
          (by simpa [enorm_eq_nnnorm])).summable
        simp [mul_comm]
      · apply Summable.mul_right
        apply ZLattice.summable_norm_sub_zpow
        simp
      · intro; positivity
      · intro; positivity
    · intro p
      simp only [weierstrassPExceptSummand]
      split_ifs with hp
      · simp only [zero_mul, norm_zero, zpow_neg, zpow_natCast, Int.reduceNeg]; positivity
      simp only [zpow_neg, zpow_natCast, add_assoc]
      norm_num
      simp only [mul_assoc, add_assoc, one_add_one_eq_two]
      rw [pow_succ (n := p.1)]
      refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · norm_cast
      · simp only [← mul_assoc]
        refine mul_le_mul ?_ le_rfl (by positivity) (by positivity)
        rw [pow_add, mul_inv_rev, mul_assoc, mul_comm ((ε ^ p.1)⁻¹)]
        refine mul_le_mul le_rfl ?_ (by positivity) (by positivity)
        rw [← inv_pow, ← inv_pow, ← mul_pow]
        gcongr
        have : ‖z - x‖ * ε < ‖p.2 - x‖ := hε' p.2 hp
        have h : 0 < ‖p.2 - x‖ := (show 0 ≤ ‖z - x‖ * ε by positivity).trans_lt this
        rw [inv_mul_le_iff₀ h, le_mul_inv_iff₀ (by positivity)]
        exact this.le

lemma weierstrassPExcept_eq_tsum (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    ℘[L - l₀] z = ∑' i : ℕ, (L.weierstrassPExceptSeries l₀ x).coeff i * (z - x) ^ i := by
  trans ∑' (l : L.lattice) (i : ℕ), if l.1 = l₀ then 0 else
      ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0) * (z - x) ^ i
  · delta weierstrassPExcept
    congr 1 with l
    split_ifs with h
    · simp
    convert ((Complex.one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero l x
      (by simpa [sub_eq_zero] using (norm_nonneg _).trans_lt (hx l h))).hasSum (y := z - x)
      (by simpa [enorm_eq_nnnorm] using hx _ h)).tsum_eq.symm with i
    · simp
    · simp [mul_comm]
  trans ∑' (l : ↥L.lattice) (i : ℕ), L.weierstrassPExceptSummand l₀ x i l * (z - x) ^ i
  · simp only [weierstrassPExceptSummand, ite_mul, zero_mul]
  · simp_rw [coeff_weierstrassPExceptSeries, ← tsum_mul_right]
    apply Summable.tsum_comm
    exact L.summable_weierstrassPExceptSummand l₀ z x hx

lemma weierstrassPExceptSeries_hasSum (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    HasSum (fun i ↦ (L.weierstrassPExceptSeries l₀ x).coeff i * (z - x) ^ i) (℘[L - l₀] z) := by
  refine (Summable.hasSum_iff ?_).mpr (L.weierstrassPExcept_eq_tsum l₀ z x hx).symm
  simp_rw [coeff_weierstrassPExceptSeries, ← tsum_mul_right]
  exact (L.summable_weierstrassPExceptSummand l₀ z x hx).prod

lemma hasFPowerSeriesOnBall_weierstrassPExcept (l₀ x : ℂ) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r ⊆ (L.lattice \ {l₀})ᶜ) :
    HasFPowerSeriesOnBall ℘[L - l₀] (L.weierstrassPExceptSeries l₀ x) x r := by
  constructor
  · apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    convert tendsto_norm.comp (L.weierstrassPExceptSeries_hasSum l₀ (x + r) x
      ?_).summable.tendsto_atTop_zero using 2 with i
    · simp
    · simp
    · intro l hl
      simpa using Set.subset_compl_comm.mp hr ⟨l.2, hl⟩
  · exact ENNReal.coe_pos.mpr hr0
  · intro z hz
    replace hz : ‖z‖ < r := by simpa using hz
    have := L.weierstrassPExceptSeries_hasSum l₀ (x + z) x
    simp only [add_sub_cancel_left] at this
    convert this (fun l hl ↦ hz.trans (by simpa using Set.subset_compl_comm.mp hr ⟨l.2, hl⟩)) with i
    rw [weierstrassPExceptSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      FormalMultilinearSeries.coeff_ofScalars]
    rfl

lemma analyticOnNhd_weierstrassPExcept (l₀ : ℂ) :
    AnalyticOnNhd ℂ ℘[L - l₀] (L.lattice \ {l₀})ᶜ := by
  intro x hx
  obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.mp L.isOpen_compl_lattice_diff x hx
  lift ε to NNReal using hε.le
  exact ⟨L.weierstrassPExceptSeries l₀ x, _, L.hasFPowerSeriesOnBall_weierstrassPExcept l₀ x (ε / 2)
    (div_pos hε (by simp)) ((Metric.closedBall_subset_ball (by norm_num; exact hε)).trans h)⟩

end AnalyticweierstrassPExcept

section AnalyticderivWeierstrassPExcept

def derivWeierstrassPExceptSeries (l₀ x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  letI := Classical.propDecidable
  .ofScalars _ fun i ↦ (i + 1) * (i + 2) *
    (L.sumInvPow x (i + 3) - if l₀ ∈ L.lattice then ((l₀ - x) ^ (i + 3))⁻¹ else 0)

lemma hasFPowerSeriesOnBall_derivWeierstrassPExcept (l₀ x : ℂ) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r ⊆ (L.lattice \ {l₀})ᶜ) :
    HasFPowerSeriesOnBall ℘'[L - l₀] (L.derivWeierstrassPExceptSeries l₀ x) x r := by
  refine .congr ?_
    ((L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept l₀).mono (.trans ?_ hr))
  · have := (L.hasFPowerSeriesOnBall_weierstrassPExcept l₀ x r hr0 hr).fderiv
    convert (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall this
    ext n
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, smul_eq_mul,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, map_smul,
      ContinuousLinearMap.apply_apply, FormalMultilinearSeries.derivSeries_coeff_one, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, mul_eq_mul_left_iff]
    left
    simp [weierstrassPExceptSeries, derivWeierstrassPExceptSeries, mul_assoc]
  · simpa using Metric.ball_subset_closedBall

lemma analyticOnNhd_derivWeierstrassPExcept (l₀ : ℂ) :
    AnalyticOnNhd ℂ ℘'[L - l₀] (L.lattice \ {l₀})ᶜ := by
  intro x hx
  obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.mp L.isOpen_compl_lattice_diff x hx
  lift ε to NNReal using hε.le
  exact ⟨L.derivWeierstrassPExceptSeries l₀ x, _,
    L.hasFPowerSeriesOnBall_derivWeierstrassPExcept l₀ x (ε / 2)
    (div_pos hε (by simp)) ((Metric.closedBall_subset_ball (by norm_num; exact hε)).trans h)⟩

end AnalyticderivWeierstrassPExcept

section Analytic

def weierstrassPSummand (x : ℂ) (i : ℕ) (l : L.lattice) : ℂ :=
  ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0)

def weierstrassPSeries (x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars _ fun i ↦ i.casesOn (℘[L] x) fun i ↦ (i + 2) * L.sumInvPow x (i + 3)

lemma weierstrassPExceptSeries_of_notMem (l₀ : ℂ) (hl₀ : l₀ ∉ L.lattice) :
    L.weierstrassPExceptSeries l₀ = L.weierstrassPSeries := by
  delta weierstrassPSeries weierstrassPExceptSeries
  congr! with z i f
  · rw [L.weierstrassPExcept_of_notMem _ hl₀]
  · simp [hl₀]

lemma weierstrassPExceptSummand_of_notMem (l₀ : ℂ) (hl₀ : l₀ ∉ L.lattice) :
    L.weierstrassPExceptSummand l₀ = L.weierstrassPSummand := by
  delta weierstrassPSummand weierstrassPExceptSummand
  ext l z l'
  have : l'.1 ≠ l₀ := fun e ↦ hl₀ (e ▸ l'.2)
  simp [this]

lemma coeff_weierstrassPSeries (x : ℂ) (i : ℕ) :
    (L.weierstrassPSeries x).coeff i = ∑' l : L.lattice, L.weierstrassPSummand x i l := by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    L.coeff_weierstrassPExceptSeries,
    ← L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice]

lemma summable_weierstrassPSummand (z x : ℂ)
    (hx : ∀ l : L.lattice, ‖z - x‖ < ‖l - x‖) :
    Summable (Function.uncurry fun b c ↦ L.weierstrassPSummand x b c * (z - x) ^ b) := by
  simp_rw [← L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice]
  refine L.summable_weierstrassPExceptSummand _ z x fun l hl ↦ hx l

lemma weierstrassPSeries_hasSum (z x : ℂ) (hx : ∀ l : L.lattice, ‖z - x‖ < ‖l - x‖) :
    HasSum (fun i ↦ (L.weierstrassPSeries x).coeff i * (z - x) ^ i) (℘[L] z) := by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact L.weierstrassPExceptSeries_hasSum _ z x fun l hl ↦ hx l

lemma hasFPowerSeriesOnBall_weierstrassP (x : ℂ) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r ⊆ L.latticeᶜ) :
    HasFPowerSeriesOnBall ℘[L] (L.weierstrassPSeries x) x r := by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact L.hasFPowerSeriesOnBall_weierstrassPExcept _ x r hr0
    (hr.trans (Set.compl_subset_compl.mpr Set.diff_subset))

lemma analyticOnNhd_weierstrassP : AnalyticOnNhd ℂ ℘[L] L.latticeᶜ := by
  simp_rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  refine (L.analyticOnNhd_weierstrassPExcept _).mono (Set.compl_subset_compl.mpr Set.diff_subset)

lemma ite_eq_one_sub_sq_mul_weierstrassP (l₀ : ℂ) (hl₀ : l₀ ∈ L.lattice) (z : ℂ) :
  (if z = l₀ then 1 else (z - l₀) ^ 2 * ℘[L] z) =
    (z - l₀) ^ 2 * L.weierstrassPExcept l₀ z + 1 - (z - l₀) ^ 2 / l₀ ^ 2 := by
  split_ifs with h
  · subst h
    simp
  rw [← L.weierstrassPExcept_add ⟨_, hl₀⟩, mul_add, mul_sub, add_sub_assoc,
    ← mul_div_assoc, mul_one, ← mul_div_assoc, mul_one, div_self]
  simpa [sub_eq_zero] using h

lemma meromorphicAt_weierstrassP (x : ℂ) : MeromorphicAt ℘[L] x := by
  by_cases hx : x ∈ L.lattice
  · use 3
    simp_rw [← L.weierstrassPExcept_add ⟨x, hx⟩, smul_eq_mul, mul_add, mul_sub]
    refine .add (.mul (by fun_prop) (L.analyticOnNhd_weierstrassPExcept x x (fun e ↦ e.2 rfl)))
      (.sub ?_ (by fun_prop))
    convert_to AnalyticAt ℂ (fun z ↦ z - x) x
    · ext z
      by_cases h : z - x = 0
      · simp [h]
      · rw [pow_succ', one_div, mul_inv_cancel_right₀]
        simpa
    · fun_prop
  · exact (L.analyticOnNhd_weierstrassP x hx).meromorphicAt

lemma order_weierstrassP (l₀ : ℂ) (h : l₀ ∈ L.lattice) :
    meromorphicOrderAt ℘[L] l₀ = -2 := by
  trans ↑(-2 : ℤ)
  · rw [meromorphicOrderAt_eq_int_iff (L.meromorphicAt_weierstrassP l₀)]
    refine ⟨fun z ↦ (z - l₀) ^ 2 * ℘[L - l₀] z + 1 - (z - l₀) ^ 2 / l₀ ^ 2, ?_, ?_, ?_⟩
    · refine .sub (.add (.mul (by fun_prop) ?_) (by fun_prop)) ?_
      · exact L.analyticOnNhd_weierstrassPExcept l₀ l₀ (by simp)
      · by_cases hl₀ : l₀ = 0
        · simpa [hl₀] using analyticAt_const
        · exact .div (by fun_prop) (by fun_prop) (by simpa)
    · simp
    · refine Filter.eventually_of_mem self_mem_nhdsWithin ?_
      rintro z (hz : _ ≠ _)
      have : (z - l₀) ^ 2 ≠ 0 := by simpa [sub_eq_zero]
      simp [← L.ite_eq_one_sub_sq_mul_weierstrassP l₀ h,
        if_neg hz, inv_mul_cancel_left₀ this, zpow_ofNat]
  · norm_num

end Analytic
