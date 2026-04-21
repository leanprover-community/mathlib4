/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

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
- `PeriodPair.analyticOnNhd_weierstrassP`: `℘` is analytic away from the lattice points.
- `PeriodPair.meromorphic_weierstrassP`: `℘` is meromorphic on the whole plane.
- `PeriodPair.order_weierstrassP`: `℘` has a pole of order 2 at each of the lattice points.
- `PeriodPair.derivWeierstrassP_sq` : `℘'(z)² = 4 ℘(z)³ - g₂ ℘(z) - g₃`

## tags

Weierstrass p-functions, Weierstrass p functions

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Module Filter
open scoped Topology Nat

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

set_option backward.isDefEq.respectTransparency false in
lemma mul_ω₁_add_mul_ω₂_mem_lattice {L : PeriodPair} {α β : ℚ} :
    α * L.ω₁ + β * L.ω₂ ∈ L.lattice ↔ α.den = 1 ∧ β.den = 1 := by
  refine ⟨fun H ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · obtain ⟨m, n, e⟩ := mem_lattice.mp H
    have := LinearIndependent.pair_iff.mp L.indep (m - α) (n - β)
      (by simp; linear_combination e)
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
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 0)).not.mpr (by norm_num)

lemma ω₂_div_two_notMem_lattice : L.ω₂ / 2 ∉ L.lattice := by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := 1 / 2)).not.mpr (by norm_num)

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

open scoped Topology in
lemma compl_lattice_diff_singleton_mem_nhds (x : ℂ) : (↑L.lattice \ {x})ᶜ ∈ 𝓝 x :=
  L.isOpen_compl_lattice_diff.mem_nhds (by simp)

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

set_option backward.isDefEq.respectTransparency false in
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
lemma weierstrassP_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) ^ 2 - 1 / l ^ 2‖ ≤ 10 * r * ‖l‖ ^ (-3 : ℝ) := by
  have : s ≠ ↑l := by rintro rfl; linarith
  have : 0 < ‖l‖ := by linarith
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

@[simp] lemma weierstrassPExcept_zero (l₀ : ℂ) :
    ℘[L - l₀] 0 = 0 := by simp [weierstrassPExcept]

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
  · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by simp))

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
    (((H.sub ((L.differentiableOn_weierstrassPExcept x).differentiableAt
      (L.compl_lattice_diff_singleton_mem_nhds x)).continuousAt).add
      (continuous_const (y := 1 / x ^ 2)).continuousAt).comp_of_eq
      (continuous_const_add x).continuousAt (add_zero _) :)

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
  simp only [Complex.norm_div, norm_neg, Complex.norm_ofNat, norm_pow]
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

@[simp] lemma deriv_weierstrassPExcept_same (l : ℂ) : deriv ℘[L - l] l = ℘'[L - l] l :=
  L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept l (x := l) (by simp)

lemma derivWeierstrassPExcept_neg (l₀ : ℂ) (z : ℂ) :
    ℘'[L - l₀] (-z) = - ℘'[L - (-l₀)] z := by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub,
    ← div_neg, ← tsum_neg, apply_ite, neg_zero]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  ring

@[simp] lemma derivWeierstrassPExcept_zero_zero : ℘'[L - 0] 0 = 0 := by
  simpa [CharZero.eq_neg_self_iff] using L.derivWeierstrassPExcept_neg 0 0

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
    ?_ ?_ ?_ ?_ (x := -(l / 2)) ?_ ?_
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
    rintro _ (rfl | rfl)
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
  · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by simp))

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
      L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept (L.ω₁ / 2) (x := x) (by simp [hx])]

end derivWeierstrassP

section AnalyticWeierstrassPExcept

/-- The sum `∑ (l - x)⁻ʳ` over `l ∈ L`. This converges when `2 < r`, see `hasSum_sumInvPow`. -/
def sumInvPow (x : ℂ) (r : ℕ) : ℂ := ∑' l : L.lattice, ((l - x) ^ r)⁻¹

lemma hasSum_sumInvPow (x : ℂ) {r : ℕ} (hr : 2 < r) :
    HasSum (fun l : L.lattice ↦ ((l - x) ^ r)⁻¹) (L.sumInvPow x r) := by
  refine Summable.hasSum (.of_norm_bounded (ZLattice.summable_norm_sub_zpow _
    (-r) (by simpa) x) fun l ↦ ?_)
  rw [← zpow_natCast, ← zpow_neg, ← norm_zpow]

/-- In the power series expansion of `℘(z) = ∑ aᵢ (z - x)ⁱ` at some `x ∉ L`,
each `aᵢ` can be written as an infinite sum over `l ∈ L`.
This is the summand of this infinite sum with the `l₀`-th term omitted.
See `PeriodPair.coeff_weierstrassPExceptSeries`. -/
def weierstrassPExceptSummand (l₀ x : ℂ) (i : ℕ) (l : L.lattice) : ℂ :=
  if l.1 = l₀ then 0 else ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0)

/-- The power series expansion of `℘[L - l₀]` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_weierstrassPExcept`. -/
def weierstrassPExceptSeries (l₀ x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  letI := Classical.propDecidable
  .ofScalars _ fun i ↦ if i = 0 then (℘[L - l₀] x) else (i + 1) *
    (L.sumInvPow x (i + 2) - if l₀ ∈ L.lattice then ((l₀ - x) ^ (i + 2))⁻¹ else 0)

lemma coeff_weierstrassPExceptSeries (l₀ x : ℂ) (i : ℕ) :
    (L.weierstrassPExceptSeries l₀ x).coeff i =
      ∑' l : L.lattice, L.weierstrassPExceptSummand l₀ x i l := by
  delta weierstrassPExceptSummand weierstrassPExceptSeries
  cases i with
  | zero => simp [weierstrassPExcept, sub_sq_comm x, zpow_ofNat]
  | succ i =>
    split_ifs with hl₀
    · trans (i + 2) * (L.sumInvPow x (i + 3) -
        ∑' l : L.lattice, if l = ⟨l₀, hl₀⟩ then (l₀ - x) ^ (-↑(i + 3) : ℤ) else 0)
      · rw [FormalMultilinearSeries.coeff_ofScalars, tsum_ite_eq, zpow_neg, zpow_natCast]
        simp [add_assoc, one_add_one_eq_two]
      · rw [sumInvPow, ← (hasSum_sumInvPow _ _ (by linarith)).summable.tsum_sub, ← tsum_mul_left]
        · simp_rw [Subtype.ext_iff, zpow_neg]
          congr with l
          split_ifs with e
          · simp only [e, zpow_natCast, sub_self, mul_zero]
          · dsimp; norm_cast; ring
        · exact summable_of_hasFiniteSupport ((Set.finite_singleton ⟨l₀, hl₀⟩).subset (by simp))
    · have h₁ (l : L.lattice) : l.1 ≠ l₀ := fun e ↦ hl₀ (e ▸ l.2)
      simp [h₁, tsum_mul_left, sumInvPow, add_assoc,
        one_add_one_eq_two, ← zpow_natCast, -neg_add_rev]

/--
In the power series expansion of `℘(z) = ∑ᵢ aᵢ (z - x)ⁱ` at some `x ∉ L`,
each `aᵢ` can be written as a sum over `l ∈ L`, i.e.
`aᵢ = ∑ₗ, (i + 1) * (l - x)⁻ⁱ⁻²` for `i ≠ 0` and `a₀ = ∑ₗ, (l - x)⁻² - l⁻²`.

We show that the double sum converges if `z` falls in a ball centered at `x` that doesn't touch `L`.
-/
-- We should be able to skip this computation via some general complex-analytic machinery but
-- they are missing at the moment.
-- Consider refactoring once we have developed more of the missing API.
lemma summable_weierstrassPExceptSummand (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    Summable (Function.uncurry fun b c ↦ L.weierstrassPExceptSummand l₀ x b c * (z - x) ^ b) := by
  -- We first find a `κ > 1`,
  -- such that the ball centered at `x` with radius `κ * ‖z - x‖` does not touch `L`.
  obtain ⟨κ, hκ, hκ'⟩ : ∃ κ : ℝ, 1 < κ ∧ ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ * κ < ‖l - x‖ := by
    obtain ⟨κ, hκ, hκ'⟩ := Metric.isOpen_iff.mp ((continuous_mul_const ‖z - x‖).isOpen_preimage _
      (isClosedMap_dist x _
      (L.isClosed_of_subset_lattice (Set.diff_subset (t := {l₀})))).upperClosure.isOpen_compl) 1
      (by simpa [Complex.dist_eq, @forall_comm ℝ, norm_sub_rev x] using hx)
    refine ⟨κ / 2 + 1, by simpa, fun l hl ↦ ?_⟩
    have : ∀ l ∈ L.lattice, l ≠ l₀ → (κ / 2 + 1) * ‖z - x‖ < dist x l := by
      simpa using @hκ' (κ / 2 + 1) (by simp [div_lt_iff₀, abs_eq_self.mpr hκ.le, hκ])
    simpa only [Complex.dist_eq, norm_sub_rev x, mul_comm] using this _ l.2 hl
  -- We single out the degree zero term via this equiv.
  let e : ℕ × L.lattice ≃ L.lattice ⊕ (ℕ × L.lattice) :=
    (Equiv.prodCongrLeft fun _ ↦ (Denumerable.eqv (Option ℕ)).symm).trans optionProdEquiv
  rw [← e.symm.summable_iff]
  apply Summable.sum
  · -- for the degree zero term, this is the usual summability of the definition of `℘`.
    simpa [weierstrassPExceptSummand, e, Function.comp_def, Function.uncurry, sub_sq_comm x,
      Denumerable.eqv] using (L.hasSum_weierstrassPExcept l₀ x).summable
  · -- for the remaining terms, we bound it by `(i + 2) κ⁻ⁱ * ‖l - x‖⁻³ * ‖z - x‖`.
    dsimp [e, Function.comp_def, Function.uncurry_def, Denumerable.eqv, weierstrassPExceptSummand]
    have H₁ : Summable fun i : ℕ ↦ ((i + 2) * κ ^ (-i : ℤ)) := by
      have : |κ⁻¹| < 1 := by grind [abs_inv, inv_lt_one_iff₀]
      simpa [mul_comm] using ((Real.hasFPowerSeriesOnBall_ofScalars_mul_add_zero 1 2).hasSum
        (y := κ⁻¹) (by simpa [enorm_eq_nnnorm])).summable
    have H₂ : Summable fun l : L.lattice ↦ ‖l - x‖ ^ (-3 : ℤ) * ‖z - x‖ :=
      (ZLattice.summable_norm_sub_zpow _ _ (by simp) _).mul_right _
    refine (H₁.mul_of_nonneg H₂ (by intro; positivity) (by intro; positivity)).of_norm_bounded ?_
    intro p
    split_ifs with hp
    · simp only [zero_mul, norm_zero, zpow_neg, zpow_natCast, Int.reduceNeg]; positivity
    have hpx : ‖p.2 - x‖ ≠ 0 := fun h ↦ by
      obtain rfl : p.2 = x := by simpa [sub_eq_zero] using h
      simpa [(norm_nonneg _).not_gt] using hx p.2 hp
    obtain rfl | hxz := eq_or_ne z x
    · simp
    calc
      _ = ‖(p.1 + 2 : ℂ)‖ * ‖p.2 - x‖ ^ (-3 - p.1 : ℤ) * ‖z - x‖ ^ (p.1 + 1) := by
        norm_num; ring_nf; simp
      _ = ‖(p.1 + 2 : ℂ)‖ * ((‖↑p.2 - x‖ / ‖z - x‖) ^ p.1)⁻¹ * ((‖p.2 - x‖ ^ 3)⁻¹ * ‖z - x‖) := by
        simp [hpx, zpow_sub₀, div_pow]; field
      _ ≤ (p.1 + 2) * (κ ^ p.1)⁻¹ * ((‖p.2 - x‖ ^ 3)⁻¹ * ‖z - x‖) := by
        gcongr
        · norm_cast
        · exact (le_div_iff₀ (by simpa [sub_eq_zero])).mpr ((mul_comm _ _).trans_le (hκ' p.2 hp).le)
      _ = _ := by simp [zpow_ofNat]

lemma weierstrassPExcept_eq_tsum (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    ℘[L - l₀] z = ∑' i : ℕ, (L.weierstrassPExceptSeries l₀ x).coeff i * (z - x) ^ i := by
  trans ∑' (l : L.lattice) (i : ℕ), if l.1 = l₀ then 0 else
      ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0) * (z - x) ^ i
  · delta weierstrassPExcept
    congr 1 with l
    split_ifs with h
    · simp
    simpa [mul_comm] using ((Complex.one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero l x
      (by simpa [sub_eq_zero] using (norm_nonneg _).trans_lt (hx l h))).hasSum (y := z - x)
      (by simpa [enorm_eq_nnnorm] using hx _ h)).tsum_eq.symm
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
      simpa [-Metric.mem_closedBall, mem_closedBall_iff_norm]
        using Set.subset_compl_comm.mp hr ⟨l.2, hl⟩
  · exact ENNReal.coe_pos.mpr hr0
  · intro z hz
    replace hz : ‖z‖ < r := by simpa using hz
    have := L.weierstrassPExceptSeries_hasSum l₀ (x + z) x
    simp only [add_sub_cancel_left] at this
    have A (l : ↥L.lattice) (hl : ↑l ≠ l₀) : r < ‖↑l - x‖ := by
      simpa [-Metric.mem_closedBall, mem_closedBall_iff_norm] using
        Set.subset_compl_comm.mp hr ⟨l.2, hl⟩
    convert this (fun l hl ↦ hz.trans (A l hl)) with i
    rw [weierstrassPExceptSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]

lemma hasFPowerSeriesAt_weierstrassPExcept (l : ℂ) :
    HasFPowerSeriesAt ℘[L - l] (.ofScalars (𝕜 := ℂ) ℂ fun i : ℕ ↦
      if i = 0 then ℘[L - l] l else (i + 1) * L.sumInvPow l (i + 2)) l := by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_diff_singleton_mem_nhds l)
  lift r to NNReal using h₁.le
  simpa [weierstrassPExceptSeries] using
    (L.hasFPowerSeriesOnBall_weierstrassPExcept l l r h₁ h₂).hasFPowerSeriesAt

lemma analyticOnNhd_weierstrassPExcept (l₀ : ℂ) : AnalyticOnNhd ℂ ℘[L - l₀] (L.lattice \ {l₀})ᶜ :=
  (L.differentiableOn_weierstrassPExcept l₀).analyticOnNhd L.isOpen_compl_lattice_diff

@[fun_prop]
lemma analyticAt_weierstrassPExcept (l₀ : ℂ) : AnalyticAt ℂ ℘[L - l₀] l₀ :=
  L.analyticOnNhd_weierstrassPExcept _ _ (by simp)

attribute [local simp] Nat.factorial_ne_zero in
lemma iteratedDeriv_weierstrassPExcept_self (l : ℂ) {n : ℕ} :
    iteratedDeriv n ℘[L - l] l =
      if n = 0 then ℘[L - l] l else (n + 1)! * L.sumInvPow l (n + 2) := by
  rw [← div_mul_cancel₀ (a := iteratedDeriv _ _ _) (b := ↑n !) (by simp),
    ← eq_div_iff_mul_eq (by simp)]
  trans if n = 0 then ℘[L - l] l else (n + 1) * L.sumInvPow l (n + 2)
  · simpa using congr($((L.analyticAt_weierstrassPExcept l).hasFPowerSeriesAt
      |>.eq_formalMultilinearSeries (L.hasFPowerSeriesAt_weierstrassPExcept l)).coeff n)
  · cases n <;> simp [Nat.factorial_succ]; field

end AnalyticWeierstrassPExcept

section AnalyticderivWeierstrassPExcept

/-- The power series expansion of `℘'[L - l₀]` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_derivWeierstrassPExcept`. -/
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
    simp [weierstrassPExceptSeries, derivWeierstrassPExceptSeries]
    ring
  · simpa using Metric.ball_subset_closedBall

lemma hasFPowerSeriesAt_derivWeierstrassPExcept (l : ℂ) :
    HasFPowerSeriesAt ℘'[L - l]
      (.ofScalars ℂ fun i ↦ (i + 1) * (i + 2) * L.sumInvPow l (i + 3)) l := by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_diff_singleton_mem_nhds l)
  simpa [derivWeierstrassPExceptSeries] using
    (L.hasFPowerSeriesOnBall_derivWeierstrassPExcept l l ⟨r, h₁.le⟩ h₁ h₂).hasFPowerSeriesAt

lemma analyticOnNhd_derivWeierstrassPExcept (l₀ : ℂ) :
    AnalyticOnNhd ℂ ℘'[L - l₀] (L.lattice \ {l₀})ᶜ :=
  (L.differentiableOn_derivWeierstrassPExcept l₀).analyticOnNhd L.isOpen_compl_lattice_diff

@[fun_prop]
lemma analyticAt_derivWeierstrassPExcept (l₀ : ℂ) :
    AnalyticAt ℂ ℘'[L - l₀] l₀ :=
  L.analyticOnNhd_derivWeierstrassPExcept l₀ _ (by simp)

lemma iteratedDeriv_derivWeierstrassPExcept_self (l : ℂ) {n : ℕ} :
    iteratedDeriv n ℘'[L - l] l = (n + 2)! * L.sumInvPow l (n + 3) := by
  have : iteratedDeriv n ℘'[L - l] l / n ! = (↑n + 1) * (↑n + 2) * L.sumInvPow l (n + 3) := by
    simpa using congr($((L.analyticAt_derivWeierstrassPExcept l).hasFPowerSeriesAt
      |>.eq_formalMultilinearSeries (L.hasFPowerSeriesAt_derivWeierstrassPExcept l)).coeff n)
  simp [div_eq_iff, Nat.factorial_ne_zero, Nat.factorial_succ] at this ⊢
  grind

@[simp]
lemma deriv_derivWeierstrassPExcept_self (l : ℂ) :
    deriv ℘'[L - l] l = 6 * L.sumInvPow l 4 := by
  simpa using L.iteratedDeriv_derivWeierstrassPExcept_self l (n := 1)

lemma analyticOnNhd_derivWeierstrassP : AnalyticOnNhd ℂ ℘'[L] L.latticeᶜ :=
  L.differentiableOn_derivWeierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl

end AnalyticderivWeierstrassPExcept

section Analytic

/-- In the power series expansion of `℘(z) = ∑ aᵢzⁱ` at some `x ∉ L`,
each `aᵢ` can be written as an infinite sum over `l ∈ L`.
This is the summand of this infinite sum. See `PeriodPair.coeff_weierstrassPSeries`. -/
def weierstrassPSummand (x : ℂ) (i : ℕ) (l : L.lattice) : ℂ :=
  ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0)

/-- The power series expansion of `℘` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_weierstrassP`. -/
def weierstrassPSeries (x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars _ fun i ↦ if i = 0 then (℘[L] x) else (i + 1) * L.sumInvPow x (i + 2)

lemma weierstrassPExceptSeries_of_notMem (l₀ : ℂ) (hl₀ : l₀ ∉ L.lattice) :
    L.weierstrassPExceptSeries l₀ = L.weierstrassPSeries := by
  delta weierstrassPSeries weierstrassPExceptSeries
  congr! with z i f
  · rw [L.weierstrassPExcept_of_notMem _ hl₀]
  · simp [hl₀]

lemma weierstrassPExceptSummand_of_notMem (l₀ : ℂ) (hl₀ : l₀ ∉ L.lattice) :
    L.weierstrassPExceptSummand l₀ = L.weierstrassPSummand := by
  grind [weierstrassPSummand, weierstrassPExceptSummand]

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

lemma analyticOnNhd_weierstrassP : AnalyticOnNhd ℂ ℘[L] L.latticeᶜ :=
  L.differentiableOn_weierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl

lemma ite_eq_one_sub_sq_mul_weierstrassP (l₀ : ℂ) (hl₀ : l₀ ∈ L.lattice) (z : ℂ) :
    (if z = l₀ then 1 else (z - l₀) ^ 2 * ℘[L] z) =
      (z - l₀) ^ 2 * ℘[L - l₀] z + 1 - (z - l₀) ^ 2 / l₀ ^ 2 := by
  grind [L.weierstrassPExcept_add ⟨_, hl₀⟩]

@[fun_prop]
lemma meromorphic_weierstrassP : Meromorphic ℘[L] := by
  intro x
  by_cases hx : x ∈ L.lattice
  · simp_rw [← funext <| L.weierstrassPExcept_add ⟨x, hx⟩]
    have := (analyticOnNhd_weierstrassPExcept L x x (by simp)).meromorphicAt
    fun_prop
  · exact (L.analyticOnNhd_weierstrassP x hx).meromorphicAt

@[fun_prop]
lemma meromorphic_derivWeierstrassP : Meromorphic ℘'[L] := by
  rw [← deriv_weierstrassP]
  fun_prop

lemma order_weierstrassP (l₀ : ℂ) (h : l₀ ∈ L.lattice) :
    meromorphicOrderAt ℘[L] l₀ = -2 := by
  trans ↑(-2 : ℤ)
  · rw [meromorphicOrderAt_eq_int_iff (L.meromorphic_weierstrassP l₀)]
    refine ⟨fun z ↦ (z - l₀) ^ 2 * ℘[L - l₀] z + 1 - (z - l₀) ^ 2 / l₀ ^ 2, ?_, ?_, ?_⟩
    · have : AnalyticAt ℂ ℘[L - l₀] l₀ := L.analyticOnNhd_weierstrassPExcept l₀ l₀ (by simp)
      suffices AnalyticAt ℂ (fun z ↦ (z - l₀) ^ 2 / l₀ ^ 2) l₀ by fun_prop
      by_cases hl₀ : l₀ = 0
      · simpa [hl₀] using analyticAt_const
      · fun_prop (disch := simpa)
    · simp
    · filter_upwards [self_mem_nhdsWithin] with z (hz : _ ≠ _)
      have : (z - l₀) ^ 2 ≠ 0 := by simpa [sub_eq_zero]
      simp [← L.ite_eq_one_sub_sq_mul_weierstrassP l₀ h,
        if_neg hz, inv_mul_cancel_left₀ this, zpow_ofNat]
  · norm_num

end Analytic

section Relation

/-- The Eisenstein series as a function on lattices.
It takes `L` to the sum `∑ l⁻ʳ` over `l ∈ L`.
TODO: Establish connections with the `ModularForm` library. -/
def G (n : ℕ) : ℂ := ∑' l : L.lattice, (l ^ n)⁻¹

@[simp]
lemma sumInvPow_zero : L.sumInvPow 0 = L.G := by
  ext; simp [sumInvPow, G]

lemma G_eq_zero_of_odd (n : ℕ) (hn : Odd n) : L.G n = 0 := by
  rw [← CharZero.eq_neg_self_iff, G, ← tsum_neg, ← (Equiv.neg _).tsum_eq]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, neg_inv, hn.neg_pow]

/-- The lattice invariant `g₂ := 60 G₄`. -/
def g₂ : ℂ := 60 * L.G 4

/-- The lattice invariant `g₃ := 140 G₆`. -/
def g₃ : ℂ := 140 * L.G 6

/-- (Implementation detail) The relation that `℘'` and `℘` satisfies.
We will show that this is constant zero. See `PeriodPair.relation_eq_zero` -/
private def relation (z : ℂ) : ℂ :=
  letI := Classical.propDecidable
  if z ∈ L.lattice then 0 else ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃

@[local fun_prop]
private lemma meromorphic_relation : Meromorphic L.relation := by
  have : Meromorphic fun z ↦ ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃ := by fun_prop
  refine fun z ↦ (this _).congr ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_diff_singleton_mem_nhds _)] with w hw hw'
  rw [relation, if_neg (by simp_all)]

private lemma relation_mul_id_pow_six_eventuallyEq :
    (L.relation * id ^ 6) =ᶠ[nhds 0] fun z ↦
      (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) ^ 2 - 4 *
      (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3 + L.g₂ *
      (℘[L - (0 : ℂ)] z * z ^ 6 + z ^ 4) + L.g₃ * z ^ 6 := by
  filter_upwards [L.compl_lattice_diff_singleton_mem_nhds _] with z hz
  by_cases hz0 : z = 0
  · simp [hz0, relation]; norm_num
  replace hz : z ∉ L.lattice := by simp_all
  simp only [Pi.mul_apply, Pi.pow_apply, relation, ↓reduceIte, hz,
    ← ZeroMemClass.coe_zero L.lattice, L.derivWeierstrassPExcept_def, L.weierstrassPExcept_def]
  simp
  field

@[local fun_prop]
private lemma analyticAt_relation_mul_id_pow_six :
    AnalyticAt ℂ (L.relation * id ^ 6) 0 := by
  refine .congr ?_ L.relation_mul_id_pow_six_eventuallyEq.symm
  fun_prop

@[local simp]
private lemma relation_neg (x) : L.relation (-x) = L.relation x := by
  classical simp [relation]

attribute [local fun_prop] AnalyticAt.contDiffAt in
private lemma iteratedDeriv_six_relation_mul_id_pow_six :
    iteratedDeriv 6 (L.relation * id ^ 6) 0 = 0 := by
  rw [L.relation_mul_id_pow_six_eventuallyEq.iteratedDeriv_eq]
  simp_rw [pow_succ (_ + _), pow_succ (_ - _), pow_zero, one_mul]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_derivWeierstrassPExcept_self, iteratedDeriv_weierstrassPExcept_self]
  simp [Finset.sum_range_succ, L.G_eq_zero_of_odd 3 (by decide), g₃,
    show Nat.choose 6 4 = 15 by rfl, show Nat.choose 6 3 = 20 by rfl]
  ring

attribute [local fun_prop] AnalyticAt.contDiffAt in
private lemma analyticAt_relation_zero : AnalyticAt ℂ L.relation 0 := by
  refine .of_meromorphicOrderAt_pos (one_pos.trans_le ?_) (by simp [relation])
  suffices 7 ≤ meromorphicOrderAt (L.relation * id ^ 6) 0 by
    rw [meromorphicOrderAt_mul (by fun_prop) (by fun_prop),
      meromorphicOrderAt_pow (by fun_prop)] at this
    rw [← WithTop.add_le_add_iff_right (z := 6) (by simp)]
    simpa [-add_le_add_iff_left_of_ne_top] using this
  rw [AnalyticAt.meromorphicOrderAt_eq (by fun_prop)]
  refine ENat.monotone_map_iff.mpr Nat.mono_cast
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (by fun_prop)).mpr fun i hi₁ ↦ ?_)
  by_cases hi₂ : Odd i
  · simpa [← CharZero.eq_neg_self_iff, hi₂, (show Even 6 by decide).neg_pow] using
      (iteratedDeriv_comp_neg i (L.relation * id ^ 6) 0 :)
  by_cases hi₃ : i = 0
  · simp [hi₃]
  by_cases hi₄ : i = 6
  · exact hi₄ ▸ L.iteratedDeriv_six_relation_mul_id_pow_six
  rw [L.relation_mul_id_pow_six_eventuallyEq.iteratedDeriv_eq]
  simp_rw [pow_succ (_ + _), pow_succ (_ - _), pow_zero, one_mul]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_derivWeierstrassPExcept_self, iteratedDeriv_weierstrassPExcept_self]
  obtain rfl | rfl : i = 2 ∨ i = 4 := by grind
  · simp [Finset.sum_range_succ]
  · simp [Finset.sum_range_succ, show Nat.choose 4 2 = 6 by rfl, g₂]; ring

@[local simp]
private lemma relation_add_coe (x : ℂ) (l : L.lattice) :
    L.relation (x + l) = L.relation x := by
  simp only [relation, derivWeierstrassP_add_coe, weierstrassP_add_coe]
  congr 1
  simpa using (L.lattice.toAddSubgroup.add_mem_cancel_right (y := x) l.2)

@[local simp]
private lemma relation_sub_coe (x : ℂ) (l : L.lattice) :
    L.relation (x - l) = L.relation x := by
  rw [← L.relation_add_coe _ l, sub_add_cancel]

private lemma analyticAt_relation (x : ℂ) : AnalyticAt ℂ L.relation x := by
  by_cases hx : x ∈ L.lattice
  · lift x to L.lattice using hx
    have := L.analyticAt_relation_zero
    rw [← sub_self x.1] at this
    convert this.comp (f := (· - x.1)) (by fun_prop)
    ext a
    simp
  · have : AnalyticAt ℂ (fun z ↦ ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃) x := by
      have := L.analyticOnNhd_derivWeierstrassP _ hx
      have := L.analyticOnNhd_weierstrassP _ hx
      fun_prop (disch := assumption)
    apply this.congr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hx] with x hx
    simp_all [relation]

private lemma relation_eq_zero : L.relation = 0 := by
  ext x
  have : Differentiable ℂ L.relation := fun x ↦ (L.analyticAt_relation x).differentiableAt
  exact (this.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic L.lattice _
    this.continuous fun z w hw ↦ by lift w to L.lattice using hw; simp).isBounded x 0).trans
    (if_pos (by simp))

/-- `℘'(z)² = 4 ℘(z)³ - g₂ ℘(z) - g₃` -/
lemma derivWeierstrassP_sq (z : ℂ) (hz : z ∉ L.lattice) :
    ℘'[L] z ^ 2 = 4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃ := by
  simpa [sub_eq_zero, relation, hz, sub_add] using congr($L.relation_eq_zero z)

end Relation

end PeriodPair
