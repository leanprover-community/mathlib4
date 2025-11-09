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

/- `℘Except l₀` is differentiable on non-lattice points and `l₀`. -/
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

end PeriodPair
