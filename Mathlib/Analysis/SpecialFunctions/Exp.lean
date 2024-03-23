/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

#align_import analysis.special_functions.exp from "leanprover-community/mathlib"@"ba5ff5ad5d120fb0ef094ad2994967e9bfaf5112"

/-!
# Complex and real exponential

In this file we prove continuity of `Complex.exp` and `Real.exp`. We also prove a few facts about
limits of `Real.exp` at infinity.

## Tags

exp
-/


noncomputable section

open Finset Filter Metric Asymptotics Set Function Bornology

open scoped Classical Topology

namespace Complex

variable {z y x : ℝ}

theorem exp_bound_sq (x z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖exp (x + z) - exp x - z • exp x‖ ≤ ‖exp x‖ * ‖z‖ ^ 2 :=
  calc
    ‖exp (x + z) - exp x - z * exp x‖ = ‖exp x * (exp z - 1 - z)‖ := by
      congr
      rw [exp_add]
      ring
    _ = ‖exp x‖ * ‖exp z - 1 - z‖ := (norm_mul _ _)
    _ ≤ ‖exp x‖ * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (abs_exp_sub_one_sub_id_le hz) (norm_nonneg _)
#align complex.exp_bound_sq Complex.exp_bound_sq

theorem locally_lipschitz_exp {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_le : r ≤ 1) (x y : ℂ)
    (hyx : ‖y - x‖ < r) : ‖exp y - exp x‖ ≤ (1 + r) * ‖exp x‖ * ‖y - x‖ := by
  have hy_eq : y = x + (y - x) := by abel
  have hyx_sq_le : ‖y - x‖ ^ 2 ≤ r * ‖y - x‖ := by
    rw [pow_two]
    exact mul_le_mul hyx.le le_rfl (norm_nonneg _) hr_nonneg
  have h_sq : ∀ z, ‖z‖ ≤ 1 → ‖exp (x + z) - exp x‖ ≤ ‖z‖ * ‖exp x‖ + ‖exp x‖ * ‖z‖ ^ 2 := by
    intro z hz
    have : ‖exp (x + z) - exp x - z • exp x‖ ≤ ‖exp x‖ * ‖z‖ ^ 2 := exp_bound_sq x z hz
    rw [← sub_le_iff_le_add', ← norm_smul z]
    exact (norm_sub_norm_le _ _).trans this
  calc
    ‖exp y - exp x‖ = ‖exp (x + (y - x)) - exp x‖ := by nth_rw 1 [hy_eq]
    _ ≤ ‖y - x‖ * ‖exp x‖ + ‖exp x‖ * ‖y - x‖ ^ 2 := (h_sq (y - x) (hyx.le.trans hr_le))
    _ ≤ ‖y - x‖ * ‖exp x‖ + ‖exp x‖ * (r * ‖y - x‖) :=
      (add_le_add_left (mul_le_mul le_rfl hyx_sq_le (sq_nonneg _) (norm_nonneg _)) _)
    _ = (1 + r) * ‖exp x‖ * ‖y - x‖ := by ring
#align complex.locally_lipschitz_exp Complex.locally_lipschitz_exp

-- Porting note: proof by term mode `locally_lipschitz_exp zero_le_one le_rfl x`
-- doesn't work because `‖y - x‖` and `dist y x` don't unify
@[continuity]
theorem continuous_exp : Continuous exp :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_of_locally_lipschitz zero_lt_one (2 * ‖exp x‖)
      (fun y ↦ by
        convert locally_lipschitz_exp zero_le_one le_rfl x y using 2
        congr
        ring)
#align complex.continuous_exp Complex.continuous_exp

theorem continuousOn_exp {s : Set ℂ} : ContinuousOn exp s :=
  continuous_exp.continuousOn
#align complex.continuous_on_exp Complex.continuousOn_exp

end Complex

section ComplexContinuousExpComp

variable {α : Type*}

open Complex

theorem Filter.Tendsto.cexp {l : Filter α} {f : α → ℂ} {z : ℂ} (hf : Tendsto f l (𝓝 z)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.tendsto _).comp hf
#align filter.tendsto.cexp Filter.Tendsto.cexp

variable [TopologicalSpace α] {f : α → ℂ} {s : Set α} {x : α}

nonrec
theorem ContinuousWithinAt.cexp (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.cexp
#align continuous_within_at.cexp ContinuousWithinAt.cexp

@[fun_prop]
nonrec
theorem ContinuousAt.cexp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.cexp
#align continuous_at.cexp ContinuousAt.cexp

@[fun_prop]
theorem ContinuousOn.cexp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y)) s :=
  fun x hx => (h x hx).cexp
#align continuous_on.cexp ContinuousOn.cexp

@[fun_prop]
theorem Continuous.cexp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuousAt.2 fun _ => h.continuousAt.cexp
#align continuous.cexp Continuous.cexp

end ComplexContinuousExpComp

namespace Real

@[continuity]
theorem continuous_exp : Continuous exp :=
  Complex.continuous_re.comp Complex.continuous_ofReal.cexp
#align real.continuous_exp Real.continuous_exp

theorem continuousOn_exp {s : Set ℝ} : ContinuousOn exp s :=
  continuous_exp.continuousOn
#align real.continuous_on_exp Real.continuousOn_exp

end Real

section RealContinuousExpComp

variable {α : Type*}

open Real

theorem Filter.Tendsto.exp {l : Filter α} {f : α → ℝ} {z : ℝ} (hf : Tendsto f l (𝓝 z)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.tendsto _).comp hf
#align filter.tendsto.exp Filter.Tendsto.exp

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {x : α}

nonrec
theorem ContinuousWithinAt.exp (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.exp
#align continuous_within_at.exp ContinuousWithinAt.exp

@[fun_prop]
nonrec
theorem ContinuousAt.exp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.exp
#align continuous_at.exp ContinuousAt.exp

@[fun_prop]
theorem ContinuousOn.exp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y)) s := fun x hx =>
  (h x hx).exp
#align continuous_on.exp ContinuousOn.exp

@[fun_prop]
theorem Continuous.exp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuousAt.2 fun _ => h.continuousAt.exp
#align continuous.exp Continuous.exp

end RealContinuousExpComp

namespace Real

variable {α : Type*} {x y z : ℝ} {l : Filter α}

theorem exp_half (x : ℝ) : exp (x / 2) = sqrt (exp x) := by
  rw [eq_comm, sqrt_eq_iff_sq_eq, sq, ← exp_add, add_halves] <;> exact (exp_pos _).le
#align real.exp_half Real.exp_half

/-- The real exponential function tends to `+∞` at `+∞`. -/
theorem tendsto_exp_atTop : Tendsto exp atTop atTop := by
  have A : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have B : ∀ᶠ x in atTop, x + 1 ≤ exp x := eventually_atTop.2 ⟨0, fun x _ => add_one_le_exp x⟩
  exact tendsto_atTop_mono' atTop B A
#align real.tendsto_exp_at_top Real.tendsto_exp_atTop

/-- The real exponential function tends to `0` at `-∞` or, equivalently, `exp(-x)` tends to `0`
at `+∞` -/
theorem tendsto_exp_neg_atTop_nhds_zero : Tendsto (fun x => exp (-x)) atTop (𝓝 0) :=
  (tendsto_inv_atTop_zero.comp tendsto_exp_atTop).congr fun x => (exp_neg x).symm
#align real.tendsto_exp_neg_at_top_nhds_0 Real.tendsto_exp_neg_atTop_nhds_zero
@[deprecated] alias tendsto_exp_neg_atTop_nhds_0 := tendsto_exp_neg_atTop_nhds_zero

/-- The real exponential function tends to `1` at `0`. -/
theorem tendsto_exp_nhds_zero_nhds_one : Tendsto exp (𝓝 0) (𝓝 1) := by
  convert continuous_exp.tendsto 0
  simp
#align real.tendsto_exp_nhds_0_nhds_1 Real.tendsto_exp_nhds_zero_nhds_one
@[deprecated] alias tendsto_exp_nhds_0_nhds_1 := tendsto_exp_nhds_zero_nhds_one

theorem tendsto_exp_atBot : Tendsto exp atBot (𝓝 0) :=
  (tendsto_exp_neg_atTop_nhds_zero.comp tendsto_neg_atBot_atTop).congr fun x =>
    congr_arg exp <| neg_neg x
#align real.tendsto_exp_at_bot Real.tendsto_exp_atBot

theorem tendsto_exp_atBot_nhdsWithin : Tendsto exp atBot (𝓝[>] 0) :=
  tendsto_inf.2 ⟨tendsto_exp_atBot, tendsto_principal.2 <| eventually_of_forall exp_pos⟩
#align real.tendsto_exp_at_bot_nhds_within Real.tendsto_exp_atBot_nhdsWithin

@[simp]
theorem isBoundedUnder_ge_exp_comp (l : Filter α) (f : α → ℝ) :
    IsBoundedUnder (· ≥ ·) l fun x => exp (f x) :=
  isBoundedUnder_of ⟨0, fun _ => (exp_pos _).le⟩
#align real.is_bounded_under_ge_exp_comp Real.isBoundedUnder_ge_exp_comp

@[simp]
theorem isBoundedUnder_le_exp_comp {f : α → ℝ} :
    (IsBoundedUnder (· ≤ ·) l fun x => exp (f x)) ↔ IsBoundedUnder (· ≤ ·) l f :=
  exp_monotone.isBoundedUnder_le_comp_iff tendsto_exp_atTop
#align real.is_bounded_under_le_exp_comp Real.isBoundedUnder_le_exp_comp

/-- The function `exp(x)/x^n` tends to `+∞` at `+∞`, for any natural number `n` -/
theorem tendsto_exp_div_pow_atTop (n : ℕ) : Tendsto (fun x => exp x / x ^ n) atTop atTop := by
  refine' (atTop_basis_Ioi.tendsto_iff (atTop_basis' 1)).2 fun C hC₁ => _
  have hC₀ : 0 < C := zero_lt_one.trans_le hC₁
  have : 0 < (exp 1 * C)⁻¹ := inv_pos.2 (mul_pos (exp_pos _) hC₀)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ≥ N, (↑k : ℝ) ^ n / exp 1 ^ k < (exp 1 * C)⁻¹ :=
    eventually_atTop.1
      ((tendsto_pow_const_div_const_pow_of_one_lt n (one_lt_exp_iff.2 zero_lt_one)).eventually
        (gt_mem_nhds this))
  simp only [← exp_nat_mul, mul_one, div_lt_iff, exp_pos, ← div_eq_inv_mul] at hN
  refine' ⟨N, trivial, fun x hx => _⟩
  rw [Set.mem_Ioi] at hx
  have hx₀ : 0 < x := (Nat.cast_nonneg N).trans_lt hx
  rw [Set.mem_Ici, le_div_iff (pow_pos hx₀ _), ← le_div_iff' hC₀]
  calc
    x ^ n ≤ ⌈x⌉₊ ^ n := mod_cast pow_le_pow_left hx₀.le (Nat.le_ceil _) _
    _ ≤ exp ⌈x⌉₊ / (exp 1 * C) := mod_cast (hN _ (Nat.lt_ceil.2 hx).le).le
    _ ≤ exp (x + 1) / (exp 1 * C) := by gcongr; exact (Nat.ceil_lt_add_one hx₀.le).le
    _ = exp x / C := by rw [add_comm, exp_add, mul_div_mul_left _ _ (exp_pos _).ne']
#align real.tendsto_exp_div_pow_at_top Real.tendsto_exp_div_pow_atTop

/-- The function `x^n * exp(-x)` tends to `0` at `+∞`, for any natural number `n`. -/
theorem tendsto_pow_mul_exp_neg_atTop_nhds_zero (n : ℕ) :
    Tendsto (fun x => x ^ n * exp (-x)) atTop (𝓝 0) :=
  (tendsto_inv_atTop_zero.comp (tendsto_exp_div_pow_atTop n)).congr fun x => by
    rw [comp_apply, inv_eq_one_div, div_div_eq_mul_div, one_mul, div_eq_mul_inv, exp_neg]
#align real.tendsto_pow_mul_exp_neg_at_top_nhds_0 Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero
@[deprecated] alias tendsto_pow_mul_exp_neg_atTop_nhds_0 := tendsto_pow_mul_exp_neg_atTop_nhds_zero

/-- The function `(b * exp x + c) / (x ^ n)` tends to `+∞` at `+∞`, for any natural number
`n` and any real numbers `b` and `c` such that `b` is positive. -/
theorem tendsto_mul_exp_add_div_pow_atTop (b c : ℝ) (n : ℕ) (hb : 0 < b) :
    Tendsto (fun x => (b * exp x + c) / x ^ n) atTop atTop := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp only [pow_zero, div_one]
    exact (tendsto_exp_atTop.const_mul_atTop hb).atTop_add tendsto_const_nhds
  simp only [add_div, mul_div_assoc]
  exact
    ((tendsto_exp_div_pow_atTop n).const_mul_atTop hb).atTop_add
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop hn))
#align real.tendsto_mul_exp_add_div_pow_at_top Real.tendsto_mul_exp_add_div_pow_atTop

/-- The function `(x ^ n) / (b * exp x + c)` tends to `0` at `+∞`, for any natural number
`n` and any real numbers `b` and `c` such that `b` is nonzero. -/
theorem tendsto_div_pow_mul_exp_add_atTop (b c : ℝ) (n : ℕ) (hb : 0 ≠ b) :
    Tendsto (fun x => x ^ n / (b * exp x + c)) atTop (𝓝 0) := by
  have H : ∀ d e, 0 < d → Tendsto (fun x : ℝ => x ^ n / (d * exp x + e)) atTop (𝓝 0) := by
    intro b' c' h
    convert (tendsto_mul_exp_add_div_pow_atTop b' c' n h).inv_tendsto_atTop using 1
    ext x
    simp
  cases' lt_or_gt_of_ne hb with h h
  · exact H b c h
  · convert (H (-b) (-c) (neg_pos.mpr h)).neg using 1
    · ext x
      field_simp
      rw [← neg_add (b * exp x) c, neg_div_neg_eq]
    · rw [neg_zero]
#align real.tendsto_div_pow_mul_exp_add_at_top Real.tendsto_div_pow_mul_exp_add_atTop

/-- `Real.exp` as an order isomorphism between `ℝ` and `(0, +∞)`. -/
def expOrderIso : ℝ ≃o Ioi (0 : ℝ) :=
  StrictMono.orderIsoOfSurjective _ (exp_strictMono.codRestrict exp_pos) <|
    (continuous_exp.subtype_mk _).surjective
      (by simp only [tendsto_Ioi_atTop, Subtype.coe_mk, tendsto_exp_atTop])
      (by simp [tendsto_exp_atBot_nhdsWithin])
#align real.exp_order_iso Real.expOrderIso

@[simp]
theorem coe_expOrderIso_apply (x : ℝ) : (expOrderIso x : ℝ) = exp x :=
  rfl
#align real.coe_exp_order_iso_apply Real.coe_expOrderIso_apply

@[simp]
theorem coe_comp_expOrderIso : (↑) ∘ expOrderIso = exp :=
  rfl
#align real.coe_comp_exp_order_iso Real.coe_comp_expOrderIso

@[simp]
theorem range_exp : range exp = Set.Ioi 0 := by
  rw [← coe_comp_expOrderIso, range_comp, expOrderIso.range_eq, image_univ, Subtype.range_coe]
#align real.range_exp Real.range_exp

@[simp]
theorem map_exp_atTop : map exp atTop = atTop := by
  rw [← coe_comp_expOrderIso, ← Filter.map_map, OrderIso.map_atTop, map_val_Ioi_atTop]
#align real.map_exp_at_top Real.map_exp_atTop

@[simp]
theorem comap_exp_atTop : comap exp atTop = atTop := by
  rw [← map_exp_atTop, comap_map exp_injective, map_exp_atTop]
#align real.comap_exp_at_top Real.comap_exp_atTop

@[simp]
theorem tendsto_exp_comp_atTop {f : α → ℝ} :
    Tendsto (fun x => exp (f x)) l atTop ↔ Tendsto f l atTop := by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_atTop]
#align real.tendsto_exp_comp_at_top Real.tendsto_exp_comp_atTop

theorem tendsto_comp_exp_atTop {f : ℝ → α} :
    Tendsto (fun x => f (exp x)) atTop l ↔ Tendsto f atTop l := by
  simp_rw [← comp_apply (g := exp), ← tendsto_map'_iff, map_exp_atTop]
#align real.tendsto_comp_exp_at_top Real.tendsto_comp_exp_atTop

@[simp]
theorem map_exp_atBot : map exp atBot = 𝓝[>] 0 := by
  rw [← coe_comp_expOrderIso, ← Filter.map_map, expOrderIso.map_atBot, ← map_coe_Ioi_atBot]
#align real.map_exp_at_bot Real.map_exp_atBot

@[simp]
theorem comap_exp_nhdsWithin_Ioi_zero : comap exp (𝓝[>] 0) = atBot := by
  rw [← map_exp_atBot, comap_map exp_injective]
#align real.comap_exp_nhds_within_Ioi_zero Real.comap_exp_nhdsWithin_Ioi_zero

theorem tendsto_comp_exp_atBot {f : ℝ → α} :
    Tendsto (fun x => f (exp x)) atBot l ↔ Tendsto f (𝓝[>] 0) l := by
  rw [← map_exp_atBot, tendsto_map'_iff]
  rfl
#align real.tendsto_comp_exp_at_bot Real.tendsto_comp_exp_atBot

@[simp]
theorem comap_exp_nhds_zero : comap exp (𝓝 0) = atBot :=
  (comap_nhdsWithin_range exp 0).symm.trans <| by simp
#align real.comap_exp_nhds_zero Real.comap_exp_nhds_zero

@[simp]
theorem tendsto_exp_comp_nhds_zero {f : α → ℝ} :
    Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto f l atBot := by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_nhds_zero]
#align real.tendsto_exp_comp_nhds_zero Real.tendsto_exp_comp_nhds_zero

-- Porting note (#10756): new lemma
theorem openEmbedding_exp : OpenEmbedding exp :=
  isOpen_Ioi.openEmbedding_subtype_val.comp expOrderIso.toHomeomorph.openEmbedding

-- Porting note (#10756): new lemma;
-- Porting note (#11215): TODO: backport & make `@[simp]`
theorem map_exp_nhds (x : ℝ) : map exp (𝓝 x) = 𝓝 (exp x) :=
  openEmbedding_exp.map_nhds_eq x

-- Porting note (#10756): new lemma;
-- Porting note (#11215): TODO: backport & make `@[simp]`
theorem comap_exp_nhds_exp (x : ℝ) : comap exp (𝓝 (exp x)) = 𝓝 x :=
  (openEmbedding_exp.nhds_eq_comap x).symm

theorem isLittleO_pow_exp_atTop {n : ℕ} : (fun x : ℝ => x ^ n) =o[atTop] Real.exp := by
  simpa [isLittleO_iff_tendsto fun x hx => ((exp_pos x).ne' hx).elim] using
    tendsto_div_pow_mul_exp_add_atTop 1 0 n zero_ne_one
#align real.is_o_pow_exp_at_top Real.isLittleO_pow_exp_atTop

@[simp]
theorem isBigO_exp_comp_exp_comp {f g : α → ℝ} :
    ((fun x => exp (f x)) =O[l] fun x => exp (g x)) ↔ IsBoundedUnder (· ≤ ·) l (f - g) :=
  Iff.trans (isBigO_iff_isBoundedUnder_le_div <| eventually_of_forall fun x => exp_ne_zero _) <| by
    simp only [norm_eq_abs, abs_exp, ← exp_sub, isBoundedUnder_le_exp_comp, Pi.sub_def]
set_option linter.uppercaseLean3 false in
#align real.is_O_exp_comp_exp_comp Real.isBigO_exp_comp_exp_comp

@[simp]
theorem isTheta_exp_comp_exp_comp {f g : α → ℝ} :
    ((fun x => exp (f x)) =Θ[l] fun x => exp (g x)) ↔
      IsBoundedUnder (· ≤ ·) l fun x => |f x - g x| := by
  simp only [isBoundedUnder_le_abs, ← isBoundedUnder_le_neg, neg_sub, IsTheta,
    isBigO_exp_comp_exp_comp, Pi.sub_def]
set_option linter.uppercaseLean3 false in
#align real.is_Theta_exp_comp_exp_comp Real.isTheta_exp_comp_exp_comp

@[simp]
theorem isLittleO_exp_comp_exp_comp {f g : α → ℝ} :
    ((fun x => exp (f x)) =o[l] fun x => exp (g x)) ↔ Tendsto (fun x => g x - f x) l atTop := by
  simp only [isLittleO_iff_tendsto, exp_ne_zero, ← exp_sub, ← tendsto_neg_atTop_iff, false_imp_iff,
    imp_true_iff, tendsto_exp_comp_nhds_zero, neg_sub]
#align real.is_o_exp_comp_exp_comp Real.isLittleO_exp_comp_exp_comp

-- Porting note (#10618): @[simp] can prove:  by simp only [@Asymptotics.isLittleO_one_left_iff,
--   Real.norm_eq_abs, Real.abs_exp, @Real.tendsto_exp_comp_atTop]
theorem isLittleO_one_exp_comp {f : α → ℝ} :
    ((fun _ => 1 : α → ℝ) =o[l] fun x => exp (f x)) ↔ Tendsto f l atTop := by
  simp only [← exp_zero, isLittleO_exp_comp_exp_comp, sub_zero]
#align real.is_o_one_exp_comp Real.isLittleO_one_exp_comp

/-- `Real.exp (f x)` is bounded away from zero along a filter if and only if this filter is bounded
from below under `f`. -/
@[simp]
theorem isBigO_one_exp_comp {f : α → ℝ} :
    ((fun _ => 1 : α → ℝ) =O[l] fun x => exp (f x)) ↔ IsBoundedUnder (· ≥ ·) l f := by
  simp only [← exp_zero, isBigO_exp_comp_exp_comp, Pi.sub_def, zero_sub, isBoundedUnder_le_neg]
set_option linter.uppercaseLean3 false in
#align real.is_O_one_exp_comp Real.isBigO_one_exp_comp

/-- `Real.exp (f x)` is bounded away from zero along a filter if and only if this filter is bounded
from below under `f`. -/
theorem isBigO_exp_comp_one {f : α → ℝ} :
    (fun x => exp (f x)) =O[l] (fun _ => 1 : α → ℝ) ↔ IsBoundedUnder (· ≤ ·) l f := by
  simp only [isBigO_one_iff, norm_eq_abs, abs_exp, isBoundedUnder_le_exp_comp]
set_option linter.uppercaseLean3 false in
#align real.is_O_exp_comp_one Real.isBigO_exp_comp_one

/-- `Real.exp (f x)` is bounded away from zero and infinity along a filter `l` if and only if
`|f x|` is bounded from above along this filter. -/
@[simp]
theorem isTheta_exp_comp_one {f : α → ℝ} :
    (fun x => exp (f x)) =Θ[l] (fun _ => 1 : α → ℝ) ↔ IsBoundedUnder (· ≤ ·) l fun x => |f x| := by
  simp only [← exp_zero, isTheta_exp_comp_exp_comp, sub_zero]
set_option linter.uppercaseLean3 false in
#align real.is_Theta_exp_comp_one Real.isTheta_exp_comp_one

lemma summable_exp_nat_mul_iff {a : ℝ} :
    Summable (fun n : ℕ ↦ exp (n * a)) ↔ a < 0 := by
  simp only [exp_nat_mul, summable_geometric_iff_norm_lt_one, norm_of_nonneg (exp_nonneg _),
    exp_lt_one_iff]

lemma summable_exp_neg_nat : Summable fun n : ℕ ↦ exp (-n) := by
  simpa only [mul_neg_one] using summable_exp_nat_mul_iff.mpr neg_one_lt_zero

lemma summable_pow_mul_exp_neg_nat_mul (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ ↦ n ^ k * exp (-r * n) := by
  simp_rw [mul_comm (-r), exp_nat_mul]
  apply summable_pow_mul_geometric_of_norm_lt_one
  rwa [norm_of_nonneg (exp_nonneg _), exp_lt_one_iff, neg_lt_zero]

end Real

namespace Complex

@[simp]
theorem comap_exp_cobounded : comap exp (cobounded ℂ) = comap re atTop :=
  calc
    comap exp (cobounded ℂ) = comap re (comap Real.exp atTop) := by
      simp only [← comap_norm_atTop, Complex.norm_eq_abs, comap_comap, (· ∘ ·), abs_exp]
    _ = comap re atTop := by rw [Real.comap_exp_atTop]
#align complex.comap_exp_comap_abs_at_top Complex.comap_exp_cobounded

@[simp]
theorem comap_exp_nhds_zero : comap exp (𝓝 0) = comap re atBot :=
  calc
    comap exp (𝓝 0) = comap re (comap Real.exp (𝓝 0)) := by
      simp only [comap_comap, ← comap_abs_nhds_zero, (· ∘ ·), abs_exp]
    _ = comap re atBot := by rw [Real.comap_exp_nhds_zero]
#align complex.comap_exp_nhds_zero Complex.comap_exp_nhds_zero

theorem comap_exp_nhdsWithin_zero : comap exp (𝓝[≠] 0) = comap re atBot := by
  have : (exp ⁻¹' {0})ᶜ = Set.univ := eq_univ_of_forall exp_ne_zero
  simp [nhdsWithin, comap_exp_nhds_zero, this]
#align complex.comap_exp_nhds_within_zero Complex.comap_exp_nhdsWithin_zero

theorem tendsto_exp_nhds_zero_iff {α : Type*} {l : Filter α} {f : α → ℂ} :
    Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto (fun x => re (f x)) l atBot := by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_nhds_zero, tendsto_comap_iff]
  rfl
#align complex.tendsto_exp_nhds_zero_iff Complex.tendsto_exp_nhds_zero_iff

/-- `Complex.abs (Complex.exp z) → ∞` as `Complex.re z → ∞`. -/
theorem tendsto_exp_comap_re_atTop : Tendsto exp (comap re atTop) (cobounded ℂ) :=
  comap_exp_cobounded ▸ tendsto_comap
#align complex.tendsto_exp_comap_re_at_top Complex.tendsto_exp_comap_re_atTop

/-- `Complex.exp z → 0` as `Complex.re z → -∞`.-/
theorem tendsto_exp_comap_re_atBot : Tendsto exp (comap re atBot) (𝓝 0) :=
  comap_exp_nhds_zero ▸ tendsto_comap
#align complex.tendsto_exp_comap_re_at_bot Complex.tendsto_exp_comap_re_atBot

theorem tendsto_exp_comap_re_atBot_nhdsWithin : Tendsto exp (comap re atBot) (𝓝[≠] 0) :=
  comap_exp_nhdsWithin_zero ▸ tendsto_comap
#align complex.tendsto_exp_comap_re_at_bot_nhds_within Complex.tendsto_exp_comap_re_atBot_nhdsWithin

end Complex
