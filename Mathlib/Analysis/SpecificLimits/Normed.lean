/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sébastien Gouëzel, Yury G. Kudryashov, Dylan MacKenzie, Patrick Massot
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Filter.ModEq
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Analysis.NormedSpace.Basic

#align_import analysis.specific_limits.normed from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# A collection of specific limit computations

This file contains important specific limit computations in (semi-)normed groups/rings/spaces, as
well as such computations in `ℝ` when the natural proof passes through a fact about normed spaces.

-/


noncomputable section

open scoped Classical
open Set Function Filter Finset Metric Asymptotics

open scoped Classical
open Topology Nat uniformity NNReal ENNReal

variable {α : Type*} {β : Type*} {ι : Type*}

theorem tendsto_norm_atTop_atTop : Tendsto (norm : ℝ → ℝ) atTop atTop :=
  tendsto_abs_atTop_atTop
#align tendsto_norm_at_top_at_top tendsto_norm_atTop_atTop

theorem summable_of_absolute_convergence_real {f : ℕ → ℝ} :
    (∃ r, Tendsto (fun n ↦ ∑ i ∈ range n, |f i|) atTop (𝓝 r)) → Summable f
  | ⟨r, hr⟩ => by
    refine .of_norm ⟨r, (hasSum_iff_tendsto_nat_of_nonneg ?_ _).2 ?_⟩
    · exact fun i ↦ norm_nonneg _
    · simpa only using hr
#align summable_of_absolute_convergence_real summable_of_absolute_convergence_real

/-! ### Powers -/


theorem tendsto_norm_zero' {𝕜 : Type*} [NormedAddCommGroup 𝕜] :
    Tendsto (norm : 𝕜 → ℝ) (𝓝[≠] 0) (𝓝[>] 0) :=
  tendsto_norm_zero.inf <| tendsto_principal_principal.2 fun _ hx ↦ norm_pos_iff.2 hx
#align tendsto_norm_zero' tendsto_norm_zero'

namespace NormedField

theorem tendsto_norm_inverse_nhdsWithin_0_atTop {𝕜 : Type*} [NormedDivisionRing 𝕜] :
    Tendsto (fun x : 𝕜 ↦ ‖x⁻¹‖) (𝓝[≠] 0) atTop :=
  (tendsto_inv_zero_atTop.comp tendsto_norm_zero').congr fun x ↦ (norm_inv x).symm
#align normed_field.tendsto_norm_inverse_nhds_within_0_at_top NormedField.tendsto_norm_inverse_nhdsWithin_0_atTop

theorem tendsto_norm_zpow_nhdsWithin_0_atTop {𝕜 : Type*} [NormedDivisionRing 𝕜] {m : ℤ}
    (hm : m < 0) :
    Tendsto (fun x : 𝕜 ↦ ‖x ^ m‖) (𝓝[≠] 0) atTop := by
  rcases neg_surjective m with ⟨m, rfl⟩
  rw [neg_lt_zero] at hm; lift m to ℕ using hm.le; rw [Int.natCast_pos] at hm
  simp only [norm_pow, zpow_neg, zpow_natCast, ← inv_pow]
  exact (tendsto_pow_atTop hm.ne').comp NormedField.tendsto_norm_inverse_nhdsWithin_0_atTop
#align normed_field.tendsto_norm_zpow_nhds_within_0_at_top NormedField.tendsto_norm_zpow_nhdsWithin_0_atTop

/-- The (scalar) product of a sequence that tends to zero with a bounded one also tends to zero. -/
theorem tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 𝔸 : Type*} [NormedDivisionRing 𝕜]
    [NormedAddCommGroup 𝔸] [Module 𝕜 𝔸] [BoundedSMul 𝕜 𝔸] {l : Filter ι} {ε : ι → 𝕜} {f : ι → 𝔸}
    (hε : Tendsto ε l (𝓝 0)) (hf : Filter.IsBoundedUnder (· ≤ ·) l (norm ∘ f)) :
    Tendsto (ε • f) l (𝓝 0) := by
  rw [← isLittleO_one_iff 𝕜] at hε ⊢
  simpa using IsLittleO.smul_isBigO hε (hf.isBigO_const (one_ne_zero : (1 : 𝕜) ≠ 0))
#align normed_field.tendsto_zero_smul_of_tendsto_zero_of_bounded NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded

@[simp]
theorem continuousAt_zpow {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m : ℤ} {x : 𝕜} :
    ContinuousAt (fun x ↦ x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m := by
  refine ⟨?_, continuousAt_zpow₀ _ _⟩
  contrapose!; rintro ⟨rfl, hm⟩ hc
  exact not_tendsto_atTop_of_tendsto_nhds (hc.tendsto.mono_left nhdsWithin_le_nhds).norm
    (tendsto_norm_zpow_nhdsWithin_0_atTop hm)
#align normed_field.continuous_at_zpow NormedField.continuousAt_zpow

@[simp]
theorem continuousAt_inv {𝕜 : Type*} [NontriviallyNormedField 𝕜] {x : 𝕜} :
    ContinuousAt Inv.inv x ↔ x ≠ 0 := by
  simpa [(zero_lt_one' ℤ).not_le] using @continuousAt_zpow _ _ (-1) x
#align normed_field.continuous_at_inv NormedField.continuousAt_inv

end NormedField

theorem isLittleO_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
    (fun n : ℕ ↦ r₁ ^ n) =o[atTop] fun n ↦ r₂ ^ n :=
  have H : 0 < r₂ := h₁.trans_lt h₂
  (isLittleO_of_tendsto fun _ hn ↦ False.elim <| H.ne' <| pow_eq_zero hn) <|
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr fun _ ↦ div_pow _ _ _
#align is_o_pow_pow_of_lt_left isLittleO_pow_pow_of_lt_left

theorem isBigO_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    (fun n : ℕ ↦ r₁ ^ n) =O[atTop] fun n ↦ r₂ ^ n :=
  h₂.eq_or_lt.elim (fun h ↦ h ▸ isBigO_refl _ _) fun h ↦ (isLittleO_pow_pow_of_lt_left h₁ h).isBigO
set_option linter.uppercaseLean3 false in
#align is_O_pow_pow_of_le_left isBigO_pow_pow_of_le_left

theorem isLittleO_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : |r₁| < |r₂|) :
    (fun n : ℕ ↦ r₁ ^ n) =o[atTop] fun n ↦ r₂ ^ n := by
  refine (IsLittleO.of_norm_left ?_).of_norm_right
  exact (isLittleO_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)
#align is_o_pow_pow_of_abs_lt_left isLittleO_pow_pow_of_abs_lt_left

open List in
/-- Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.

* 0: $f n = o(a ^ n)$ for some $-R < a < R$;
* 1: $f n = o(a ^ n)$ for some $0 < a < R$;
* 2: $f n = O(a ^ n)$ for some $-R < a < R$;
* 3: $f n = O(a ^ n)$ for some $0 < a < R$;
* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$
     for all `n`;
* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;
* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.

NB: For backwards compatibility, if you add more items to the list, please append them at the end of
the list. -/
theorem TFAE_exists_lt_isLittleO_pow (f : ℕ → ℝ) (R : ℝ) :
    TFAE
      [∃ a ∈ Ioo (-R) R, f =o[atTop] (a ^ ·), ∃ a ∈ Ioo 0 R, f =o[atTop] (a ^ ·),
        ∃ a ∈ Ioo (-R) R, f =O[atTop] (a ^ ·), ∃ a ∈ Ioo 0 R, f =O[atTop] (a ^ ·),
        ∃ a < R, ∃ C : ℝ, (0 < C ∨ 0 < R) ∧ ∀ n, |f n| ≤ C * a ^ n,
        ∃ a ∈ Ioo 0 R, ∃ C > 0, ∀ n, |f n| ≤ C * a ^ n, ∃ a < R, ∀ᶠ n in atTop, |f n| ≤ a ^ n,
        ∃ a ∈ Ioo 0 R, ∀ᶠ n in atTop, |f n| ≤ a ^ n] := by
  have A : Ico 0 R ⊆ Ioo (-R) R :=
    fun x hx ↦ ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩
  have B : Ioo 0 R ⊆ Ioo (-R) R := Subset.trans Ioo_subset_Ico_self A
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have 1 → 3
  · exact fun ⟨a, ha, H⟩ ↦ ⟨a, ha, H.isBigO⟩
  tfae_have 2 → 1
  · exact fun ⟨a, ha, H⟩ ↦ ⟨a, B ha, H⟩
  tfae_have 3 → 2
  · rintro ⟨a, ha, H⟩
    rcases exists_between (abs_lt.2 ha) with ⟨b, hab, hbR⟩
    exact ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩,
      H.trans_isLittleO (isLittleO_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩
  tfae_have 2 → 4
  · exact fun ⟨a, ha, H⟩ ↦ ⟨a, ha, H.isBigO⟩
  tfae_have 4 → 3
  · exact fun ⟨a, ha, H⟩ ↦ ⟨a, B ha, H⟩
  -- Add 5 and 6 using 4 → 6 → 5 → 3
  tfae_have 4 → 6
  · rintro ⟨a, ha, H⟩
    rcases bound_of_isBigO_nat_atTop H with ⟨C, hC₀, hC⟩
    refine ⟨a, ha, C, hC₀, fun n ↦ ?_⟩
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg ha.1.le] using hC (pow_ne_zero n ha.1.ne')
  tfae_have 6 → 5
  · exact fun ⟨a, ha, C, H₀, H⟩ ↦ ⟨a, ha.2, C, Or.inl H₀, H⟩
  tfae_have 5 → 3
  · rintro ⟨a, ha, C, h₀, H⟩
    rcases sign_cases_of_C_mul_pow_nonneg fun n ↦ (abs_nonneg _).trans (H n) with (rfl | ⟨hC₀, ha₀⟩)
    · obtain rfl : f = 0 := by
        ext n
        simpa using H n
      simp only [lt_irrefl, false_or_iff] at h₀
      exact ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, isBigO_zero _ _⟩
    exact ⟨a, A ⟨ha₀, ha⟩,
      isBigO_of_le' _ fun n ↦ (H n).trans <| mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le⟩
  -- Add 7 and 8 using 2 → 8 → 7 → 3
  tfae_have 2 → 8
  · rintro ⟨a, ha, H⟩
    refine ⟨a, ha, (H.def zero_lt_one).mono fun n hn ↦ ?_⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_pow, abs_of_pos ha.1] at hn
  tfae_have 8 → 7
  · exact fun ⟨a, ha, H⟩ ↦ ⟨a, ha.2, H⟩
  tfae_have 7 → 3
  · rintro ⟨a, ha, H⟩
    have : 0 ≤ a := nonneg_of_eventually_pow_nonneg (H.mono fun n ↦ (abs_nonneg _).trans)
    refine ⟨a, A ⟨this, ha⟩, IsBigO.of_bound 1 ?_⟩
    simpa only [Real.norm_eq_abs, one_mul, abs_pow, abs_of_nonneg this]
  -- Porting note: used to work without explicitly having 6 → 7
  tfae_have 6 → 7
  · exact fun h ↦ tfae_8_to_7 <| tfae_2_to_8 <| tfae_3_to_2 <| tfae_5_to_3 <| tfae_6_to_5 h
  tfae_finish
#align tfae_exists_lt_is_o_pow TFAE_exists_lt_isLittleO_pow

/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
theorem isLittleO_pow_const_const_pow_of_one_lt {R : Type*} [NormedRing R] (k : ℕ) {r : ℝ}
    (hr : 1 < r) : (fun n ↦ (n : R) ^ k : ℕ → R) =o[atTop] fun n ↦ r ^ n := by
  have : Tendsto (fun x : ℝ ↦ x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : ℝ) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : ℝ, hr' : r' ^ k < r, h1 : 1 < r'⟩ :=
    ((this.eventually (gt_mem_nhds hr)).and self_mem_nhdsWithin).exists
  have h0 : 0 ≤ r' := zero_le_one.trans h1.le
  suffices (fun n ↦ (n : R) ^ k : ℕ → R) =O[atTop] fun n : ℕ ↦ (r' ^ k) ^ n from
    this.trans_isLittleO (isLittleO_pow_pow_of_lt_left (pow_nonneg h0 _) hr')
  conv in (r' ^ _) ^ _ => rw [← pow_mul, mul_comm, pow_mul]
  suffices ∀ n : ℕ, ‖(n : R)‖ ≤ (r' - 1)⁻¹ * ‖(1 : R)‖ * ‖r' ^ n‖ from
    (isBigO_of_le' _ this).pow _
  intro n
  rw [mul_right_comm]
  refine n.norm_cast_le.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  simpa [_root_.div_eq_inv_mul, Real.norm_eq_abs, abs_of_nonneg h0] using n.cast_le_pow_div_sub h1
#align is_o_pow_const_const_pow_of_one_lt isLittleO_pow_const_const_pow_of_one_lt

/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
theorem isLittleO_coe_const_pow_of_one_lt {R : Type*} [NormedRing R] {r : ℝ} (hr : 1 < r) :
    ((↑) : ℕ → R) =o[atTop] fun n ↦ r ^ n := by
  simpa only [pow_one] using @isLittleO_pow_const_const_pow_of_one_lt R _ 1 _ hr
#align is_o_coe_const_pow_of_one_lt isLittleO_coe_const_pow_of_one_lt

/-- If `‖r₁‖ < r₂`, then for any natural `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
theorem isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type*} [NormedRing R] (k : ℕ)
    {r₁ : R} {r₂ : ℝ} (h : ‖r₁‖ < r₂) :
    (fun n ↦ (n : R) ^ k * r₁ ^ n : ℕ → R) =o[atTop] fun n ↦ r₂ ^ n := by
  by_cases h0 : r₁ = 0
  · refine (isLittleO_zero _ _).congr' (mem_atTop_sets.2 <| ⟨1, fun n hn ↦ ?_⟩) EventuallyEq.rfl
    simp [zero_pow (one_le_iff_ne_zero.1 hn), h0]
  rw [← Ne, ← norm_pos_iff] at h0
  have A : (fun n ↦ (n : R) ^ k : ℕ → R) =o[atTop] fun n ↦ (r₂ / ‖r₁‖) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h)
  suffices (fun n ↦ r₁ ^ n) =O[atTop] fun n ↦ ‖r₁‖ ^ n by
    simpa [div_mul_cancel₀ _ (pow_pos h0 _).ne'] using A.mul_isBigO this
  exact IsBigO.of_bound 1 (by simpa using eventually_norm_pow_le r₁)
#align is_o_pow_const_mul_const_pow_const_pow_of_norm_lt isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt

theorem tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n ↦ (n : ℝ) ^ k / r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  (isLittleO_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero
#align tendsto_pow_const_div_const_pow_of_one_lt tendsto_pow_const_div_const_pow_of_one_lt

/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n ↦ (n : ℝ) ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  by_cases h0 : r = 0
  · exact tendsto_const_nhds.congr'
      (mem_atTop_sets.2 ⟨1, fun n hn ↦ by simp [zero_lt_one.trans_le hn |>.ne', h0]⟩)
  have hr' : 1 < |r|⁻¹ := one_lt_inv (abs_pos.2 h0) hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'
#align tendsto_pow_const_mul_const_pow_of_abs_lt_one tendsto_pow_const_mul_const_pow_of_abs_lt_one

/-- If `0 ≤ r < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`.
This is a specialized version of `tendsto_pow_const_mul_const_pow_of_abs_lt_one`, singled out
for ease of application. -/
theorem tendsto_pow_const_mul_const_pow_of_lt_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n ↦ (n : ℝ) ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)
#align tendsto_pow_const_mul_const_pow_of_lt_one tendsto_pow_const_mul_const_pow_of_lt_one

/-- If `|r| < 1`, then `n * r ^ n` tends to zero. -/
theorem tendsto_self_mul_const_pow_of_abs_lt_one {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n ↦ n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr
#align tendsto_self_mul_const_pow_of_abs_lt_one tendsto_self_mul_const_pow_of_abs_lt_one

/-- If `0 ≤ r < 1`, then `n * r ^ n` tends to zero. This is a specialized version of
`tendsto_self_mul_const_pow_of_abs_lt_one`, singled out for ease of application. -/
theorem tendsto_self_mul_const_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n ↦ n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r
#align tendsto_self_mul_const_pow_of_lt_one tendsto_self_mul_const_pow_of_lt_one

/-- In a normed ring, the powers of an element x with `‖x‖ < 1` tend to zero. -/
theorem tendsto_pow_atTop_nhds_zero_of_norm_lt_one {R : Type*} [NormedRing R] {x : R}
    (h : ‖x‖ < 1) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h
#align tendsto_pow_at_top_nhds_0_of_norm_lt_1 tendsto_pow_atTop_nhds_zero_of_norm_lt_one
@[deprecated (since := "2024-01-31")]
alias tendsto_pow_atTop_nhds_0_of_norm_lt_1 := tendsto_pow_atTop_nhds_zero_of_norm_lt_one

theorem tendsto_pow_atTop_nhds_zero_of_abs_lt_one {r : ℝ} (h : |r| < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one h
#align tendsto_pow_at_top_nhds_0_of_abs_lt_1 tendsto_pow_atTop_nhds_zero_of_abs_lt_one
@[deprecated (since := "2024-01-31")]
alias tendsto_pow_atTop_nhds_0_of_abs_lt_1 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one

/-! ### Geometric series-/


section Geometric

variable {K : Type*} [NormedDivisionRing K] {ξ : K}

theorem hasSum_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : HasSum (fun n : ℕ ↦ ξ ^ n) (1 - ξ)⁻¹ := by
  have xi_ne_one : ξ ≠ 1 := by
    contrapose! h
    simp [h]
  have A : Tendsto (fun n ↦ (ξ ^ n - 1) * (ξ - 1)⁻¹) atTop (𝓝 ((0 - 1) * (ξ - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one h).sub tendsto_const_nhds).mul tendsto_const_nhds
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  · simpa [geom_sum_eq, xi_ne_one, neg_inv, div_eq_mul_inv] using A
  · simp [norm_pow, summable_geometric_of_lt_one (norm_nonneg _) h]
#align has_sum_geometric_of_norm_lt_1 hasSum_geometric_of_norm_lt_one

@[deprecated (since := "2024-01-31")]
alias hasSum_geometric_of_norm_lt_1 := hasSum_geometric_of_norm_lt_one

theorem summable_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : Summable fun n : ℕ ↦ ξ ^ n :=
  ⟨_, hasSum_geometric_of_norm_lt_one h⟩
#align summable_geometric_of_norm_lt_1 summable_geometric_of_norm_lt_one

@[deprecated (since := "2024-01-31")]
alias summable_geometric_of_norm_lt_1 := summable_geometric_of_norm_lt_one

theorem tsum_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : ∑' n : ℕ, ξ ^ n = (1 - ξ)⁻¹ :=
  (hasSum_geometric_of_norm_lt_one h).tsum_eq
#align tsum_geometric_of_norm_lt_1 tsum_geometric_of_norm_lt_one

@[deprecated (since := "2024-01-31")]
alias tsum_geometric_of_norm_lt_1 := tsum_geometric_of_norm_lt_one

theorem hasSum_geometric_of_abs_lt_one {r : ℝ} (h : |r| < 1) :
    HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ :=
  hasSum_geometric_of_norm_lt_one h
#align has_sum_geometric_of_abs_lt_1 hasSum_geometric_of_abs_lt_one

@[deprecated (since := "2024-01-31")]
alias hasSum_geometric_of_abs_lt_1 := hasSum_geometric_of_abs_lt_one

theorem summable_geometric_of_abs_lt_one {r : ℝ} (h : |r| < 1) : Summable fun n : ℕ ↦ r ^ n :=
  summable_geometric_of_norm_lt_one h
#align summable_geometric_of_abs_lt_1 summable_geometric_of_abs_lt_one

@[deprecated (since := "2024-01-31")]
alias summable_geometric_of_abs_lt_1 := summable_geometric_of_abs_lt_one

theorem tsum_geometric_of_abs_lt_one {r : ℝ} (h : |r| < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_one h
#align tsum_geometric_of_abs_lt_1 tsum_geometric_of_abs_lt_one

@[deprecated (since := "2024-01-31")]
alias tsum_geometric_of_abs_lt_1 := tsum_geometric_of_abs_lt_one

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp]
theorem summable_geometric_iff_norm_lt_one : (Summable fun n : ℕ ↦ ξ ^ n) ↔ ‖ξ‖ < 1 := by
  refine ⟨fun h ↦ ?_, summable_geometric_of_norm_lt_one⟩
  obtain ⟨k : ℕ, hk : dist (ξ ^ k) 0 < 1⟩ :=
    (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists
  simp only [norm_pow, dist_zero_right] at hk
  rw [← one_pow k] at hk
  exact lt_of_pow_lt_pow_left _ zero_le_one hk
#align summable_geometric_iff_norm_lt_1 summable_geometric_iff_norm_lt_one

@[deprecated (since := "2024-01-31")]
alias summable_geometric_iff_norm_lt_1 := summable_geometric_iff_norm_lt_one

end Geometric

section MulGeometric

theorem summable_norm_pow_mul_geometric_of_norm_lt_one {R : Type*} [NormedRing R] (k : ℕ) {r : R}
    (hr : ‖r‖ < 1) : Summable fun n : ℕ ↦ ‖((n : R) ^ k * r ^ n : R)‖ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  exact summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h)
    (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt _ hrr').isBigO.norm_left
#align summable_norm_pow_mul_geometric_of_norm_lt_1 summable_norm_pow_mul_geometric_of_norm_lt_one

@[deprecated (since := "2024-01-31")]
alias summable_norm_pow_mul_geometric_of_norm_lt_1 := summable_norm_pow_mul_geometric_of_norm_lt_one

theorem summable_pow_mul_geometric_of_norm_lt_one {R : Type*} [NormedRing R] [CompleteSpace R]
    (k : ℕ) {r : R} (hr : ‖r‖ < 1) : Summable (fun n ↦ (n : R) ^ k * r ^ n : ℕ → R) :=
  .of_norm <| summable_norm_pow_mul_geometric_of_norm_lt_one _ hr
#align summable_pow_mul_geometric_of_norm_lt_1 summable_pow_mul_geometric_of_norm_lt_one

@[deprecated (since := "2024-01-31")]
alias summable_pow_mul_geometric_of_norm_lt_1 := summable_pow_mul_geometric_of_norm_lt_one

/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `HasSum` version. -/
theorem hasSum_coe_mul_geometric_of_norm_lt_one {𝕜 : Type*} [NormedDivisionRing 𝕜] [CompleteSpace 𝕜]
    {r : 𝕜} (hr : ‖r‖ < 1) : HasSum (fun n ↦ n * r ^ n : ℕ → 𝕜) (r / (1 - r) ^ 2) := by
  have A : Summable (fun n ↦ (n : 𝕜) * r ^ n : ℕ → 𝕜) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have B : HasSum (r ^ · : ℕ → 𝕜) (1 - r)⁻¹ := hasSum_geometric_of_norm_lt_one hr
  refine A.hasSum_iff.2 ?_
  have hr' : r ≠ 1 := by
    rintro rfl
    simp [lt_irrefl] at hr
  set s : 𝕜 := ∑' n : ℕ, n * r ^ n
  have : Commute (1 - r) s :=
    .tsum_right _ fun _ =>
      .sub_left (.one_left _) (.mul_right (Nat.commute_cast _ _) (.pow_right (.refl _) _))
  calc
    s = s * (1 - r) / (1 - r) := (mul_div_cancel_right₀ _ (sub_ne_zero.2 hr'.symm)).symm
    _ = (1 - r) * s / (1 - r) := by rw [this.eq]
    _ = (s - r * s) / (1 - r) := by rw [_root_.sub_mul, one_mul]
    _ = (((0 : ℕ) * r ^ 0 + ∑' n : ℕ, (n + 1 : ℕ) * r ^ (n + 1)) - r * s) / (1 - r) := by
      rw [← tsum_eq_zero_add A]
    _ = ((r * ∑' n : ℕ, ↑(n + 1) * r ^ n) - r * s) / (1 - r) := by
      simp only [cast_zero, pow_zero, mul_one, _root_.pow_succ', (Nat.cast_commute _ r).left_comm,
        _root_.tsum_mul_left, zero_add]
    _ = r / (1 - r) ^ 2 := by
      simp [add_mul, tsum_add A B.summable, mul_add, B.tsum_eq, ← div_eq_mul_inv, sq,
        div_mul_eq_div_div_swap]
#align has_sum_coe_mul_geometric_of_norm_lt_1 hasSum_coe_mul_geometric_of_norm_lt_one

@[deprecated (since := "2024-01-31")]
alias hasSum_coe_mul_geometric_of_norm_lt_1 := hasSum_coe_mul_geometric_of_norm_lt_one

/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
theorem tsum_coe_mul_geometric_of_norm_lt_one {𝕜 : Type*} [NormedDivisionRing 𝕜] [CompleteSpace 𝕜]
    {r : 𝕜} (hr : ‖r‖ < 1) : (∑' n : ℕ, n * r ^ n : 𝕜) = r / (1 - r) ^ 2 :=
  (hasSum_coe_mul_geometric_of_norm_lt_one hr).tsum_eq
#align tsum_coe_mul_geometric_of_norm_lt_1 tsum_coe_mul_geometric_of_norm_lt_one

@[deprecated (since := "2024-01-31")]
alias tsum_coe_mul_geometric_of_norm_lt_1 := tsum_coe_mul_geometric_of_norm_lt_one

end MulGeometric

section SummableLeGeometric

variable [SeminormedAddCommGroup α] {r C : ℝ} {f : ℕ → α}

nonrec theorem SeminormedAddCommGroup.cauchySeq_of_le_geometric {C : ℝ} {r : ℝ} (hr : r < 1)
    {u : ℕ → α} (h : ∀ n, ‖u n - u (n + 1)‖ ≤ C * r ^ n) : CauchySeq u :=
  cauchySeq_of_le_geometric r C hr (by simpa [dist_eq_norm] using h)
#align seminormed_add_comm_group.cauchy_seq_of_le_geometric SeminormedAddCommGroup.cauchySeq_of_le_geometric

theorem dist_partial_sum_le_of_le_geometric (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) (n : ℕ) :
    dist (∑ i ∈ range n, f i) (∑ i ∈ range (n + 1), f i) ≤ C * r ^ n := by
  rw [sum_range_succ, dist_eq_norm, ← norm_neg, neg_sub, add_sub_cancel_left]
  exact hf n
#align dist_partial_sum_le_of_le_geometric dist_partial_sum_le_of_le_geometric

/-- If `‖f n‖ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
theorem cauchySeq_finset_of_geometric_bound (hr : r < 1) (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) :
    CauchySeq fun s : Finset ℕ ↦ ∑ x ∈ s, f x :=
  cauchySeq_finset_of_norm_bounded _
    (aux_hasSum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).summable hf
#align cauchy_seq_finset_of_geometric_bound cauchySeq_finset_of_geometric_bound

/-- If `‖f n‖ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
theorem norm_sub_le_of_geometric_bound_of_hasSum (hr : r < 1) (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) {a : α}
    (ha : HasSum f a) (n : ℕ) : ‖(∑ x ∈ Finset.range n, f x) - a‖ ≤ C * r ^ n / (1 - r) := by
  rw [← dist_eq_norm]
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
  exact ha.tendsto_sum_nat
#align norm_sub_le_of_geometric_bound_of_has_sum norm_sub_le_of_geometric_bound_of_hasSum

@[simp]
theorem dist_partial_sum (u : ℕ → α) (n : ℕ) :
    dist (∑ k ∈ range (n + 1), u k) (∑ k ∈ range n, u k) = ‖u n‖ := by
  simp [dist_eq_norm, sum_range_succ]
#align dist_partial_sum dist_partial_sum

@[simp]
theorem dist_partial_sum' (u : ℕ → α) (n : ℕ) :
    dist (∑ k ∈ range n, u k) (∑ k ∈ range (n + 1), u k) = ‖u n‖ := by
  simp [dist_eq_norm', sum_range_succ]
#align dist_partial_sum' dist_partial_sum'

theorem cauchy_series_of_le_geometric {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ‖u n‖ ≤ C * r ^ n) : CauchySeq fun n ↦ ∑ k ∈ range n, u k :=
  cauchySeq_of_le_geometric r C hr (by simp [h])
#align cauchy_series_of_le_geometric cauchy_series_of_le_geometric

theorem NormedAddCommGroup.cauchy_series_of_le_geometric' {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ‖u n‖ ≤ C * r ^ n) : CauchySeq fun n ↦ ∑ k ∈ range (n + 1), u k :=
  (cauchy_series_of_le_geometric hr h).comp_tendsto <| tendsto_add_atTop_nat 1
#align normed_add_comm_group.cauchy_series_of_le_geometric' NormedAddCommGroup.cauchy_series_of_le_geometric'

theorem NormedAddCommGroup.cauchy_series_of_le_geometric'' {C : ℝ} {u : ℕ → α} {N : ℕ} {r : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1) (h : ∀ n ≥ N, ‖u n‖ ≤ C * r ^ n) :
    CauchySeq fun n ↦ ∑ k ∈ range (n + 1), u k := by
  set v : ℕ → α := fun n ↦ if n < N then 0 else u n
  have hC : 0 ≤ C :=
    (mul_nonneg_iff_of_pos_right <| pow_pos hr₀ N).mp ((norm_nonneg _).trans <| h N <| le_refl N)
  have : ∀ n ≥ N, u n = v n := by
    intro n hn
    simp [v, hn, if_neg (not_lt.mpr hn)]
  apply cauchySeq_sum_of_eventually_eq this
    (NormedAddCommGroup.cauchy_series_of_le_geometric' hr₁ _)
  · exact C
  intro n
  simp only [v]
  split_ifs with H
  · rw [norm_zero]
    exact mul_nonneg hC (pow_nonneg hr₀.le _)
  · push_neg at H
    exact h _ H
#align normed_add_comm_group.cauchy_series_of_le_geometric'' NormedAddCommGroup.cauchy_series_of_le_geometric''

/-- The term norms of any convergent series are bounded by a constant. -/
lemma exists_norm_le_of_cauchySeq (h : CauchySeq fun n ↦ ∑ k ∈ range n, f k) :
    ∃ C, ∀ n, ‖f n‖ ≤ C := by
  obtain ⟨b, ⟨_, key, _⟩⟩ := cauchySeq_iff_le_tendsto_0.mp h
  refine ⟨b 0, fun n ↦ ?_⟩
  simpa only [dist_partial_sum'] using key n (n + 1) 0 (_root_.zero_le _) (_root_.zero_le _)

end SummableLeGeometric

section NormedRingGeometric

variable {R : Type*} [NormedRing R] [CompleteSpace R]

open NormedSpace

/-- A geometric series in a complete normed ring is summable.
Proved above (same name, different namespace) for not-necessarily-complete normed fields. -/
theorem NormedRing.summable_geometric_of_norm_lt_one (x : R) (h : ‖x‖ < 1) :
    Summable fun n : ℕ ↦ x ^ n :=
  have h1 : Summable fun n : ℕ ↦ ‖x‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) h
  h1.of_norm_bounded_eventually_nat _ (eventually_norm_pow_le x)
#align normed_ring.summable_geometric_of_norm_lt_1 NormedRing.summable_geometric_of_norm_lt_one
@[deprecated (since := "2024-01-31")]
alias NormedRing.summable_geometric_of_norm_lt_1 := NormedRing.summable_geometric_of_norm_lt_one

/-- Bound for the sum of a geometric series in a normed ring. This formula does not assume that the
normed ring satisfies the axiom `‖1‖ = 1`. -/
theorem NormedRing.tsum_geometric_of_norm_lt_one (x : R) (h : ‖x‖ < 1) :
    ‖∑' n : ℕ, x ^ n‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖x‖)⁻¹ := by
  rw [tsum_eq_zero_add (summable_geometric_of_norm_lt_one x h)]
  simp only [_root_.pow_zero]
  refine le_trans (norm_add_le _ _) ?_
  have : ‖∑' b : ℕ, (fun n ↦ x ^ (n + 1)) b‖ ≤ (1 - ‖x‖)⁻¹ - 1 := by
    refine tsum_of_norm_bounded ?_ fun b ↦ norm_pow_le' _ (Nat.succ_pos b)
    convert (hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_lt_one (norm_nonneg x) h)
    simp
  linarith
#align normed_ring.tsum_geometric_of_norm_lt_1 NormedRing.tsum_geometric_of_norm_lt_one

@[deprecated (since := "2024-01-31")]
alias NormedRing.tsum_geometric_of_norm_lt_1 := NormedRing.tsum_geometric_of_norm_lt_one

theorem geom_series_mul_neg (x : R) (h : ‖x‖ < 1) : (∑' i : ℕ, x ^ i) * (1 - x) = 1 := by
  have := (NormedRing.summable_geometric_of_norm_lt_one x h).hasSum.mul_right (1 - x)
  refine tendsto_nhds_unique this.tendsto_sum_nat ?_
  have : Tendsto (fun n : ℕ ↦ 1 - x ^ n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h)
  convert← this
  rw [← geom_sum_mul_neg, Finset.sum_mul]
#align geom_series_mul_neg geom_series_mul_neg

theorem mul_neg_geom_series (x : R) (h : ‖x‖ < 1) : ((1 - x) * ∑' i : ℕ, x ^ i) = 1 := by
  have := (NormedRing.summable_geometric_of_norm_lt_one x h).hasSum.mul_left (1 - x)
  refine tendsto_nhds_unique this.tendsto_sum_nat ?_
  have : Tendsto (fun n : ℕ ↦ 1 - x ^ n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h)
  convert← this
  rw [← mul_neg_geom_sum, Finset.mul_sum]
#align mul_neg_geom_series mul_neg_geom_series

theorem geom_series_succ (x : R) (h : ‖x‖ < 1) : ∑' i : ℕ, x ^ (i + 1) = ∑' i : ℕ, x ^ i - 1 := by
  rw [eq_sub_iff_add_eq, tsum_eq_zero_add (NormedRing.summable_geometric_of_norm_lt_one x h),
    pow_zero, add_comm]

theorem geom_series_mul_shift (x : R) (h : ‖x‖ < 1) :
    x * ∑' i : ℕ, x ^ i = ∑' i : ℕ, x ^ (i + 1) := by
  simp_rw [← (NormedRing.summable_geometric_of_norm_lt_one _ h).tsum_mul_left, ← _root_.pow_succ']

theorem geom_series_mul_one_add (x : R) (h : ‖x‖ < 1) :
    (1 + x) * ∑' i : ℕ, x ^ i = 2 * ∑' i : ℕ, x ^ i - 1 := by
  rw [add_mul, one_mul, geom_series_mul_shift x h, geom_series_succ x h, two_mul, add_sub_assoc]

end NormedRingGeometric

/-! ### Summability tests based on comparison with geometric series -/

theorem summable_of_ratio_norm_eventually_le {α : Type*} [SeminormedAddCommGroup α]
    [CompleteSpace α] {f : ℕ → α} {r : ℝ} (hr₁ : r < 1)
    (h : ∀ᶠ n in atTop, ‖f (n + 1)‖ ≤ r * ‖f n‖) : Summable f := by
  by_cases hr₀ : 0 ≤ r
  · rw [eventually_atTop] at h
    rcases h with ⟨N, hN⟩
    rw [← @summable_nat_add_iff α _ _ _ _ N]
    refine .of_norm_bounded (fun n ↦ ‖f N‖ * r ^ n)
      (Summable.mul_left _ <| summable_geometric_of_lt_one hr₀ hr₁) fun n ↦ ?_
    simp only
    conv_rhs => rw [mul_comm, ← zero_add N]
    refine le_geom (u := fun n ↦ ‖f (n + N)‖) hr₀ n fun i _ ↦ ?_
    convert hN (i + N) (N.le_add_left i) using 3
    ac_rfl
  · push_neg at hr₀
    refine .of_norm_bounded_eventually_nat 0 summable_zero ?_
    filter_upwards [h] with _ hn
    by_contra! h
    exact not_lt.mpr (norm_nonneg _) (lt_of_le_of_lt hn <| mul_neg_of_neg_of_pos hr₀ h)
#align summable_of_ratio_norm_eventually_le summable_of_ratio_norm_eventually_le

theorem summable_of_ratio_test_tendsto_lt_one {α : Type*} [NormedAddCommGroup α] [CompleteSpace α]
    {f : ℕ → α} {l : ℝ} (hl₁ : l < 1) (hf : ∀ᶠ n in atTop, f n ≠ 0)
    (h : Tendsto (fun n ↦ ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) : Summable f := by
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
  refine summable_of_ratio_norm_eventually_le hr₁ ?_
  filter_upwards [eventually_le_of_tendsto_lt hr₀ h, hf] with _ _ h₁
  rwa [← div_le_iff (norm_pos_iff.mpr h₁)]
#align summable_of_ratio_test_tendsto_lt_one summable_of_ratio_test_tendsto_lt_one

theorem not_summable_of_ratio_norm_eventually_ge {α : Type*} [SeminormedAddCommGroup α] {f : ℕ → α}
    {r : ℝ} (hr : 1 < r) (hf : ∃ᶠ n in atTop, ‖f n‖ ≠ 0)
    (h : ∀ᶠ n in atTop, r * ‖f n‖ ≤ ‖f (n + 1)‖) : ¬Summable f := by
  rw [eventually_atTop] at h
  rcases h with ⟨N₀, hN₀⟩
  rw [frequently_atTop] at hf
  rcases hf N₀ with ⟨N, hNN₀ : N₀ ≤ N, hN⟩
  rw [← @summable_nat_add_iff α _ _ _ _ N]
  refine mt Summable.tendsto_atTop_zero
    fun h' ↦ not_tendsto_atTop_of_tendsto_nhds (tendsto_norm_zero.comp h') ?_
  convert tendsto_atTop_of_geom_le _ hr _
  · refine lt_of_le_of_ne (norm_nonneg _) ?_
    intro h''
    specialize hN₀ N hNN₀
    simp only [comp_apply, zero_add] at h''
    exact hN h''.symm
  · intro i
    dsimp only [comp_apply]
    convert hN₀ (i + N) (hNN₀.trans (N.le_add_left i)) using 3
    ac_rfl
#align not_summable_of_ratio_norm_eventually_ge not_summable_of_ratio_norm_eventually_ge

theorem not_summable_of_ratio_test_tendsto_gt_one {α : Type*} [SeminormedAddCommGroup α]
    {f : ℕ → α} {l : ℝ} (hl : 1 < l) (h : Tendsto (fun n ↦ ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) :
    ¬Summable f := by
  have key : ∀ᶠ n in atTop, ‖f n‖ ≠ 0 := by
    filter_upwards [eventually_ge_of_tendsto_gt hl h] with _ hn hc
    rw [hc, _root_.div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩
  refine not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently ?_
  filter_upwards [eventually_ge_of_tendsto_gt hr₁ h, key] with _ _ h₁
  rwa [← le_div_iff (lt_of_le_of_ne (norm_nonneg _) h₁.symm)]
#align not_summable_of_ratio_test_tendsto_gt_one not_summable_of_ratio_test_tendsto_gt_one

section NormedDivisionRing

variable [NormedDivisionRing α] [CompleteSpace α] {f : ℕ → α}

/-- If a power series converges at `w`, it converges absolutely at all `z` of smaller norm. -/
theorem summable_powerSeries_of_norm_lt {w z : α}
    (h : CauchySeq fun n ↦ ∑ i ∈ range n, f i * w ^ i) (hz : ‖z‖ < ‖w‖) :
    Summable fun n ↦ f n * z ^ n := by
  have hw : 0 < ‖w‖ := (norm_nonneg z).trans_lt hz
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq h
  rw [summable_iff_cauchySeq_finset]
  refine cauchySeq_finset_of_geometric_bound (r := ‖z‖ / ‖w‖) (C := C) ((div_lt_one hw).mpr hz)
    (fun n ↦ ?_)
  rw [norm_mul, norm_pow, div_pow, ← mul_comm_div]
  conv at hC => enter [n]; rw [norm_mul, norm_pow, ← _root_.le_div_iff (by positivity)]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg z) n)

/-- If a power series converges at 1, it converges absolutely at all `z` of smaller norm. -/
theorem summable_powerSeries_of_norm_lt_one {z : α}
    (h : CauchySeq fun n ↦ ∑ i ∈ range n, f i) (hz : ‖z‖ < 1) :
    Summable fun n ↦ f n * z ^ n :=
  summable_powerSeries_of_norm_lt (w := 1) (by simp [h]) (by simp [hz])

end NormedDivisionRing

section

/-! ### Dirichlet and alternating series tests -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}

/-- **Dirichlet's test** for monotone sequences. -/
theorem Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) (hgb : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ b) :
    CauchySeq fun n ↦ ∑ i ∈ range n, f i • z i := by
  rw [← cauchySeq_shift 1]
  simp_rw [Finset.sum_range_by_parts _ _ (Nat.succ _), sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
    tsub_zero]
  apply (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
    ⟨b, eventually_map.mpr <| eventually_of_forall fun n ↦ hgb <| n + 1⟩).cauchySeq.add
  refine CauchySeq.neg ?_
  refine cauchySeq_range_of_norm_bounded _ ?_
    (fun n ↦ ?_ : ∀ n, ‖(f (n + 1) + -f n) • (Finset.range (n + 1)).sum z‖ ≤ b * |f (n + 1) - f n|)
  · simp_rw [abs_of_nonneg (sub_nonneg_of_le (hfa (Nat.le_succ _))), ← mul_sum]
    apply Real.uniformContinuous_const_mul.comp_cauchySeq
    simp_rw [sum_range_sub, sub_eq_add_neg]
    exact (Tendsto.cauchySeq hf0).add_const
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)
#align monotone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded

/-- **Dirichlet's test** for antitone sequences. -/
theorem Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) (hzb : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ b) :
    CauchySeq fun n ↦ ∑ i ∈ range n, f i • z i := by
  have hfa' : Monotone fun n ↦ -f n := fun _ _ hab ↦ neg_le_neg <| hfa hab
  have hf0' : Tendsto (fun n ↦ -f n) atTop (𝓝 0) := by
    convert hf0.neg
    norm_num
  convert (hfa'.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg
  simp
#align antitone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded

theorem norm_sum_neg_one_pow_le (n : ℕ) : ‖∑ i ∈ range n, (-1 : ℝ) ^ i‖ ≤ 1 := by
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num
#align norm_sum_neg_one_pow_le norm_sum_neg_one_pow_le

/-- The **alternating series test** for monotone sequences.
See also `Monotone.tendsto_alternating_series_of_tendsto_zero`. -/
theorem Monotone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le
#align monotone.cauchy_seq_alternating_series_of_tendsto_zero Monotone.cauchySeq_alternating_series_of_tendsto_zero

/-- The **alternating series test** for monotone sequences. -/
theorem Monotone.tendsto_alternating_series_of_tendsto_zero (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete <| hfa.cauchySeq_alternating_series_of_tendsto_zero hf0
#align monotone.tendsto_alternating_series_of_tendsto_zero Monotone.tendsto_alternating_series_of_tendsto_zero

/-- The **alternating series test** for antitone sequences.
See also `Antitone.tendsto_alternating_series_of_tendsto_zero`. -/
theorem Antitone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le
#align antitone.cauchy_seq_alternating_series_of_tendsto_zero Antitone.cauchySeq_alternating_series_of_tendsto_zero

/-- The **alternating series test** for antitone sequences. -/
theorem Antitone.tendsto_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete <| hfa.cauchySeq_alternating_series_of_tendsto_zero hf0
#align antitone.tendsto_alternating_series_of_tendsto_zero Antitone.tendsto_alternating_series_of_tendsto_zero

end

/-! ### Partial sum bounds on alternating convergent series -/

section

variable {E : Type*} [OrderedRing E] [TopologicalSpace E] [OrderClosedTopology E]
  {l : E} {f : ℕ → E}

/-- Partial sums of an alternating monotone series with an even number of terms provide
upper bounds on the limit. -/
theorem Monotone.tendsto_le_alternating_series
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfm : Monotone f) (k : ℕ) : l ≤ ∑ i ∈ range (2 * k), (-1) ^ i * f i := by
  have ha : Antitone (fun n ↦ ∑ i ∈ range (2 * n), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, one_mul,
      ← sub_eq_add_neg, sub_le_iff_le_add]
    gcongr
    exact hfm (by omega)
  exact ha.le_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; omega) tendsto_id)) _

/-- Partial sums of an alternating monotone series with an odd number of terms provide
lower bounds on the limit. -/
theorem Monotone.alternating_series_le_tendsto
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfm : Monotone f) (k : ℕ) : ∑ i ∈ range (2 * k + 1), (-1) ^ i * f i ≤ l := by
  have hm : Monotone (fun n ↦ ∑ i ∈ range (2 * n + 1), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      sum_range_succ _ (2 * n + 1 + 1), sum_range_succ _ (2 * n + 1)]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, neg_neg, one_mul,
      ← sub_eq_add_neg, sub_add_eq_add_sub, le_sub_iff_add_le]
    gcongr
    exact hfm (by omega)
  exact hm.ge_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; omega) tendsto_id)) _

/-- Partial sums of an alternating antitone series with an even number of terms provide
lower bounds on the limit. -/
theorem Antitone.alternating_series_le_tendsto
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfa : Antitone f) (k : ℕ) : ∑ i ∈ range (2 * k), (-1) ^ i * f i ≤ l := by
  have hm : Monotone (fun n ↦ ∑ i ∈ range (2 * n), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, one_mul,
      ← sub_eq_add_neg, le_sub_iff_add_le]
    gcongr
    exact hfa (by omega)
  exact hm.ge_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; omega) tendsto_id)) _

/-- Partial sums of an alternating antitone series with an odd number of terms provide
upper bounds on the limit. -/
theorem Antitone.tendsto_le_alternating_series
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfa : Antitone f) (k : ℕ) : l ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * f i := by
  have ha : Antitone (fun n ↦ ∑ i ∈ range (2 * n + 1), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, neg_neg, one_mul,
      ← sub_eq_add_neg, sub_add_eq_add_sub, sub_le_iff_le_add]
    gcongr
    exact hfa (by omega)
  exact ha.le_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; omega) tendsto_id)) _

end

/-!
### Factorial
-/

/-- The series `∑' n, x ^ n / n!` is summable of any `x : ℝ`. See also `expSeries_div_summable`
for a version that also works in `ℂ`, and `NormedSpace.expSeries_summable'` for a version
that works in any normed algebra over `ℝ` or `ℂ`. -/
theorem Real.summable_pow_div_factorial (x : ℝ) : Summable (fun n ↦ x ^ n / n ! : ℕ → ℝ) := by
  -- We start with trivial estimates
  have A : (0 : ℝ) < ⌊‖x‖⌋₊ + 1 := zero_lt_one.trans_le (by simp)
  have B : ‖x‖ / (⌊‖x‖⌋₊ + 1) < 1 := (div_lt_one A).2 (Nat.lt_floor_add_one _)
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊‖x‖⌋₊`.
  suffices ∀ n ≥ ⌊‖x‖⌋₊, ‖x ^ (n + 1) / (n + 1)!‖ ≤ ‖x‖ / (⌊‖x‖⌋₊ + 1) * ‖x ^ n / ↑n !‖ from
    summable_of_ratio_norm_eventually_le B (eventually_atTop.2 ⟨⌊‖x‖⌋₊, this⟩)
  -- Finally, we prove the upper estimate
  intro n hn
  calc
    ‖x ^ (n + 1) / (n + 1)!‖ = ‖x‖ / (n + 1) * ‖x ^ n / (n !)‖ := by
      rw [_root_.pow_succ', Nat.factorial_succ, Nat.cast_mul, ← _root_.div_mul_div_comm, norm_mul,
        norm_div, Real.norm_natCast, Nat.cast_succ]
    _ ≤ ‖x‖ / (⌊‖x‖⌋₊ + 1) * ‖x ^ n / (n !)‖ := by gcongr
#align real.summable_pow_div_factorial Real.summable_pow_div_factorial

theorem Real.tendsto_pow_div_factorial_atTop (x : ℝ) :
    Tendsto (fun n ↦ x ^ n / n ! : ℕ → ℝ) atTop (𝓝 0) :=
  (Real.summable_pow_div_factorial x).tendsto_atTop_zero
#align real.tendsto_pow_div_factorial_at_top Real.tendsto_pow_div_factorial_atTop
