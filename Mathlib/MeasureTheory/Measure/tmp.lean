/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Yury G. Kudryashov, Patrick Massot

! This file was ported from Lean 3 source module analysis.specific_limits.basic
! leanprover-community/mathlib commit 57ac39bd365c2f80589a700f9fbb664d3a1a30c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Order.Filter.Archimedean
import Mathlib.Order.Iterate
import Mathlib.Topology.Instances.ENNReal

/-!
# Tmp Module

import Mathlib.Topology.Algebra.Algebra causes error
-/

noncomputable section

open Classical Set Function Filter Finset Metric

open Classical Topology Nat BigOperators uniformity NNReal ENNReal

theorem tendsto_add_one_pow_atTop_atTop_of_pos [LinearOrderedSemiring α] [Archimedean α] {r : α}
    (h : 0 < r) : Tendsto (fun n : ℕ => (r + 1) ^ n) atTop atTop :=
  (tendsto_atTop_atTop_of_monotone' fun _ _ => pow_le_pow (le_add_of_nonneg_left (le_of_lt h))) <|
    not_bddAbove_iff.2 fun _ => Set.exists_range_iff.2 <| add_one_pow_unbounded_of_pos _ h

theorem tendsto_pow_atTop_atTop_of_one_lt [LinearOrderedRing α] [Archimedean α] {r : α}
    (h : 1 < r) : Tendsto (fun n : ℕ => r ^ n) atTop atTop :=
  sub_add_cancel r 1 ▸ tendsto_add_one_pow_atTop_atTop_of_pos (sub_pos.2 h)

theorem tendsto_pow_atTop_nhds_0_of_lt_1 {𝕜 : Type _} [LinearOrderedField 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  h₁.eq_or_lt.elim
    (fun hr => (tendsto_add_atTop_iff_nat 1).mp <| by
      simp [_root_.pow_succ, ← hr, tendsto_const_nhds])
    (fun hr =>
      have := one_lt_inv hr h₂ |> tendsto_pow_atTop_atTop_of_one_lt
      (tendsto_inv_atTop_zero.comp this).congr fun n => by simp)

theorem hasSum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
  have : r ≠ 1 := ne_of_lt h₂
  have : Tendsto (fun n => (r ^ n - 1) * (r - 1)⁻¹) atTop (𝓝 ((0 - 1) * (r - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_0_of_lt_1 h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds
  (hasSum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr <| by
    simp_all [neg_inv, geom_sum_eq, div_eq_mul_inv]

theorem hasSum_geometric_two' (a : ℝ) : HasSum (fun n : ℕ => a / 2 / 2 ^ n) a := by
  convert HasSum.mul_left (a / 2)
      (hasSum_geometric_of_lt_1 (le_of_lt one_half_pos) one_half_lt_one) using 1
  · funext n
    simp
    rfl
  · norm_num

def posSumOfEncodable {ε : ℝ} (hε : 0 < ε) (ι) [Encodable ι] :
    { ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c ≤ ε } := by
  let f n := ε / 2 / 2 ^ n
  have hf : HasSum f ε := hasSum_geometric_two' _
  have f0 : ∀ n, 0 < f n := fun n => div_pos (half_pos hε) (pow_pos (by simp) _)
  refine' ⟨f ∘ Encodable.encode, fun i => f0 _, _⟩
  rcases hf.summable.comp_injective (@Encodable.encode_injective ι _) with ⟨c, hg⟩
  refine' ⟨c, hg, hasSum_le_inj _ (@Encodable.encode_injective ι _) _ _ hg hf⟩
  · intro i _
    exact le_of_lt (f0 _)
  · intro n
    exact le_rfl

theorem NNReal.exists_pos_sum_of_countable {ε : ℝ≥0} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c < ε := by
  cases nonempty_encodable ι
  obtain ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε)
  obtain ⟨ε', hε', c, hc, hcε⟩ := posSumOfEncodable a0 ι
  exact
    ⟨fun i => ⟨ε' i, (hε' i).le⟩, fun i => NNReal.coe_lt_coe.1 <| hε' i,
      ⟨c, hasSum_le (fun i => (hε' i).le) hasSum_zero hc⟩, NNReal.hasSum_coe.1 hc,
      aε.trans_le' <| NNReal.coe_le_coe.1 hcε⟩

theorem ENNReal.exists_pos_sum_of_countable {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ (∑' i, (ε' i : ℝ≥0∞)) < ε := by
  rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, _⟩
  rcases NNReal.exists_pos_sum_of_countable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩
  exact ⟨ε', hp, (ENNReal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩
