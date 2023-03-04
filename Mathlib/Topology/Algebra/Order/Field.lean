/-
Copyright (c) 2022 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Devon Tuma, Eric Rodriguez, Oliver Nash

! This file was ported from Lean 3 source module topology.algebra.order.field
! leanprover-community/mathlib commit 9a59dcb7a2d06bf55da57b9030169219980660cd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Positivity
import Mathbin.Tactic.Linarith.Default
import Mathbin.Topology.Algebra.Order.Group
import Mathbin.Topology.Algebra.Field

/-!
# Topologies on linear ordered fields

-/


open Set Filter TopologicalSpace

open Function

open OrderDual (toDual ofDual)

open Topology Classical Filter

variable {α β : Type _}

variable [LinearOrderedField α] [TopologicalSpace α] [OrderTopology α]

variable {l : Filter β} {f g : β → α}

section continuous_mul

theorem mul_tendsto_nhds_zero_right (x : α) :
    Tendsto (uncurry ((· * ·) : α → α → α)) (𝓝 0 ×ᶠ 𝓝 x) <| 𝓝 0 :=
  by
  have hx : 0 < 2 * (1 + |x|) := by positivity
  rw [((nhds_basis_zero_abs_sub_lt α).Prod <| nhds_basis_abs_sub_lt x).tendsto_iffₓ
      (nhds_basis_zero_abs_sub_lt α)]
  refine' fun ε ε_pos => ⟨(ε / (2 * (1 + |x|)), 1), ⟨div_pos ε_pos hx, zero_lt_one⟩, _⟩
  suffices ∀ a b : α, |a| < ε / (2 * (1 + |x|)) → |b - x| < 1 → |a| * |b| < ε by
    simpa only [and_imp, Prod.forall, mem_prod, ← abs_mul]
  intro a b h h'
  refine' lt_of_le_of_lt (mul_le_mul_of_nonneg_left _ (abs_nonneg a)) ((lt_div_iff hx).1 h)
  calc
    |b| = |b - x + x| := by rw [sub_add_cancel b x]
    _ ≤ |b - x| + |x| := (abs_add (b - x) x)
    _ ≤ 2 * (1 + |x|) := by linarith
    
#align mul_tendsto_nhds_zero_right mul_tendsto_nhds_zero_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mul_tendsto_nhds_zero_left (x : α) :
    Tendsto (uncurry ((· * ·) : α → α → α)) (𝓝 x ×ᶠ 𝓝 0) <| 𝓝 0 :=
  by
  intro s hs
  have := mul_tendsto_nhds_zero_right x hs
  rw [Filter.mem_map, mem_prod_iff] at this⊢
  obtain ⟨U, hU, V, hV, h⟩ := this
  exact
    ⟨V, hV, U, hU, fun y hy =>
      (mul_comm y.2 y.1 ▸ h (⟨hy.2, hy.1⟩ : Prod.mk y.2 y.1 ∈ U ×ˢ V) : y.1 * y.2 ∈ s)⟩
#align mul_tendsto_nhds_zero_left mul_tendsto_nhds_zero_left

theorem nhds_eq_map_mul_left_nhds_one {x₀ : α} (hx₀ : x₀ ≠ 0) :
    𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1) :=
  by
  have hx₀' : 0 < |x₀| := abs_pos.2 hx₀
  refine' Filter.ext fun t => _
  simp only [exists_prop, set_of_subset_set_of, (nhds_basis_abs_sub_lt x₀).mem_iff,
    (nhds_basis_abs_sub_lt (1 : α)).mem_iff, Filter.mem_map']
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨i, hi, hit⟩ := h
    refine' ⟨i / |x₀|, div_pos hi (abs_pos.2 hx₀), fun x hx => hit _⟩
    calc
      |x₀ * x - x₀| = |x₀ * (x - 1)| := congr_arg abs (by ring_nf)
      _ = |x₀| * |x - 1| := (abs_mul x₀ (x - 1))
      _ < |x₀| * (i / |x₀|) := (mul_lt_mul' le_rfl hx (by positivity) (abs_pos.2 hx₀))
      _ = |x₀| * i / |x₀| := by ring
      _ = i := mul_div_cancel_left i fun h => hx₀ (abs_eq_zero.1 h)
      
  · obtain ⟨i, hi, hit⟩ := h
    refine' ⟨i * |x₀|, mul_pos hi (abs_pos.2 hx₀), fun x hx => _⟩
    have : |x / x₀ - 1| < i
    calc
      |x / x₀ - 1| = |x / x₀ - x₀ / x₀| := by rw [div_self hx₀]
      _ = |(x - x₀) / x₀| := (congr_arg abs (sub_div x x₀ x₀).symm)
      _ = |x - x₀| / |x₀| := (abs_div (x - x₀) x₀)
      _ < i * |x₀| / |x₀| := (div_lt_div_of_lt (abs_pos.2 hx₀) hx)
      _ = i := by rw [← mul_div_assoc', div_self (ne_of_lt <| abs_pos.2 hx₀).symm, mul_one]
      
    specialize hit (x / x₀) this
    rwa [mul_div_assoc', mul_div_cancel_left x hx₀] at hit
#align nhds_eq_map_mul_left_nhds_one nhds_eq_map_mul_left_nhds_one

theorem nhds_eq_map_mul_right_nhds_one {x₀ : α} (hx₀ : x₀ ≠ 0) :
    𝓝 x₀ = map (fun x => x * x₀) (𝓝 1) := by
  simp_rw [mul_comm _ x₀, nhds_eq_map_mul_left_nhds_one hx₀]
#align nhds_eq_map_mul_right_nhds_one nhds_eq_map_mul_right_nhds_one

theorem mul_tendsto_nhds_one_nhds_one :
    Tendsto (uncurry ((· * ·) : α → α → α)) (𝓝 1 ×ᶠ 𝓝 1) <| 𝓝 1 :=
  by
  rw [((nhds_basis_Ioo_pos (1 : α)).Prod <| nhds_basis_Ioo_pos (1 : α)).tendsto_iffₓ
      (nhds_basis_Ioo_pos_of_pos (zero_lt_one : (0 : α) < 1))]
  intro ε hε
  have hε' : 0 ≤ 1 - ε / 4 := by linarith
  have ε_pos : 0 < ε / 4 := by linarith
  have ε_pos' : 0 < ε / 2 := by linarith
  simp only [and_imp, Prod.forall, mem_Ioo, Function.uncurry_apply_pair, mem_prod, Prod.exists]
  refine' ⟨ε / 4, ε / 4, ⟨ε_pos, ε_pos⟩, fun a b ha ha' hb hb' => _⟩
  have ha0 : 0 ≤ a := le_trans hε' (le_of_lt ha)
  have hb0 : 0 ≤ b := le_trans hε' (le_of_lt hb)
  refine'
    ⟨lt_of_le_of_lt _ (mul_lt_mul'' ha hb hε' hε'), lt_of_lt_of_le (mul_lt_mul'' ha' hb' ha0 hb0) _⟩
  ·
    calc
      1 - ε = 1 - ε / 2 - ε / 2 := by ring_nf
      _ ≤ 1 - ε / 2 - ε / 2 + ε / 2 * (ε / 2) := (le_add_of_nonneg_right (by positivity))
      _ = (1 - ε / 2) * (1 - ε / 2) := by ring_nf
      _ ≤ (1 - ε / 4) * (1 - ε / 4) := mul_le_mul (by linarith) (by linarith) (by linarith) hε'
      
  ·
    calc
      (1 + ε / 4) * (1 + ε / 4) = 1 + ε / 2 + ε / 4 * (ε / 4) := by ring_nf
      _ = 1 + ε / 2 + ε * ε / 16 := by ring_nf
      _ ≤ 1 + ε / 2 + ε / 2 :=
        (add_le_add_left
          (div_le_div (le_of_lt hε.1)
            (le_trans ((mul_le_mul_left hε.1).2 hε.2) (le_of_eq <| mul_one ε)) zero_lt_two
            (by linarith))
          (1 + ε / 2))
      _ ≤ 1 + ε := by ring_nf
      
#align mul_tendsto_nhds_one_nhds_one mul_tendsto_nhds_one_nhds_one

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedField.continuousMul : ContinuousMul α :=
  ⟨by
    rw [continuous_iff_continuousAt]
    rintro ⟨x₀, y₀⟩
    by_cases hx₀ : x₀ = 0
    · rw [hx₀, ContinuousAt, zero_mul, nhds_prod_eq]
      exact mul_tendsto_nhds_zero_right y₀
    by_cases hy₀ : y₀ = 0
    · rw [hy₀, ContinuousAt, mul_zero, nhds_prod_eq]
      exact mul_tendsto_nhds_zero_left x₀
    have hxy : x₀ * y₀ ≠ 0 := mul_ne_zero hx₀ hy₀
    have key :
      (fun p : α × α => x₀ * p.1 * (p.2 * y₀)) =
        ((fun x => x₀ * x) ∘ fun x => x * y₀) ∘ uncurry (· * ·) :=
      by
      ext p
      simp [uncurry, mul_assoc]
    have key₂ : ((fun x => x₀ * x) ∘ fun x => y₀ * x) = fun x => x₀ * y₀ * x :=
      by
      ext x
      simp
    calc
      map (uncurry (· * ·)) (𝓝 (x₀, y₀)) = map (uncurry (· * ·)) (𝓝 x₀ ×ᶠ 𝓝 y₀) := by
        rw [nhds_prod_eq]
      _ = map (fun p : α × α => x₀ * p.1 * (p.2 * y₀)) (𝓝 1 ×ᶠ 𝓝 1) := by
        rw [uncurry, nhds_eq_map_mul_left_nhds_one hx₀, nhds_eq_map_mul_right_nhds_one hy₀,
          prod_map_map_eq, Filter.map_map]
      _ = map ((fun x => x₀ * x) ∘ fun x => x * y₀) (map (uncurry (· * ·)) (𝓝 1 ×ᶠ 𝓝 1)) := by
        rw [key, ← Filter.map_map]
      _ ≤ map ((fun x : α => x₀ * x) ∘ fun x => x * y₀) (𝓝 1) :=
        (map_mono mul_tendsto_nhds_one_nhds_one)
      _ = 𝓝 (x₀ * y₀) := by
        rw [← Filter.map_map, ← nhds_eq_map_mul_right_nhds_one hy₀,
          nhds_eq_map_mul_left_nhds_one hy₀, Filter.map_map, key₂, ←
          nhds_eq_map_mul_left_nhds_one hxy]
      ⟩
#align linear_ordered_field.has_continuous_mul LinearOrderedField.continuousMul

end continuous_mul

/-- In a linearly ordered field with the order topology, if `f` tends to `at_top` and `g` tends to
a positive constant `C` then `f * g` tends to `at_top`. -/
theorem Filter.Tendsto.atTop_mul {C : α} (hC : 0 < C) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop :=
  by
  refine' tendsto_at_top_mono' _ _ (hf.at_top_mul_const (half_pos hC))
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)),
    hf.eventually (eventually_ge_at_top 0)]with x hg hf using mul_le_mul_of_nonneg_left hg.le hf
#align filter.tendsto.at_top_mul Filter.Tendsto.atTop_mul

/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `at_top` then `f * g` tends to `at_top`. -/
theorem Filter.Tendsto.mul_atTop {C : α} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.at_top_mul hC hf
#align filter.tendsto.mul_at_top Filter.Tendsto.mul_atTop

/-- In a linearly ordered field with the order topology, if `f` tends to `at_top` and `g` tends to
a negative constant `C` then `f * g` tends to `at_bot`. -/
theorem Filter.Tendsto.atTop_mul_neg {C : α} (hC : C < 0) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [(· ∘ ·), neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_at_top_at_bot.comp (hf.at_top_mul (neg_pos.2 hC) hg.neg)
#align filter.tendsto.at_top_mul_neg Filter.Tendsto.atTop_mul_neg

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `at_top` then `f * g` tends to `at_bot`. -/
theorem Filter.Tendsto.neg_mul_atTop {C : α} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.at_top_mul_neg hC hf
#align filter.tendsto.neg_mul_at_top Filter.Tendsto.neg_mul_atTop

/-- In a linearly ordered field with the order topology, if `f` tends to `at_bot` and `g` tends to
a positive constant `C` then `f * g` tends to `at_bot`. -/
theorem Filter.Tendsto.atBot_mul {C : α} (hC : 0 < C) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  simpa [(· ∘ ·)] using
    tendsto_neg_at_top_at_bot.comp ((tendsto_neg_at_bot_at_top.comp hf).atTop_mul hC hg)
#align filter.tendsto.at_bot_mul Filter.Tendsto.atBot_mul

/-- In a linearly ordered field with the order topology, if `f` tends to `at_bot` and `g` tends to
a negative constant `C` then `f * g` tends to `at_top`. -/
theorem Filter.Tendsto.atBot_mul_neg {C : α} (hC : C < 0) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  simpa [(· ∘ ·)] using
    tendsto_neg_at_bot_at_top.comp ((tendsto_neg_at_bot_at_top.comp hf).atTop_mul_neg hC hg)
#align filter.tendsto.at_bot_mul_neg Filter.Tendsto.atBot_mul_neg

/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `at_bot` then `f * g` tends to `at_bot`. -/
theorem Filter.Tendsto.mul_atBot {C : α} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.at_bot_mul hC hf
#align filter.tendsto.mul_at_bot Filter.Tendsto.mul_atBot

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `at_bot` then `f * g` tends to `at_top`. -/
theorem Filter.Tendsto.neg_mul_atBot {C : α} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.at_bot_mul_neg hC hf
#align filter.tendsto.neg_mul_at_bot Filter.Tendsto.neg_mul_atBot

/-- The function `x ↦ x⁻¹` tends to `+∞` on the right of `0`. -/
theorem tendsto_inv_zero_atTop : Tendsto (fun x : α => x⁻¹) (𝓝[>] (0 : α)) atTop :=
  by
  refine' (at_top_basis' 1).tendsto_right_iff.2 fun b hb => _
  have hb' : 0 < b := by positivity
  filter_upwards [Ioc_mem_nhdsWithin_Ioi
      ⟨le_rfl, inv_pos.2 hb'⟩]with x hx using(le_inv hx.1 hb').1 hx.2
#align tendsto_inv_zero_at_top tendsto_inv_zero_atTop

/-- The function `r ↦ r⁻¹` tends to `0` on the right as `r → +∞`. -/
theorem tendsto_inv_atTop_zero' : Tendsto (fun r : α => r⁻¹) atTop (𝓝[>] (0 : α)) :=
  by
  refine'
    (has_basis.tendsto_iff at_top_basis ⟨fun s => mem_nhdsWithin_Ioi_iff_exists_Ioc_subset⟩).2 _
  refine' fun b hb => ⟨b⁻¹, trivial, fun x hx => _⟩
  have : 0 < x := lt_of_lt_of_le (inv_pos.2 hb) hx
  exact ⟨inv_pos.2 this, (inv_le this hb).2 hx⟩
#align tendsto_inv_at_top_zero' tendsto_inv_atTop_zero'

theorem tendsto_inv_atTop_zero : Tendsto (fun r : α => r⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero'.mono_right inf_le_left
#align tendsto_inv_at_top_zero tendsto_inv_atTop_zero

theorem Filter.Tendsto.div_atTop [ContinuousMul α] {f g : β → α} {l : Filter β} {a : α}
    (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x / g x) l (𝓝 0) :=
  by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_at_top_zero.comp hg)
#align filter.tendsto.div_at_top Filter.Tendsto.div_atTop

theorem Filter.Tendsto.inv_tendsto_atTop (h : Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0) :=
  tendsto_inv_atTop_zero.comp h
#align filter.tendsto.inv_tendsto_at_top Filter.Tendsto.inv_tendsto_atTop

theorem Filter.Tendsto.inv_tendsto_zero (h : Tendsto f l (𝓝[>] 0)) : Tendsto f⁻¹ l atTop :=
  tendsto_inv_zero_atTop.comp h
#align filter.tendsto.inv_tendsto_zero Filter.Tendsto.inv_tendsto_zero

/-- The function `x^(-n)` tends to `0` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_neg_at_top`. -/
theorem tendsto_pow_neg_atTop {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : α => x ^ (-(n : ℤ))) atTop (𝓝 0) := by
  simpa only [zpow_neg, zpow_ofNat] using (@tendsto_pow_at_top α _ _ hn).inv_tendsto_atTop
#align tendsto_pow_neg_at_top tendsto_pow_neg_atTop

theorem tendsto_zpow_atTop_zero {n : ℤ} (hn : n < 0) : Tendsto (fun x : α => x ^ n) atTop (𝓝 0) :=
  by
  lift -n to ℕ using le_of_lt (neg_pos.mpr hn) with N
  rw [← neg_pos, ← h, Nat.cast_pos] at hn
  simpa only [h, neg_neg] using tendsto_pow_neg_atTop hn.ne'
#align tendsto_zpow_at_top_zero tendsto_zpow_atTop_zero

theorem tendsto_const_mul_zpow_atTop_zero {n : ℤ} {c : α} (hn : n < 0) :
    Tendsto (fun x => c * x ^ n) atTop (𝓝 0) :=
  mul_zero c ▸ Filter.Tendsto.const_mul c (tendsto_zpow_atTop_zero hn)
#align tendsto_const_mul_zpow_at_top_zero tendsto_const_mul_zpow_atTop_zero

theorem tendsto_const_mul_pow_nhds_iff' {n : ℕ} {c d : α} :
    Tendsto (fun x : α => c * x ^ n) atTop (𝓝 d) ↔ (c = 0 ∨ n = 0) ∧ c = d :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [tendsto_const_nhds_iff]
  rcases lt_trichotomy c 0 with (hc | rfl | hc)
  · have := tendsto_const_mul_pow_at_bot_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atBot this, hc.ne, hn]
  · simp [tendsto_const_nhds_iff]
  · have := tendsto_const_mul_pow_at_top_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atTop this, hc.ne', hn]
#align tendsto_const_mul_pow_nhds_iff' tendsto_const_mul_pow_nhds_iff'

theorem tendsto_const_mul_pow_nhds_iff {n : ℕ} {c d : α} (hc : c ≠ 0) :
    Tendsto (fun x : α => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d := by
  simp [tendsto_const_mul_pow_nhds_iff', hc]
#align tendsto_const_mul_pow_nhds_iff tendsto_const_mul_pow_nhds_iff

theorem tendsto_const_mul_zpow_atTop_nhds_iff {n : ℤ} {c d : α} (hc : c ≠ 0) :
    Tendsto (fun x : α => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d ∨ n < 0 ∧ d = 0 :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · by_cases hn : 0 ≤ n
    · lift n to ℕ using hn
      simp only [zpow_ofNat] at h
      rw [tendsto_const_mul_pow_nhds_iff hc, ← Int.coe_nat_eq_zero] at h
      exact Or.inl h
    · rw [not_le] at hn
      refine' Or.inr ⟨hn, tendsto_nhds_unique h (tendsto_const_mul_zpow_atTop_zero hn)⟩
  · cases h
    · simp only [h.left, h.right, zpow_zero, mul_one]
      exact tendsto_const_nhds
    · exact h.2.symm ▸ tendsto_const_mul_zpow_atTop_zero h.1
#align tendsto_const_mul_zpow_at_top_nhds_iff tendsto_const_mul_zpow_atTop_nhds_iff

-- TODO: With a different proof, this could be possibly generalised to only require a
-- `linear_ordered_semifield` instance, which would also remove the need for the
-- `nnreal` instance of `has_continuous_inv₀`.
-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedField.to_topologicalDivisionRing : TopologicalDivisionRing α
    where continuousAt_inv₀ :=
    by
    suffices ∀ {x : α}, 0 < x → ContinuousAt Inv.inv x
      by
      intro x hx
      cases hx.symm.lt_or_lt
      · exact this h
      convert (this <| neg_pos.mpr h).neg.comp continuous_neg.continuous_at
      ext
      simp [neg_inv]
    intro t ht
    rw [ContinuousAt,
      (nhds_basis_Ioo_pos t).tendsto_iffₓ <| nhds_basis_Ioo_pos_of_pos <| inv_pos.2 ht]
    rintro ε ⟨hε : ε > 0, hεt : ε ≤ t⁻¹⟩
    refine' ⟨min (t ^ 2 * ε / 2) (t / 2), by positivity, fun x h => _⟩
    have hx : t / 2 < x := by
      rw [Set.mem_Ioo, sub_lt_comm, lt_min_iff] at h
      nlinarith
    have hx' : 0 < x := (half_pos ht).trans hx
    have aux : 0 < 2 / t ^ 2 := by positivity
    rw [Set.mem_Ioo, ← sub_lt_iff_lt_add', sub_lt_comm, ← abs_sub_lt_iff] at h⊢
    rw [inv_sub_inv ht.ne' hx'.ne', abs_div, div_eq_mul_inv]
    suffices (|t * x|)⁻¹ < 2 / t ^ 2 by
      rw [← abs_neg, neg_sub]
      refine' (mul_lt_mul'' h this (by positivity) (by positivity)).trans_le _
      rw [mul_comm, mul_min_of_nonneg _ _ aux.le]
      apply min_le_of_left_le
      rw [← mul_div, ← mul_assoc, div_mul_cancel _ (sq_pos_of_pos ht).ne',
        mul_div_cancel' ε two_ne_zero]
    refine' inv_lt_of_inv_lt aux _
    rw [inv_div, abs_of_pos <| mul_pos ht hx', sq, ← mul_div_assoc']
    exact mul_lt_mul_of_pos_left hx ht
#align linear_ordered_field.to_topological_division_ring LinearOrderedField.to_topologicalDivisionRing

theorem nhdsWithin_pos_comap_mul_left {x : α} (hx : 0 < x) :
    comap (fun ε => x * ε) (𝓝[>] 0) = 𝓝[>] 0 :=
  by
  suffices ∀ {x : α} (hx : 0 < x), 𝓝[>] 0 ≤ comap (fun ε => x * ε) (𝓝[>] 0)
    by
    refine' le_antisymm _ (this hx)
    have hr : 𝓝[>] (0 : α) = ((𝓝[>] (0 : α)).comap fun ε => x⁻¹ * ε).comap fun ε => x * ε := by
      simp [comap_comap, inv_mul_cancel hx.ne.symm, comap_id, one_mul_eq_id]
    conv_rhs => rw [hr]
    rw [comap_le_comap_iff
        (by convert univ_mem <;> exact (mul_left_surjective₀ hx.ne.symm).range_eq)]
    exact this (inv_pos.mpr hx)
  intro x hx
  convert nhdsWithin_le_comap (continuous_mul_left x).ContinuousWithinAt
  · exact (mul_zero _).symm
  · rw [image_const_mul_Ioi_zero hx]
#align nhds_within_pos_comap_mul_left nhdsWithin_pos_comap_mul_left

theorem eventually_nhdsWithin_pos_mul_left {x : α} (hx : 0 < x) {p : α → Prop}
    (h : ∀ᶠ ε in 𝓝[>] 0, p ε) : ∀ᶠ ε in 𝓝[>] 0, p (x * ε) :=
  by
  convert h.comap fun ε => x * ε
  exact (nhdsWithin_pos_comap_mul_left hx).symm
#align eventually_nhds_within_pos_mul_left eventually_nhdsWithin_pos_mul_left

