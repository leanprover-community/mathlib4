/-
Copyright (c) 2022 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Devon Tuma, Eric Rodriguez, Oliver Nash
-/
import Mathlib.Data.Set.Pointwise.Interval
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Order.Group

/-!
# Topologies on linear ordered fields

In this file we prove that a linear ordered field with order topology has continuous multiplication
and division (apart from zero in the denominator). We also prove theorems like
`Filter.Tendsto.mul_atTop`: if `f` tends to a positive number and `g` tends to positive infinity,
then `f * g` tends to positive infinity.
-/


open Set Filter TopologicalSpace Function
open scoped Pointwise Topology
open OrderDual (toDual ofDual)

/-- If a (possibly non-unital and/or non-associative) ring `R` admits a submultiplicative
nonnegative norm `norm : R → 𝕜`, where `𝕜` is a linear ordered field, and the open balls
`{ x | norm x < ε }`, `ε > 0`, form a basis of neighborhoods of zero, then `R` is a topological
ring. -/
theorem TopologicalRing.of_norm {R 𝕜 : Type*} [NonUnitalNonAssocRing R] [LinearOrderedField 𝕜]
    [TopologicalSpace R] [TopologicalAddGroup R] (norm : R → 𝕜)
    (norm_nonneg : ∀ x, 0 ≤ norm x) (norm_mul_le : ∀ x y, norm (x * y) ≤ norm x * norm y)
    (nhds_basis : (𝓝 (0 : R)).HasBasis ((0 : 𝕜) < ·) (fun ε ↦ { x | norm x < ε })) :
    TopologicalRing R := by
  have h0 : ∀ f : R → R, ∀ c ≥ (0 : 𝕜), (∀ x, norm (f x) ≤ c * norm x) →
      Tendsto f (𝓝 0) (𝓝 0) := by
    refine fun f c c0 hf ↦ (nhds_basis.tendsto_iff nhds_basis).2 fun ε ε0 ↦ ?_
    rcases exists_pos_mul_lt ε0 c with ⟨δ, δ0, hδ⟩
    refine ⟨δ, δ0, fun x hx ↦ (hf _).trans_lt ?_⟩
    exact (mul_le_mul_of_nonneg_left (le_of_lt hx) c0).trans_lt hδ
  apply TopologicalRing.of_addGroup_of_nhds_zero
  case hmul =>
    refine ((nhds_basis.prod nhds_basis).tendsto_iff nhds_basis).2 fun ε ε0 ↦ ?_
    refine ⟨(1, ε), ⟨one_pos, ε0⟩, fun (x, y) ⟨hx, hy⟩ => ?_⟩
    simp only [sub_zero] at *
    calc norm (x * y) ≤ norm x * norm y := norm_mul_le _ _
    _ < ε := mul_lt_of_le_one_of_lt_of_nonneg hx.le hy (norm_nonneg _)
  case hmul_left => exact fun x => h0 _ (norm x) (norm_nonneg _) (norm_mul_le x)
  case hmul_right =>
    exact fun y => h0 (· * y) (norm y) (norm_nonneg y) fun x =>
      (norm_mul_le x y).trans_eq (mul_comm _ _)

variable {𝕜 α : Type*} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α → 𝕜}

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedField.topologicalRing : TopologicalRing 𝕜 :=
  .of_norm abs abs_nonneg (fun _ _ ↦ (abs_mul _ _).le) <| by
    simpa using nhds_basis_abs_sub_lt (0 : 𝕜)

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atTop` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.atTop_mul {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ (hf.atTop_mul_const (half_pos hC))
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)), hf.eventually_ge_atTop 0]
    with x hg hf using mul_le_mul_of_nonneg_left hg.le hf

/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `Filter.atTop` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.mul_atTop {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atTop_mul hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atTop` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.atTop_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  have := hf.atTop_mul (neg_pos.2 hC) hg.neg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `Filter.atTop` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.neg_mul_atTop {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atTop_mul_neg hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atBot` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.atBot_mul {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul hC hg
  simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atBot` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.atBot_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_neg hC hg
  simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.mul_atBot {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atBot_mul hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.neg_mul_atBot {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atBot_mul_neg hC hf

@[simp]
lemma inv_atTop₀ : (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0 :=
  (((atTop_basis_Ioi' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis <|
    (nhdsWithin_Ioi_basis _).congr (by simp) fun a ha ↦ by simp [inv_Ioi (inv_pos.2 ha)]

@[simp] lemma inv_nhdsWithin_Ioi_zero : (𝓝[>] (0 : 𝕜))⁻¹ = atTop := by
  rw [← inv_atTop₀, inv_inv]

/-- The function `x ↦ x⁻¹` tends to `+∞` on the right of `0`. -/
theorem tendsto_inv_zero_atTop : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[>] (0 : 𝕜)) atTop :=
  inv_nhdsWithin_Ioi_zero.le

/-- The function `r ↦ r⁻¹` tends to `0` on the right as `r → +∞`. -/
theorem tendsto_inv_atTop_zero' : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝[>] (0 : 𝕜)) :=
  inv_atTop₀.le

theorem tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero'.mono_right inf_le_left

theorem Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atTop_zero.comp hg)

theorem Filter.Tendsto.inv_tendsto_atTop (h : Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0) :=
  tendsto_inv_atTop_zero.comp h

theorem Filter.Tendsto.inv_tendsto_zero (h : Tendsto f l (𝓝[>] 0)) : Tendsto f⁻¹ l atTop :=
  tendsto_inv_zero_atTop.comp h

/-- If there exist real constants `b` and `B` such that for `n` big enough, `b ≤ f n ≤ B`, then
  `f n / (n : ℝ)` tends to `0` as `n` tends to infinity. -/
theorem bdd_le_mul_tendsto_zero [Nonempty α] [SemilatticeSup α] {f g : α → 𝕜} {b B : 𝕜}
    (hb : ∀ᶠ x in atTop, b ≤ f x) (hB : ∀ᶠ x in atTop, f x ≤ B) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun x ↦ f x * (g x)) atTop (𝓝 0) := by
  obtain ⟨nb, hnb⟩ := eventually_atTop.mp hb
  obtain ⟨nB, hnB⟩ := eventually_atTop.mp hB
  have h := OrderTopology.topology_eq_generate_intervals (α := 𝕜)
  subst h
  rw [TopologicalSpace.tendsto_nhds_generateFrom_iff] at hg ⊢
  intro U hU_open hU0
  set b' := if b = 0 then -1 else b with hb'
  have hb0 : b' ≠ 0 := by
    simp only [hb']; split_ifs with h; exacts [neg_ne_zero.mpr one_ne_zero, h]
  have hbb' : b' ≤ b := by simp only [hb']; split_ifs <;> linarith
  set V := HMul.hMul b' ⁻¹' U with hV
  have hV_open : V ∈ {s | ∃ a, s = Ioi a ∨ s = Iio a} :=
    Set.preimage_const_mul_Ioi_or_Iio hb0 hU_open hV
  have hV0 : 0 ∈ V := by simpa only [hV, mem_preimage, mul_zero]
  have hVg := hg V hV_open hV0
  set B' := if B = 0 then 1 else B with hB'
  have hBB' : B ≤ B' := by simp only [hB']; split_ifs <;> linarith
  have hB0 : B' ≠ 0 := by simp only [hB']; split_ifs with h; exacts [one_ne_zero, h]
  set W := HMul.hMul B' ⁻¹' U with hW
  have hW_open : W ∈ {s | ∃ a, s = Ioi a ∨ s = Iio a} :=
    Set.preimage_const_mul_Ioi_or_Iio hB0 hU_open hW
  have hW0 : 0 ∈ W := by simpa only [hW, mem_preimage, mul_zero]
  have hWg := hg W hW_open hW0
  obtain ⟨aU, (haU | haU)⟩ := hU_open <;>
  simp only [hV, hW, haU, mem_atTop_sets, ge_iff_le, mem_preimage, mem_Ioi, mem_Iio]
    at hVg hWg ⊢ <;>
  obtain ⟨aV, haV⟩ := hVg <;>
  obtain ⟨aW, haW⟩ := hWg <;>
  use Sup.sup (Sup.sup aV aW) (Sup.sup nb nB) <;>
  intro x hx
  · by_cases hgx : 0 ≤ g x
    · have h : aU < b' * g x :=
        haV x (le_trans (le_sup_of_le_left (le_sup_of_le_left (le_refl _))) hx)
      exact lt_of_lt_of_le h (mul_le_mul_of_nonneg_right (le_trans hbb'
        (hnb x (le_trans (le_sup_of_le_right (le_sup_of_le_left (le_refl _))) hx))) hgx)
    · have h : aU < B' * g x :=
        haW x (le_trans (le_sup_of_le_left (le_sup_of_le_right (le_refl _))) hx)
      exact lt_of_lt_of_le h (mul_le_mul_of_nonpos_right
        (le_trans (hnB x (le_trans (le_sup_of_le_right (le_sup_of_le_right (le_refl _))) hx)) hBB')
        (le_of_lt (not_le.mp hgx)))
  · by_cases hgx : 0 ≤ g x
    · have h : B' * g x < aU :=
        haW x (le_trans (le_sup_of_le_left (le_sup_of_le_right (le_refl _))) hx)
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_trans (hnB x
        (le_trans (le_sup_of_le_right (le_sup_of_le_right (le_refl _))) hx)) hBB') hgx) h
    · have h : b' * g x < aU :=
        haV x (le_trans (le_sup_of_le_left (le_sup_of_le_left (le_refl _))) hx)
      exact lt_of_le_of_lt (mul_le_mul_of_nonpos_right (le_trans hbb' (hnb x (le_trans
        (le_sup_of_le_right (le_sup_of_le_left (le_refl _))) hx))) (le_of_lt (not_le.mp hgx))) h

theorem tendsto_bdd_div_atTop_nhds_zero [Nonempty α] [SemilatticeSup α] {f g : α → 𝕜} {b B : 𝕜}
    (hb : ∀ᶠ x in atTop, b ≤ f x) (hB : ∀ᶠ x in atTop, f x ≤ B) (hg : Tendsto g atTop atTop) :
    Tendsto (fun x => f x / g x) atTop (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact bdd_le_mul_tendsto_zero hb hB (Filter.Tendsto.inv_tendsto_atTop hg)

/-- The function `x^(-n)` tends to `0` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_neg_atTop`. -/
theorem tendsto_pow_neg_atTop {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : 𝕜 => x ^ (-(n : ℤ))) atTop (𝓝 0) := by
  simpa only [zpow_neg, zpow_natCast] using (@tendsto_pow_atTop 𝕜 _ _ hn).inv_tendsto_atTop

theorem tendsto_zpow_atTop_zero {n : ℤ} (hn : n < 0) :
    Tendsto (fun x : 𝕜 => x ^ n) atTop (𝓝 0) := by
  lift -n to ℕ using le_of_lt (neg_pos.mpr hn) with N h
  rw [← neg_pos, ← h, Nat.cast_pos] at hn
  simpa only [h, neg_neg] using tendsto_pow_neg_atTop hn.ne'

theorem tendsto_const_mul_zpow_atTop_zero {n : ℤ} {c : 𝕜} (hn : n < 0) :
    Tendsto (fun x => c * x ^ n) atTop (𝓝 0) :=
  mul_zero c ▸ Filter.Tendsto.const_mul c (tendsto_zpow_atTop_zero hn)

theorem tendsto_const_mul_pow_nhds_iff' {n : ℕ} {c d : 𝕜} :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ (c = 0 ∨ n = 0) ∧ c = d := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [tendsto_const_nhds_iff]
  rcases lt_trichotomy c 0 with (hc | rfl | hc)
  · have := tendsto_const_mul_pow_atBot_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atBot this, hc.ne, hn]
  · simp [tendsto_const_nhds_iff]
  · have := tendsto_const_mul_pow_atTop_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atTop this, hc.ne', hn]

theorem tendsto_const_mul_pow_nhds_iff {n : ℕ} {c d : 𝕜} (hc : c ≠ 0) :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d := by
  simp [tendsto_const_mul_pow_nhds_iff', hc]

theorem tendsto_const_mul_zpow_atTop_nhds_iff {n : ℤ} {c d : 𝕜} (hc : c ≠ 0) :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d ∨ n < 0 ∧ d = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases n with -- Porting note: Lean 3 proof used `by_cases`, then `lift` but `lift` failed
    | ofNat n =>
      left
      simpa [tendsto_const_mul_pow_nhds_iff hc] using h
    | negSucc n =>
      have hn := Int.negSucc_lt_zero n
      exact Or.inr ⟨hn, tendsto_nhds_unique h (tendsto_const_mul_zpow_atTop_zero hn)⟩
  · cases' h with h h
    · simp only [h.left, h.right, zpow_zero, mul_one]
      exact tendsto_const_nhds
    · exact h.2.symm ▸ tendsto_const_mul_zpow_atTop_zero h.1

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedSemifield.toHasContinuousInv₀ {𝕜}
    [LinearOrderedSemifield 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [ContinuousMul 𝕜] :
    HasContinuousInv₀ 𝕜 := .of_nhds_one <| tendsto_order.2 <| by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨x', h₀, hxx', h₁⟩ : ∃ x', 0 < x' ∧ x ≤ x' ∧ x' < 1 :=
      ⟨max x (1 / 2), one_half_pos.trans_le (le_max_right _ _), le_max_left _ _,
        max_lt hx one_half_lt_one⟩
    filter_upwards [Ioo_mem_nhds one_pos (one_lt_inv h₀ h₁)] with y hy
    exact hxx'.trans_lt <| inv_inv x' ▸ inv_lt_inv_of_lt hy.1 hy.2
  · filter_upwards [Ioi_mem_nhds (inv_lt_one hx)] with y hy
    simpa only [inv_inv] using inv_lt_inv_of_lt (inv_pos.2 <| one_pos.trans hx) hy

instance (priority := 100) LinearOrderedField.toTopologicalDivisionRing :
    TopologicalDivisionRing 𝕜 := ⟨⟩

-- Porting note (#11215): TODO: generalize to a `GroupWithZero`
theorem nhdsWithin_pos_comap_mul_left {x : 𝕜} (hx : 0 < x) :
    comap (x * ·) (𝓝[>] 0) = 𝓝[>] 0 := by
  rw [nhdsWithin, comap_inf, comap_principal, preimage_const_mul_Ioi _ hx, zero_div]
  congr 1
  refine ((Homeomorph.mulLeft₀ x hx.ne').comap_nhds_eq _).trans ?_
  simp

theorem eventually_nhdsWithin_pos_mul_left {x : 𝕜} (hx : 0 < x) {p : 𝕜 → Prop}
    (h : ∀ᶠ ε in 𝓝[>] 0, p ε) : ∀ᶠ ε in 𝓝[>] 0, p (x * ε) := by
  rw [← nhdsWithin_pos_comap_mul_left hx]
  exact h.comap fun ε => x * ε
