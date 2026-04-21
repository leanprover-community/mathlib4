/-
Copyright (c) 2022 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Devon Tuma, Eric Rodriguez, Oliver Nash
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Order.Group

/-!
# Topologies on linear ordered fields

In this file we prove that a linear ordered field with order topology has continuous multiplication
and division (apart from zero in the denominator). We also prove theorems like
`Filter.Tendsto.mul_atTop`: if `f` tends to a positive number and `g` tends to positive infinity,
then `f * g` tends to positive infinity.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open Set Filter TopologicalSpace Function
open scoped Pointwise Topology
open OrderDual (toDual ofDual)

section Semifield

variable {𝕜 α : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α → 𝕜}

/-- In a linearly ordered semifield with the order topology, if `f` tends to `Filter.atTop` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ (hf.atTop_mul_const (half_pos hC))
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)), hf.eventually_ge_atTop 0] with x hg
    hf using mul_le_mul_of_nonneg_left hg.le hf

-- TODO: after removing this deprecated alias,
-- rename `Filter.Tendsto.atTop_mul'` to `Filter.Tendsto.atTop_mul`.
-- Same for the other 3 similar aliases below.
/-- In a linearly ordered semifield with the order topology, if `f` tends to a positive constant `C`
and `g` tends to `Filter.atTop` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.pos_mul_atTop {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atTop_mul_pos hC hf

@[simp]
lemma inv_atTop₀ : (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0 :=
  (((atTop_basis_Ioi' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis <|
    (nhdsGT_basis _).congr (by simp) fun a ha ↦ by simp [inv_Ioi₀ (inv_pos.2 ha)]

@[simp]
lemma inv_nhdsGT_zero : (𝓝[>] (0 : 𝕜))⁻¹ = atTop := by rw [← inv_atTop₀, inv_inv]

/-- The function `x ↦ x⁻¹` tends to `+∞` on the right of `0`. -/
theorem tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[>] (0 : 𝕜)) atTop :=
  inv_nhdsGT_zero.le

/-- The function `r ↦ r⁻¹` tends to `0` on the right as `r → +∞`. -/
theorem tendsto_inv_atTop_nhdsGT_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝[>] (0 : 𝕜)) :=
  inv_atTop₀.le

theorem tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop {f : 𝕜 → α}
    (h : Tendsto (fun x ↦ f x⁻¹) atTop l) :
    Tendsto f (𝓝[>] 0) l := by
  convert h.comp tendsto_inv_nhdsGT_zero
  grind [inv_inv]

theorem tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_nhdsGT_zero.mono_right inf_le_left

theorem Filter.Tendsto.inv_tendsto_atTop (h : Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0) :=
  tendsto_inv_atTop_zero.comp h

theorem Filter.Tendsto.inv_tendsto_nhdsGT_zero (h : Tendsto f l (𝓝[>] 0)) : Tendsto f⁻¹ l atTop :=
  tendsto_inv_nhdsGT_zero.comp h

/-- The function `x^(-n)` tends to `0` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_neg_atTop`. -/
theorem tendsto_pow_neg_atTop {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : 𝕜 => x ^ (-(n : ℤ))) atTop (𝓝 0) := by
  simpa only [zpow_neg, zpow_natCast] using (tendsto_pow_atTop (α := 𝕜) hn).inv_tendsto_atTop

theorem tendsto_zpow_atTop_zero {n : ℤ} (hn : n < 0) :
    Tendsto (fun x : 𝕜 => x ^ n) atTop (𝓝 0) := by
  lift -n to ℕ using le_of_lt (neg_pos.mpr hn) with N h
  rw [← neg_pos, ← h, Nat.cast_pos] at hn
  simpa only [h, neg_neg] using tendsto_pow_neg_atTop hn.ne'

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toContinuousInv₀ [ContinuousMul 𝕜] :
    ContinuousInv₀ 𝕜 := .of_nhds_one <| tendsto_order.2 <| by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨x', h₀, hxx', h₁⟩ : ∃ x', 0 < x' ∧ x ≤ x' ∧ x' < 1 :=
      ⟨max x (1 / 2), one_half_pos.trans_le (le_max_right _ _), le_max_left _ _,
        max_lt hx one_half_lt_one⟩
    filter_upwards [Ioo_mem_nhds one_pos ((one_lt_inv₀ h₀).2 h₁)] with y hy
    exact hxx'.trans_lt <| lt_inv_of_lt_inv₀ hy.1 hy.2
  · filter_upwards [Ioi_mem_nhds (inv_lt_one_of_one_lt₀ hx)] with y hy
    exact inv_lt_of_inv_lt₀ (by positivity) hy

end Semifield

/-- If a (possibly non-unital and/or non-associative) ring `R` admits a submultiplicative
nonnegative norm `norm : R → 𝕜`, where `𝕜` is a linear ordered field, and the open balls
`{ x | norm x < ε }`, `ε > 0`, form a basis of neighborhoods of zero, then `R` is a topological
ring. -/
theorem IsTopologicalRing.of_norm {R 𝕜 : Type*} [NonUnitalNonAssocRing R]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace R] [IsTopologicalAddGroup R] (norm : R → 𝕜)
    (norm_nonneg : ∀ x, 0 ≤ norm x) (norm_mul_le : ∀ x y, norm (x * y) ≤ norm x * norm y)
    (nhds_basis : (𝓝 (0 : R)).HasBasis ((0 : 𝕜) < ·) (fun ε ↦ { x | norm x < ε })) :
    IsTopologicalRing R := by
  have h0 : ∀ f : R → R, ∀ c ≥ (0 : 𝕜), (∀ x, norm (f x) ≤ c * norm x) →
      Tendsto f (𝓝 0) (𝓝 0) := by
    refine fun f c c0 hf ↦ (nhds_basis.tendsto_iff nhds_basis).2 fun ε ε0 ↦ ?_
    rcases exists_pos_mul_lt ε0 c with ⟨δ, δ0, hδ⟩
    refine ⟨δ, δ0, fun x hx ↦ (hf _).trans_lt ?_⟩
    exact (mul_le_mul_of_nonneg_left (le_of_lt hx) c0).trans_lt hδ
  apply IsTopologicalRing.of_addGroup_of_nhds_zero
  case hmul =>
    refine ((nhds_basis.prod nhds_basis).tendsto_iff nhds_basis).2 fun ε ε0 ↦ ?_
    refine ⟨(1, ε), ⟨one_pos, ε0⟩, fun (x, y) ⟨hx, hy⟩ => ?_⟩
    simp only at *
    calc norm (x * y) ≤ norm x * norm y := norm_mul_le _ _
    _ < ε := (mul_le_of_le_one_left (norm_nonneg _) hx.le).trans_lt hy
  case hmul_left => exact fun x => h0 _ (norm x) (norm_nonneg _) (norm_mul_le x)
  case hmul_right =>
    exact fun y => h0 (· * y) (norm y) (norm_nonneg y) fun x =>
      (norm_mul_le x y).trans_eq (mul_comm _ _)

variable {𝕜 α : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α → 𝕜}

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.topologicalRing : IsTopologicalRing 𝕜 :=
  .of_norm abs abs_nonneg (fun _ _ ↦ (abs_mul _ _).le) <| by
    simpa using nhds_basis_abs_sub_lt (0 : 𝕜)

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atTop` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.atTop_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  have := hf.atTop_mul_pos (neg_pos.2 hC) hg.neg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `Filter.atTop` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.neg_mul_atTop {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atTop_mul_neg hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atBot` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.atBot_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_pos hC hg
  simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atBot` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.atBot_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_neg hC hg
  simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.pos_mul_atBot {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atBot_mul_pos hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.neg_mul_atBot {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atBot_mul_neg hC hf

@[simp]
lemma inv_atBot₀ : (atBot : Filter 𝕜)⁻¹ = 𝓝[<] 0 :=
  (((atBot_basis_Iio' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis <|
    (nhdsLT_basis _).congr (by simp) fun a ha ↦ by simp [inv_Iio₀ (inv_neg''.2 ha)]

@[simp]
lemma inv_nhdsLT_zero : (𝓝[<] (0 : 𝕜))⁻¹ = atBot := by
  rw [← inv_atBot₀, inv_inv]

/-- The function `x ↦ x⁻¹` tends to `-∞` on the left of `0`. -/
theorem tendsto_inv_nhdsLT_zero : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[<] (0 : 𝕜)) atBot :=
  inv_nhdsLT_zero.le

theorem tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot {f : 𝕜 → α}
    (h : Tendsto (fun x ↦ f x⁻¹) atBot l) :
    Tendsto f (𝓝[<] 0) l := by
  convert h.comp tendsto_inv_nhdsLT_zero
  grind

/-- The function `r ↦ r⁻¹` tends to `0` on the left as `r → -∞`. -/
theorem tendsto_inv_atBot_nhdsLT_zero : Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝[<] (0 : 𝕜)) :=
  inv_atBot₀.le

theorem tendsto_inv_atBot_zero : Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝 0) :=
  tendsto_inv_atBot_nhdsLT_zero.mono_right inf_le_left

theorem Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atTop_zero.comp hg)

theorem Filter.Tendsto.div_atBot {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atBot_zero.comp hg)

lemma Filter.Tendsto.const_div_atTop (hg : Tendsto g l atTop) (r : 𝕜) :
    Tendsto (fun n ↦ r / g n) l (𝓝 0) :=
  tendsto_const_nhds.div_atTop hg

lemma Filter.Tendsto.const_div_atBot (hg : Tendsto g l atBot) (r : 𝕜) :
    Tendsto (fun n ↦ r / g n) l (𝓝 0) :=
  tendsto_const_nhds.div_atBot hg

theorem Filter.Tendsto.inv_tendsto_atBot (h : Tendsto f l atBot) : Tendsto f⁻¹ l (𝓝 0) :=
  tendsto_inv_atBot_zero.comp h

theorem Filter.Tendsto.inv_tendsto_nhdsLT_zero (h : Tendsto f l (𝓝[<] 0)) : Tendsto f⁻¹ l atBot :=
  tendsto_inv_nhdsLT_zero.comp h

/-- If `g` tends to zero and there exists a constant `C : 𝕜` such that eventually `|f x| ≤ C`,
  then the product `f * g` tends to zero. -/
theorem bdd_le_mul_tendsto_zero' {f g : α → 𝕜} (C : 𝕜) (hf : ∀ᶠ x in l, |f x| ≤ C)
    (hg : Tendsto g l (𝓝 0)) : Tendsto (fun x ↦ f x * g x) l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hC : Tendsto (fun x ↦ |C * g x|) l (𝓝 0) := by
    convert (hg.const_mul C).abs
    simp_rw [mul_zero, abs_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
  · filter_upwards [hf] with x _ using abs_nonneg _
  · filter_upwards [hf] with x hx
    simp only [comp_apply, abs_mul]
    exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (abs_nonneg _)

/-- If `g` tends to zero and there exist constants `b B : 𝕜` such that eventually `b ≤ f x| ≤ B`,
  then the product `f * g` tends to zero. -/
theorem bdd_le_mul_tendsto_zero {f g : α → 𝕜} {b B : 𝕜} (hb : ∀ᶠ x in l, b ≤ f x)
    (hB : ∀ᶠ x in l, f x ≤ B) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x ↦ f x * g x) l (𝓝 0) := by
  set C := max |b| |B|
  have hbC : -C ≤ b := neg_le.mpr (le_max_of_le_left (neg_le_abs b))
  have hBC : B ≤ C := le_max_of_le_right (le_abs_self B)
  apply bdd_le_mul_tendsto_zero' C _ hg
  filter_upwards [hb, hB]
  exact fun x hbx hBx ↦ abs_le.mpr ⟨hbC.trans hbx, hBx.trans hBC⟩

/-- If `g` tends to `atTop` and there exist constants `b B : 𝕜` such that eventually
  `b ≤ f x| ≤ B`, then the quotient `f / g` tends to zero. -/
theorem tendsto_bdd_div_atTop_nhds_zero {f g : α → 𝕜} {b B : 𝕜}
    (hb : ∀ᶠ x in l, b ≤ f x) (hB : ∀ᶠ x in l, f x ≤ B) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact bdd_le_mul_tendsto_zero hb hB hg.inv_tendsto_atTop

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
  · cases n with
    | ofNat n =>
      left
      simpa [tendsto_const_mul_pow_nhds_iff hc] using h
    | negSucc n =>
      have hn := Int.negSucc_lt_zero n
      exact Or.inr ⟨hn, tendsto_nhds_unique h (tendsto_const_mul_zpow_atTop_zero hn)⟩
  · rcases h with h | h
    · simp only [h.left, h.right, zpow_zero, mul_one]
      exact tendsto_const_nhds
    · exact h.2.symm ▸ tendsto_const_mul_zpow_atTop_zero h.1

instance (priority := 100) IsStrictOrderedRing.toIsTopologicalDivisionRing :
    IsTopologicalDivisionRing 𝕜 := ⟨⟩

-- TODO: generalize to a `GroupWithZero`
theorem comap_mulLeft_nhdsGT_zero {x : 𝕜} (hx : 0 < x) : comap (x * ·) (𝓝[>] 0) = 𝓝[>] 0 := by
  rw [nhdsWithin, comap_inf, comap_principal, preimage_const_mul_Ioi₀ _ hx, zero_div]
  congr 1
  refine ((Homeomorph.mulLeft₀ x hx.ne').comap_nhds_eq _).trans ?_
  simp

theorem eventually_nhdsGT_zero_mul_left {x : 𝕜} (hx : 0 < x) {p : 𝕜 → Prop}
    (h : ∀ᶠ ε in 𝓝[>] 0, p ε) : ∀ᶠ ε in 𝓝[>] 0, p (x * ε) := by
  rw [← comap_mulLeft_nhdsGT_zero hx]
  exact h.comap fun ε => x * ε
