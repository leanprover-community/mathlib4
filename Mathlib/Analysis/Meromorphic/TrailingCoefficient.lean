/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Order.Filter.Tendsto
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

/-!
# The Trailing Coefficient of a Meromorphic Function

This file defines the trailing coefficient of a meromorphic function. If `f` is meromorphic at a
point `x`, the trailing coefficient is defined as the (unique!) value `g x` for a presentation of
`f` in the form `(z - x) ^ order • g z` with `g` analytic at `x`.

The lemma `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt` expresses the trailing coefficient
as a limit.
-/

@[expose] public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {x : 𝕜}

open Filter Topology

variable (f x) in
/--
If `f` is meromorphic of finite order at a point `x`, the trailing coefficient is defined as the
(unique!) value `g x` for a presentation of `f` in the form `(z - x) ^ order • g z` with `g`
analytic at `x`. In all other cases, the trailing coefficient is defined to be zero.
-/
noncomputable def meromorphicTrailingCoeffAt : E := by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · exact 0
    · exact ((meromorphicOrderAt_ne_top_iff h₁).1 h₂).choose x
  · exact 0

/--
If `f` is not meromorphic at `x`, the trailing coefficient is zero by definition.
-/
@[simp] lemma meromorphicTrailingCoeffAt_of_not_MeromorphicAt (h : ¬MeromorphicAt f x) :
    meromorphicTrailingCoeffAt f x = 0 := by simp [meromorphicTrailingCoeffAt, h]

/--
If `f` is meromorphic of infinite order at `x`, the trailing coefficient is zero by definition.
-/
@[simp] lemma MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
    (h : meromorphicOrderAt f x = ⊤) :
    meromorphicTrailingCoeffAt f x = 0 := by simp_all [meromorphicTrailingCoeffAt]

/-!
## Characterization of the Trailing Coefficient
-/

/--
Definition of the trailing coefficient in case where `f` is meromorphic and a presentation of the
form `f = (z - x) ^ order • g z` is given, with `g` analytic at `x`.
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE (h₁g : AnalyticAt 𝕜 g x)
    (h : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ (meromorphicOrderAt f x).untop₀ • g z) :
    meromorphicTrailingCoeffAt f x = g x := by
  have h₁f : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h]
    fun_prop
  by_cases h₃ : meromorphicOrderAt f x = ⊤
  · simp only [h₃, WithTop.untop₀_top, zpow_zero, one_smul,
      MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top] at ⊢ h
    apply EventuallyEq.eq_of_nhds (f := 0)
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop) (by fun_prop)]
    apply (h.symm.trans (meromorphicOrderAt_eq_top_iff.1 h₃)).symm
  · unfold meromorphicTrailingCoeffAt
    simp only [h₁f, reduceDIte, h₃, ne_eq]
    obtain ⟨h'₁, h'₂, h'₃⟩ := ((meromorphicOrderAt_ne_top_iff h₁f).1 h₃).choose_spec
    apply Filter.EventuallyEq.eq_of_nhds
    rw [← h'₁.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₁g.continuousAt]
    filter_upwards [h, h'₃, self_mem_nhdsWithin] with y h₁y h₂y h₃y
    rw [← sub_eq_zero]
    rwa [h₂y, ← sub_eq_zero, ← smul_sub, smul_eq_zero_iff_right] at h₁y
    simp_all [zpow_ne_zero, sub_ne_zero]

/--
Variant of `meromorphicTrailingCoeffAt_of_order_eq_finite`: Definition of the trailing coefficient
in case where `f` is meromorphic of finite order and a presentation is given.
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : ℤ} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) (h : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n • g z) :
    meromorphicTrailingCoeffAt f x = g x := by
  have h₄ : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h]
    fun_prop
  have : meromorphicOrderAt f x = n := by
    simp only [meromorphicOrderAt_eq_int_iff h₄, ne_eq]
    use g, h₁g, h₂g
    exact h
  simp_all [meromorphicTrailingCoeffAt_of_eq_nhdsNE h₁g]

/--
If `f` is analytic and does not vanish at `x`, then the trailing coefficient of `f` at `x` is `f x`.
-/
@[simp]
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x ≠ 0) :
    meromorphicTrailingCoeffAt f x = f x := by
  rw [h₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0) h₂]
  filter_upwards
  simp

/--
If `f` is meromorphic at `x`, then the trailing coefficient of `f` at `x` is the limit of the
function `(· - x) ^ (-order) • f`.
-/
lemma MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt (h : MeromorphicAt f x) :
    Tendsto ((· - x) ^ (-(meromorphicOrderAt f x).untop₀) • f) (𝓝[≠] x)
      (𝓝 (meromorphicTrailingCoeffAt f x)) := by
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · simp_all only [WithTop.untop₀_top, neg_zero, zpow_zero, one_smul,
      meromorphicTrailingCoeffAt_of_order_eq_top]
    apply Tendsto.congr' (f₁ := 0)
    · filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂] with y hy
      simp_all
    · apply Tendsto.congr' (f₁ := 0) (by rfl) continuousWithinAt_const.tendsto
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h).1 h₂
  apply Tendsto.congr' (f₁ := g)
  · filter_upwards [h₃g, self_mem_nhdsWithin] with y h₁y h₂y
    rw [zpow_neg, Pi.smul_apply', Pi.inv_apply, Pi.pow_apply, h₁y, ← smul_assoc, smul_eq_mul,
      ← zpow_neg, ← zpow_add', neg_add_cancel, zpow_zero, one_smul]
    left
    simp_all [sub_ne_zero]
  · rw [h₁g.meromorphicTrailingCoeffAt_of_eq_nhdsNE h₃g]
    apply h₁g.continuousAt.continuousWithinAt

/-!
## Elementary Properties
-/

/--
If `f` is meromorphic of finite order at `x`, then the trailing coefficient is not zero.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁ : MeromorphicAt f x)
    (h₂ : meromorphicOrderAt f x ≠ ⊤) :
    meromorphicTrailingCoeffAt f x ≠ 0 := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  simpa [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g] using h₂g

/--
The trailing coefficient of a constant function is the constant.
-/
@[simp]
theorem meromorphicTrailingCoeffAt_const {x : 𝕜} {e : 𝕜} :
    meromorphicTrailingCoeffAt (fun _ ↦ e) x = e := by
  by_cases he : e = 0
  · rw [he]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
    rw [meromorphicOrderAt_eq_top_iff]
    simp
  · exact analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero he

/--
The trailing coefficient of `fun z ↦ z - constant` at `z₀` equals one if `z₀ = constant`, or else
`z₀ - constant`.
-/
theorem meromorphicTrailingCoeffAt_id_sub_const [DecidableEq 𝕜] {x y : 𝕜} :
    meromorphicTrailingCoeffAt (· - y) x = if x = y then 1 else x - y := by
  by_cases h : x = y
  · simp_all only [sub_self, ite_true]
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 1) (by fun_prop)
      (by apply one_ne_zero)
    simp
  · simp_all only [ite_false]
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (by fun_prop)
    simp_all [sub_ne_zero]

/-!
## Congruence Lemma
-/

/--
If two functions agree in a punctured neighborhood, then their trailing coefficients agree.
-/
lemma meromorphicTrailingCoeffAt_congr_nhdsNE {f₁ f₂ : 𝕜 → E} (h : f₁ =ᶠ[𝓝[≠] x] f₂) :
    meromorphicTrailingCoeffAt f₁ x = meromorphicTrailingCoeffAt f₂ x := by
  by_cases h₁ : ¬MeromorphicAt f₁ x
  · simp [h₁, (MeromorphicAt.meromorphicAt_congr h).not.1 h₁]
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f₁ x = ⊤
  · simp_all [meromorphicOrderAt_congr h]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g,
    h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g (h.symm.trans h₃g)]

/-!
## Behavior under Arithmetic Operations
-/

/--
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁ + f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt {f₁ f₂ : 𝕜 → E}
    (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ + f₂) x = meromorphicTrailingCoeffAt f₁ x := by
  -- Trivial case: f₁ not meromorphic at x
  by_cases! hf₁ : ¬MeromorphicAt f₁ x
  · have : ¬MeromorphicAt (f₁ + f₂) x := by
      rwa [add_comm, hf₂.meromorphicAt_add_iff_meromorphicAt₁]
    simp_all
  -- Trivial case: f₂ vanishes locally around x
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₂ x to ℤ using h₁f₂ with n₂ hn₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  lift meromorphicOrderAt f₁ x to ℤ using (by aesop) with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  rw [WithTop.coe_lt_coe] at h
  have τ₀ : ∀ᶠ z in 𝓝[≠] x, (f₁ + f₂) z = (z - x) ^ n₁ • (g₁ + (z - x) ^ (n₂ - n₁) • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with z h₁z h₂z h₃z
    simp only [Pi.add_apply, h₁z, h₂z, Pi.smul_apply, smul_add, ← smul_assoc, smul_eq_mul,
      add_right_inj]
    rw [← zpow_add₀, add_sub_cancel]
    simp_all [sub_ne_zero]
  have τ₁ : AnalyticAt 𝕜 (fun z ↦ g₁ z + (z - x) ^ (n₂ - n₁) • g₂ z) x :=
    h₁g₁.fun_add (AnalyticAt.fun_smul (AnalyticAt.fun_zpow_nonneg (by fun_prop)
      (sub_nonneg_of_le h.le)) h₁g₂)
  have τ₂ : g₁ x + (x - x) ^ (n₂ - n₁) • g₂ x ≠ 0 := by
    simp_all [zero_zpow _ (sub_ne_zero.2 (ne_of_lt h).symm)]
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    τ₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE τ₂ τ₀, sub_self, add_eq_left,
    smul_eq_zero, zero_zpow _ (sub_ne_zero.2 (ne_of_lt h).symm)]
  tauto

/--
If `f₁` and `f₂` have equal order at `x` and if their trailing coefficients do not cancel, then the
trailing coefficient of `f₁ + f₂` at `x` is the sum of the trailing coefficients.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁ : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x)
    (h₂ : meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x ≠ 0) :
    meromorphicTrailingCoeffAt (f₁ + f₂) x
      = meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x := by
  -- Trivial case: f₁ vanishes locally around x
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [meromorphicTrailingCoeffAt_of_order_eq_top h₁f₁, zero_add]
    apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₁]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x to ℤ using (by lia) with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  lift meromorphicOrderAt f₂ x to ℤ using (by lia) with n₂ hn₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  rw [WithTop.coe_eq_coe, h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    h₁g₂.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₂ h₃g₂] at *
  have τ₀ : ∀ᶠ z in 𝓝[≠] x, (f₁ + f₂) z = (z - x) ^ n₁ • (g₁ + g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with z h₁z h₂z h₃z
    simp_all
  simp [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (by fun_prop)
    (by simp_all) τ₀]

/--
The trailing coefficient of a scalar product is the scalar product of the trailing coefficients.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ • f₂) x =
      (meromorphicTrailingCoeffAt f₁ x) • (meromorphicTrailingCoeffAt f₂ x) := by
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · simp_all [meromorphicOrderAt_smul hf₁ hf₂]
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp_all [meromorphicOrderAt_smul hf₁ hf₂]
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_ne_top_iff hf₁).1 h₁f₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_ne_top_iff hf₂).1 h₁f₂
  have : f₁ • f₂ =ᶠ[𝓝[≠] x]
      fun z ↦ (z - x) ^ (meromorphicOrderAt (f₁ • f₂) x).untop₀ • (g₁ • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with y h₁y h₂y h₃y
    simp_all [meromorphicOrderAt_smul hf₁ hf₂, zpow_add₀ (sub_ne_zero.2 h₃y)]
    module
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    h₁g₂.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₂ h₃g₂,
    (h₁g₁.smul h₁g₂).meromorphicTrailingCoeffAt_of_eq_nhdsNE this]
  simp

/--
The trailing coefficient of a product is the product of the trailing coefficients.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_mul {f₁ f₂ : 𝕜 → 𝕜} (hf₁ : MeromorphicAt f₁ x)
    (hf₂ : MeromorphicAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ * f₂) x =
      (meromorphicTrailingCoeffAt f₁ x) * (meromorphicTrailingCoeffAt f₂ x) :=
  meromorphicTrailingCoeffAt_smul hf₁ hf₂

/--
The trailing coefficient of a product is the product of the trailing coefficients.
-/
theorem meromorphicTrailingCoeffAt_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    {x : 𝕜} (h : ∀ σ ∈ s, MeromorphicAt (f σ) x) :
    meromorphicTrailingCoeffAt (∏ n ∈ s, f n) x = ∏ n ∈ s, meromorphicTrailingCoeffAt (f n) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    apply meromorphicTrailingCoeffAt_const
  | insert σ s₁ hσ hind =>
    have : ∀ σ₀ ∈ s₁, MeromorphicAt (f σ₀) x := by
      intro τ hτ
      apply h τ (Finset.mem_insert_of_mem hτ)
    rw [Finset.prod_insert hσ, Finset.prod_insert hσ,
      (h σ (Finset.mem_insert_self σ s₁)).meromorphicTrailingCoeffAt_mul
      (MeromorphicAt.prod this), hind this]

/--
The trailing coefficient of the inverse function is the inverse of the trailing coefficient.
-/
lemma meromorphicTrailingCoeffAt_inv {f : 𝕜 → 𝕜} :
    meromorphicTrailingCoeffAt f⁻¹ x = (meromorphicTrailingCoeffAt f x)⁻¹ := by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · simp_all [meromorphicOrderAt_inv (f := f) (x := x)]
    have : f⁻¹ * f =ᶠ[𝓝[≠] x] 1 := by
      filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero h₁).1 h₂]
      simp_all
    rw [← mul_eq_one_iff_eq_inv₀ (h₁.meromorphicTrailingCoeffAt_ne_zero h₂),
      ← h₁.inv.meromorphicTrailingCoeffAt_mul h₁, meromorphicTrailingCoeffAt_congr_nhdsNE this,
      analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0)]
    · simp
    · simp only [zpow_zero, smul_eq_mul, mul_one]
      exact eventuallyEq_nhdsWithin_of_eqOn fun _ ↦ congrFun rfl
  · simp_all

/--
The trailing coefficient of the power of a function is the power of the trailing coefficient.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_zpow {n : ℤ} {f : 𝕜 → 𝕜} (h₁ : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (f ^ n) x = (meromorphicTrailingCoeffAt f x) ^ n := by
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · by_cases h₃ : n = 0
    · simp only [h₃, zpow_zero]
      apply analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero (ne_zero_of_eq_one rfl)
    · simp_all [meromorphicOrderAt_zpow h₁, zero_zpow n h₃]
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
    rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (n := (meromorphicOrderAt f x).untop₀) h₂g h₃g,
      (h₁g.zpow h₂g (n := n)).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (n := (meromorphicOrderAt (f ^ n) x).untop₀)
        (by simp_all [zpow_ne_zero])]
    · simp only [Pi.pow_apply]
    · filter_upwards [h₃g] with a ha
      simp_all [mul_zpow, ← zpow_mul, meromorphicOrderAt_zpow h₁, mul_comm]

/--
The trailing coefficient of the power of a function is the power of the trailing coefficient.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_pow {n : ℕ} {f : 𝕜 → 𝕜} (h₁ : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (f ^ n) x = (meromorphicTrailingCoeffAt f x) ^ n := by
  convert h₁.meromorphicTrailingCoeffAt_zpow (n := n) <;> simp
