/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.LocallyFinsupp

/-!
# The Divisor of a meromorphic function

This file defines the divisor of a meromorphic function and proves the most basic lemmas about those
divisors. The lemma `MeromorphicOn.divisor_restrict` guarantees compatibility between restrictions
of divisors and of meromorphic functions to subsets of their domain of definition.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open Filter Metric Topology

namespace MeromorphicOn

/-!
## Definition of the Divisor
-/

open Classical in
/--
The divisor of a meromorphic function `f`, mapping a point `z` to the order of `f` at `z`, and to
zero if the order is infinite.
-/
noncomputable def divisor (f : 𝕜 → E) (U : Set 𝕜) :
    Function.locallyFinsuppWithin U ℤ where
  toFun := fun z ↦ if MeromorphicOn f U ∧ z ∈ U then (meromorphicOrderAt f z).untop₀ else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportLocallyFiniteWithinDomain' := by
    simp_all only [Function.support_subset_iff, ne_eq, ite_eq_right_iff, WithTop.untop₀_eq_zero,
      and_imp, Classical.not_imp, not_or, implies_true,
      ← supportDiscreteWithin_iff_locallyFiniteWithin]
    by_cases hf : MeromorphicOn f U
    · filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
        hf.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top]
      simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, Pi.ofNat_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero, and_imp]
      tauto
    · simp [hf, Pi.zero_def]

open Classical in
/-- Definition of the divisor -/
theorem divisor_def (f : 𝕜 → E) (U : Set 𝕜) :
    divisor f U z = if MeromorphicOn f U ∧ z ∈ U then (meromorphicOrderAt f z).untop₀ else 0 :=
  rfl

/--
Simplifier lemma: on `U`, the divisor of a function `f` that is meromorphic on `U` evaluates to
`order.untop₀`.
-/
@[simp]
lemma divisor_apply {f : 𝕜 → E} (hf : MeromorphicOn f U) (hz : z ∈ U) :
    divisor f U z = (meromorphicOrderAt f z).untop₀ := by simp_all [MeromorphicOn.divisor_def]

/-- The divisor of a function `f` evaluates to zero if `f` is not meromorphic. -/
@[simp] theorem divisor_eq_zero_of_not_meromorphicOn {f : 𝕜 → E} (hf : ¬ MeromorphicOn f U) :
    divisor f U z = 0 := by
  unfold divisor
  aesop

lemma AnalyticOnNhd.divisor_apply {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U) (hz : z ∈ U) :
    divisor f U z = ((analyticOrderAt f z).map (↑)).untop₀ := by
  rw [hf.meromorphicOn.divisor_apply hz, (hf z hz).meromorphicOrderAt_eq]

/-!
## Support Properties
-/

/--
Special case of `Function.locallyFinsuppWithin.finiteSupport` that frequently shows in complex
analysis: Divisors on spheres have finite support.
-/
lemma _root_.divisor_sphere_support_finite [ProperSpace 𝕜] {f : 𝕜 → E} {R : ℝ} {c : 𝕜} :
    (divisor f (sphere c R)).support.Finite :=
    (divisor f (sphere c R)).finiteSupport (isCompact_sphere c R)

/--
If `f` is meromorphic on a compact set `U` and `V ⊆ U`, then the divisor of `f` on `V` has finite
support.
-/
lemma divisor_support_finite_of_subset {f : 𝕜 → E} {V : Set 𝕜} (hf : MeromorphicOn f U)
    (hU : IsCompact U) (hV : V ⊆ U) :
    (divisor f V).support.Finite := by
  apply ((divisor f U).finiteSupport hU).subset
  intro b hb
  rw [Function.mem_support, ne_eq, divisor_apply hf (hV ((divisor f V).supportWithinDomain hb))]
  rwa [Function.mem_support, ne_eq, divisor_apply (fun x hx ↦ hf x (hV hx))
    ((divisor f V).supportWithinDomain hb)] at hb

/--
Special case of `MeromorphicOn.divisor_subset_finiteSupport` that frequently shows in complex
analysis, where  `U` is a closed ball and `V` is its interior.
-/
lemma divisor_ball_support_finite [ProperSpace 𝕜] {f : 𝕜 → E} {R : ℝ} {c : 𝕜}
    (hf : MeromorphicOn f (closedBall c R)) :
    (divisor f (ball c R)).support.Finite :=
  hf.divisor_support_finite_of_subset (isCompact_closedBall c R) ball_subset_closedBall

/-!
## Congruence Lemmas
-/

/--
If `f₁` is meromorphic on `U`, if `f₂` agrees with `f₁` on a codiscrete subset of `U` and outside of
`U`, then `f₁` and `f₂` induce the same divisors on `U`.
-/
theorem divisor_congr_codiscreteWithin_of_eqOn_compl {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂) (h₂ : Set.EqOn f₁ f₂ Uᶜ) :
    divisor f₁ U = divisor f₂ U := by
  ext x
  by_cases hx : x ∈ U
  · simp only [hf₁, hx, divisor_apply, hf₁.congr_codiscreteWithin_of_eqOn_compl h₁ h₂]
    congr 1
    apply meromorphicOrderAt_congr
    simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin, disjoint_principal_right] at h₁
    filter_upwards [h₁ x hx] with a ha
    simp at ha
    tauto
  · simp [hx]

/-
If two meromorphic functions agree outside a set codiscrete within a perfect set, then they define
the same divisors there.
-/
theorem divisor_of_eventuallyEq_codiscreteWithin_preperfect {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U) (hU : Preperfect U)
    (h : f₁ =ᶠ[codiscreteWithin U] f₂) :
    divisor f₁ U = divisor f₂ U := by
  ext z
  by_cases hz : z ∉ U
  · simp_all
  rw [not_not] at hz
  rw [divisor_apply hf₁ hz, divisor_apply hf₂ hz]
  congr 1
  apply meromorphicOrderAt_congr
  apply (hf₁ z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hf₂ z hz) hz hU h

/--
If two functions differ only on a discrete set of an open, then they induce the same divisors.
-/
theorem divisor_congr_codiscreteWithin {f₁ f₂ : 𝕜 → E} (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂)
    (h₂ : IsOpen U) :
    divisor f₁ U = divisor f₂ U := by
  by_cases hf₁ : MeromorphicOn f₁ U
  · ext x
    by_cases hx : x ∈ U
    · simp only [hf₁, hx, divisor_apply, hf₁.congr_codiscreteWithin h₁ h₂]
      congr 1
      apply meromorphicOrderAt_congr
      simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
        disjoint_principal_right] at h₁
      have : U ∈ 𝓝[≠] x := by
        apply mem_nhdsWithin.mpr
        use U, h₂, hx, Set.inter_subset_left
      filter_upwards [this, h₁ x hx] with a h₁a h₂a
      simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_setOf_eq, not_and] at h₂a
      tauto
    · simp [hx]
  · simp [divisor, hf₁, (meromorphicOn_congr_codiscreteWithin h₁ h₂).not.1 hf₁]

/-!
## Divisors of Analytic Functions
-/

/-- Analytic functions have non-negative divisors. -/
theorem AnalyticOnNhd.divisor_nonneg {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U) :
    0 ≤ MeromorphicOn.divisor f U := by
  intro x
  by_cases hx : x ∈ U
  · simp [hf.meromorphicOn, hx, (hf x hx).meromorphicOrderAt_nonneg]
  simp [hx]

/--
The divisor of a constant function is `0`.
-/
@[simp]
theorem divisor_const (e : E) :
    divisor (fun _ ↦ e) U = 0 := by
  classical
  ext x
  simp only [divisor_def, meromorphicOrderAt_const, Function.locallyFinsuppWithin.coe_zero,
    Pi.zero_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero,
    LinearOrderedAddCommGroupWithTop.top_ne_zero, imp_false, ite_eq_left_iff, WithTop.zero_ne_top,
    Decidable.not_not, and_imp]
  tauto

/--
The divisor of a constant function is `0`.
-/
@[simp]
theorem divisor_intCast (n : ℤ) :
    divisor (n : 𝕜 → 𝕜) U = 0 := divisor_const (n : 𝕜)

/--
The divisor of a constant function is `0`.
-/
@[simp]
theorem divisor_natCast (n : ℕ) :
    divisor (n : 𝕜 → 𝕜) U = 0 := divisor_const (n : 𝕜)

/--
The divisor of a constant function is `0`.
-/
@[simp] theorem divisor_ofNat (n : ℕ) :
    divisor (ofNat(n) : 𝕜 → 𝕜) U = 0 := by
  convert! divisor_const (n : 𝕜)
  simp [Semiring.toGrindSemiring_ofNat 𝕜 n]

/-!
## Behavior under Standard Operations
-/

/--
The divisor of `f₁ + f₂` is larger than or equal to the minimum of the divisors of `f₁` and `f₂`,
respectively.
-/
theorem min_divisor_le_divisor_add {f₁ f₂ : 𝕜 → E} {z : 𝕜} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) (h₁z : z ∈ U) (h₃ : meromorphicOrderAt (f₁ + f₂) z ≠ ⊤) :
    min (divisor f₁ U z) (divisor f₂ U z) ≤ divisor (f₁ + f₂) U z := by
  by_cases! hz : z ∉ U
  · simp_all
  rw [divisor_apply hf₁ hz, divisor_apply hf₂ hz, divisor_apply (hf₁.add hf₂) hz]
  by_cases h₁ : meromorphicOrderAt f₁ z = ⊤
  · simp_all
  by_cases h₂ : meromorphicOrderAt f₂ z = ⊤
  · simp_all
  rw [← WithTop.untop₀_min h₁ h₂]
  apply WithTop.untop₀_le_untop₀ h₃
  exact meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)

/--
The pole divisor of `f₁ + f₂` is smaller than or equal to the maximum of the pole divisors of `f₁`
and `f₂`, respectively.
-/
theorem negPart_divisor_add_le_max {f₁ f₂ : 𝕜 → E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ max (divisor f₁ U)⁻ (divisor f₂ U)⁻ := by
  intro z
  by_cases! hz : z ∉ U
  · simp [hz]
  simp only [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.max_apply]
  by_cases hf₁₂ : meromorphicOrderAt (f₁ + f₂) z = ⊤
  · simp [divisor_apply (hf₁.add hf₂) hz, hf₁₂, negPart_nonneg]
  rw [← negPart_min]
  apply ((le_iff_posPart_negPart _ _).1 (min_divisor_le_divisor_add hf₁ hf₂ hz hf₁₂)).2

/--
The pole divisor of `f₁ + f₂` is smaller than or equal to the sum of the pole divisors of `f₁` and
`f₂`, respectively.
-/
theorem negPart_divisor_add_le_add {f₁ f₂ : 𝕜 → E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
  calc (divisor (f₁ + f₂) U)⁻
    _ ≤ max (divisor f₁ U)⁻ (divisor f₂ U)⁻ :=
      negPart_divisor_add_le_max hf₁ hf₂
    _ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
      by_cases h : (divisor f₁ U)⁻ ≤ (divisor f₂ U)⁻
      <;> simp_all [negPart_nonneg]

/--
If orders are finite, the divisor of the scalar product of two meromorphic functions is the sum of
the divisors.

See `MeromorphicOn.exists_order_ne_top_iff_forall` and
`MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to guarantee conditions
`h₂f₁` and `h₂f₂`.
-/
theorem divisor_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z ∈ U, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₂f₂ : ∀ z ∈ U, meromorphicOrderAt f₂ z ≠ ⊤) :
    divisor (f₁ • f₂) U = divisor f₁ U + divisor f₂ U := by
  ext z
  by_cases hz : z ∈ U
  · lift meromorphicOrderAt f₁ z to ℤ using (h₂f₁ z hz) with a₁ ha₁
    lift meromorphicOrderAt f₂ z to ℤ using (h₂f₂ z hz) with a₂ ha₂
    simp [h₁f₁, h₁f₂, h₁f₁.smul h₁f₂, hz, meromorphicOrderAt_smul (h₁f₁ z hz) (h₁f₂ z hz),
      ← ha₁, ← ha₂, ← WithTop.coe_add]
  · simp [hz]

/--
If orders are finite, the divisor of the scalar product of two meromorphic functions is the sum of
the divisors.
-/
theorem divisor_fun_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z ∈ U, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₂f₂ : ∀ z ∈ U, meromorphicOrderAt f₂ z ≠ ⊤) :
    divisor (fun z ↦ f₁ z • f₂ z) U = divisor f₁ U + divisor f₂ U :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

/--
If orders are finite, the divisor of the product of two meromorphic functions is the sum of the
divisors.

See `MeromorphicOn.exists_order_ne_top_iff_forall` and
`MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to guarantee conditions
`h₂f₁` and `h₂f₂`.
-/
theorem divisor_mul {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z ∈ U, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₂f₂ : ∀ z ∈ U, meromorphicOrderAt f₂ z ≠ ⊤) :
    divisor (f₁ * f₂) U = divisor f₁ U + divisor f₂ U := divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

/--
If orders are finite, the divisor of the product of two meromorphic functions is the sum of the
divisors.
-/
theorem divisor_fun_mul {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z ∈ U, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₂f₂ : ∀ z ∈ U, meromorphicOrderAt f₂ z ≠ ⊤) :
    divisor (fun z ↦ f₁ z * f₂ z) U = divisor f₁ U + divisor f₂ U :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

open Finset in
/--
If orders are finite, the divisor of a product of meromorphic functions is the sum of the divisors.
-/
theorem divisor_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicOn (f i) U)
    (h₂f : ∀ i ∈ s, ∀ z ∈ U, meromorphicOrderAt (f i) z ≠ ⊤) :
    divisor (∏ i ∈ s, f i) U = ∑ i ∈ s, divisor (f i) U := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [prod_empty, sum_empty]
    exact divisor_ofNat 1
  | insert a s ha hs =>
    have (z) (hz : z ∈ U) : meromorphicOrderAt (∏ i ∈ s, f i) z ≠ ⊤ := by
      simpa [meromorphicOrderAt_prod (fun i hi ↦ h₁f i (mem_insert_of_mem hi) z hz)]
        using fun i hi ↦ h₂f i (mem_insert_of_mem hi) z hz
    rw [prod_insert ha, sum_insert ha, divisor_mul (by aesop)
        (prod (fun i hi ↦ h₁f i (mem_insert_of_mem hi)))
        (h₂f a (mem_insert_self a s)) this,
      hs (fun i hi ↦ h₁f i (mem_insert_of_mem hi))
        (fun i hi ↦ h₂f i (mem_insert_of_mem hi))]

/--
If orders are finite, the divisor of a product of meromorphic functions is the sum of the divisors.
-/
theorem divisor_fun_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicOn (f i) U)
    (h₂f : ∀ i ∈ s, ∀ z ∈ U, meromorphicOrderAt (f i) z ≠ ⊤) :
    divisor (fun x ↦ ∏ i ∈ s, f i x) U = ∑ i ∈ s, divisor (f i) U := by
  convert! divisor_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

/-- The divisor of the inverse is the negative of the divisor. -/
@[simp]
theorem divisor_inv {f : 𝕜 → 𝕜} :
    divisor f⁻¹ U = -divisor f U := by
  ext z
  by_cases h : MeromorphicOn f U ∧ z ∈ U
  · simp [divisor_apply, h, meromorphicOrderAt_inv]
  · simp [divisor_def, h]

/-- The divisor of the inverse is the negative of the divisor. -/
@[simp]
theorem divisor_fun_inv {f : 𝕜 → 𝕜} : divisor (fun z ↦ (f z)⁻¹) U = -divisor f U := divisor_inv

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_pow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℕ) :
    divisor (f ^ n) U = n • divisor f U := by
  classical
  ext z
  by_cases hn : n = 0
  · simp [hn]
  by_cases hz : z ∈ U
  · simp [hf.pow, divisor_apply, meromorphicOrderAt_pow (hf z hz), hf, hz]
  · simp [hz]

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_fun_pow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℕ) :
    divisor (fun z ↦ f z ^ n) U = n • divisor f U := divisor_pow hf n

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_zpow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℤ) :
    divisor (f ^ n) U = n • divisor f U := by
  classical
  ext z
  by_cases hn : n = 0
  · simp [hn]
  by_cases hz : z ∈ U
  · simp [hf.zpow, divisor_apply, meromorphicOrderAt_zpow (hf z hz), hf, hz]
  · simp [hz]

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_fun_zpow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℤ) :
    divisor (fun z ↦ f z ^ n) U = n • divisor f U := divisor_zpow hf n

/--
Taking the divisor of a meromorphic function commutes with restriction.
-/
@[simp]
theorem divisor_restrict {f : 𝕜 → E} {V : Set 𝕜} (hf : MeromorphicOn f U) (hV : V ⊆ U) :
    (divisor f U).restrict hV = divisor f V := by
  ext x
  by_cases hx : x ∈ V
  · rw [Function.locallyFinsuppWithin.restrict_apply]
    simp [hf, hx, hf.mono_set hV, hV hx]
  · simp [hx]

/-- Adding an analytic function to a meromorphic one does not change the pole divisor. -/
theorem negPart_divisor_add_of_analyticNhdOn_right {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : AnalyticOnNhd 𝕜 f₂ U) :
    (divisor (f₁ + f₂) U)⁻ = (divisor f₁ U)⁻ := by
  ext x
  by_cases hx : x ∈ U
  · suffices -(meromorphicOrderAt (f₁ + f₂) x).untop₀ ⊔ 0 = -(meromorphicOrderAt f₁ x).untop₀ ⊔ 0 by
      simpa [negPart_def, hx, hf₁, hf₁.add hf₂.meromorphicOn]
    by_cases h : 0 ≤ meromorphicOrderAt f₁ x
    · suffices 0 ≤ meromorphicOrderAt (f₁ + f₂) x by simp_all
      calc 0
      _ ≤ min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) :=
        le_inf h (hf₂ x hx).meromorphicOrderAt_nonneg
      _ ≤ meromorphicOrderAt (f₁ + f₂) x :=
        meromorphicOrderAt_add (hf₁ x hx) (hf₂ x hx).meromorphicAt
    · suffices meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x by
        rwa [meromorphicOrderAt_add_eq_left_of_lt (hf₂.meromorphicOn x hx)]
      calc meromorphicOrderAt f₁ x
      _ < 0 := by simpa using h
      _ ≤ meromorphicOrderAt f₂ x := (hf₂ x hx).meromorphicOrderAt_nonneg
  simp [hx]

/-- Adding an analytic function to a meromorphic one does not change the pole divisor. -/
theorem negPart_divisor_add_of_analyticNhdOn_left {f₁ f₂ : 𝕜 → E} (hf₁ : AnalyticOnNhd 𝕜 f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ = (divisor f₂ U)⁻ := by
  rw [add_comm]
  exact negPart_divisor_add_of_analyticNhdOn_right hf₂ hf₁

open WithTop in
/-- The divisor of the function `z ↦ z - z₀` at `x` is `0` if `x ≠ z₀`. -/
lemma divisor_sub_const_of_ne {U : Set 𝕜} {z₀ x : 𝕜} (hx : x ≠ z₀) : divisor (· - z₀) U x = 0 := by
  by_cases hu : x ∈ U
  · rw [divisor_apply (show MeromorphicOn (· - z₀) U from fun_sub id <| const z₀) hu,
      ← untop₀_coe 0]
    congr
    exact (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr
      ⟨(· - z₀), analyticAt_id.fun_sub analyticAt_const, by simp [sub_ne_zero_of_ne hx]⟩
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu

open WithTop in
/-- The divisor of the function `z ↦ z - z₀` at `z₀` is `1`. -/
lemma divisor_sub_const_self {z₀ : 𝕜} {U : Set 𝕜} (h : z₀ ∈ U) : divisor (· - z₀) U z₀ = 1 := by
  rw [divisor_apply (show MeromorphicOn (· - z₀) U from fun_sub id <| const z₀) h, ← untop₀_coe 1]
  congr
  exact (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr ⟨fun _ ↦ 1, analyticAt_const, by simp⟩

/-- Divisors are invariant under translation. -/
@[simp] theorem divisor_comp_add_const_eq_divisor {c x : 𝕜} {f : 𝕜 → E} :
    divisor (f ∘ (· + c)) {x | x + c ∈ U} (x - c) = divisor f U x := by
  by_cases h : ¬ MeromorphicOn f U
  · have := (meromorphicOn_comp_add_const_iff_meromorphicOn (c := c) (U := U) (f := f)).not.2 h
    simp_all
  rw [not_not] at h
  have := (meromorphicOn_comp_add_const_iff_meromorphicOn (c := c) (U := U) (f := f)).2 h
  by_cases h₁ : ¬ x ∈ U
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]
    <;> aesop
  rw [divisor_apply, divisor_apply]
  <;> aesop

/-- Divisors are invariant under translation. -/
@[simp] theorem divisor_fun_comp_add_const_eq_divisor {c x : 𝕜} {f : 𝕜 → E} :
    divisor (fun z ↦ f (z + c)) {x | x + c ∈ U} (x - c) = divisor f U x :=
  divisor_comp_add_const_eq_divisor

/-- Divisors are invariant under translation. -/
@[simp] theorem divisor_comp_sub_const_eq_divisor {c : 𝕜} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) {x | x - c ∈ U} (z + c) = divisor f U z := by
  nth_rw 2 [← divisor_comp_add_const_eq_divisor (c := -c)]
  congr 2
  <;> simp [sub_eq_add_neg]

/-- Divisors are invariant under translation. -/
@[simp] theorem divisor_fun_comp_sub_const_eq_divisor {c : 𝕜} {f : 𝕜 → E} :
    divisor (fun z ↦ f (z - c)) {x | x - c ∈ U} (z + c) = divisor f U z :=
  divisor_comp_sub_const_eq_divisor

/-- Divisors are invariant under translation, special case where the set is a ball.. -/
@[simp] theorem divisor_ball_comp_add_const_eq_divisor_ball {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (ball c R) (z + c) = divisor f (ball 0 R) z := by
  nth_rw 2 [← divisor_comp_sub_const_eq_divisor (c := c)]
  congr
  all_goals
    rw [ball_eq_setOf_sub_mem_ball]

/-- Divisors are invariant under translation, special case where the set is a ball. -/
@[simp] theorem divisor_ball_fun_comp_add_const_eq_divisor_ball {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (fun z ↦ f (z - c)) (ball c R) (z + c) = divisor f (ball 0 R) z :=
  divisor_ball_comp_add_const_eq_divisor_ball

/-- Divisors are invariant under translation, special case where the set is a closed ball. -/
@[simp] theorem divisor_closedBall_comp_add_const_eq_divisor_closedBall {c : 𝕜} {R : ℝ}
    {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (closedBall c R) (z + c) = divisor f (closedBall 0 R) z := by
  nth_rw 2 [← divisor_comp_sub_const_eq_divisor (c := c)]
  congr
  all_goals
    rw [closedBall_eq_setOf_sub_mem_closedBall]

/-- Divisors are invariant under translation, special case where the set is a closed ball. -/
@[simp] theorem divisor_closedBall_fun_comp_add_const_eq_divisor_closedBall {c : 𝕜} {R : ℝ}
    {f : 𝕜 → E} :
    divisor (fun z ↦ f (z - c)) (closedBall c R) (z + c) = divisor f (closedBall 0 R) z :=
  divisor_closedBall_comp_add_const_eq_divisor_closedBall

/-- Divisors are invariant under translation, special case where the set is a sphere. -/
@[simp] theorem divisor_sphere_comp_add_const_eq_divisor_sphere {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (sphere c R) (z + c) = divisor f (sphere 0 R) z := by
  nth_rw 2 [← divisor_comp_sub_const_eq_divisor (c := c)]
  congr
  all_goals
    rw [sphere_eq_setOf_sub_mem_sphere]

/-- Divisors are invariant under translation, special case where the set is a sphere. -/
@[simp] theorem divisor_sphere_fun_comp_add_const_eq_divisor_sphere {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (fun z ↦ f (z - c)) (sphere c R) (z + c) = divisor f (sphere 0 R) z :=
  divisor_sphere_comp_add_const_eq_divisor_sphere

end MeromorphicOn
