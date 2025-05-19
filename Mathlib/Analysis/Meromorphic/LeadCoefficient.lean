/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Order

/-!
# The Leading Coefficient of a Meromorphic Function

This file defines the leading coefficient of a meromorphic function. If `f` is meromorphic at a
point `x`, the leading coefficient is defined as the (unique!) value `g x` for a presentation of `f`
in the form `(z - x) ^ order • g z` with `g` analytic at `x`.

The lemma `leadCoeff_eq_limit` expresses the leading coefficient as a limit.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {x : 𝕜} {n : ℤ}

open Filter Topology

namespace MeromorphicAt

variable (f x) in
/--
If `f` is meromorphic of finite order at a point `x`, the leading coefficient is defined as the
(unique!) value `g x` for a presentation of `f` in the form `(z - x) ^ order • g z` with `g`
analytic at `x`. In all other cases, the leading coefficient is defined to be zero.
-/
noncomputable def leadCoeff : E := by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : h₁.order = ⊤
    · exact 0
    · exact (h₁.order_ne_top_iff.1 h₂).choose x
  · exact 0

/--
If `f` is not meromorphic at `x`, the leading coefficient is zero by definition.
-/
@[simp] lemma leadCoeff_of_not_MeromorphicAt (h : ¬MeromorphicAt f x) :
    leadCoeff f x = 0 := by simp_all [leadCoeff]

/--
If `f` is meromorphic of infinite order at `x`, the leading coefficient is zero by definition.
-/
@[simp] lemma leadCoeff_of_order_eq_top (h₁ : MeromorphicAt f x) (h₂ : h₁.order = ⊤) :
    leadCoeff f x = 0 := by simp_all [leadCoeff]

/-!
## Characterization of the Leading Coefficient
-/

/--
Definition of the leading coefficient in case where `f` is meromorphic of finite order and a
presentation is given.
-/
@[simp]
lemma leadCoeff_of_order_eq_finite (h₁ : MeromorphicAt f x) (h₂ : AnalyticAt 𝕜 g x)
    (h₃ : h₁.order ≠ ⊤) (h₄ : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ h₁.order.untop₀ • g z) :
    leadCoeff f x = g x := by
  unfold leadCoeff
  simp only [h₁, not_true_eq_false, reduceDIte, h₃, ne_eq]
  obtain ⟨h'₁, h'₂, h'₃⟩ := (h₁.order_ne_top_iff.1 h₃).choose_spec
  apply Filter.EventuallyEq.eq_of_nhds
  rw [← h'₁.continuousAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE h₂.continuousAt]
  filter_upwards [h₄, h'₃, self_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [← sub_eq_zero]
  rwa [h₂y, ← sub_eq_zero, ← smul_sub, smul_eq_zero_iff_right] at h₁y
  simp_all [zpow_ne_zero, sub_ne_zero]

/--
Variant of `leadCoeff_of_order_eq_finite`: Definition of the leading coefficient in case where
`f` is meromorphic of finite order and a presentation is given.
-/
@[simp]
lemma _root_.AnalyticAt.leadCoeff_of_order_eq_finite₁ (h₁ : AnalyticAt 𝕜 g x) (h₂ : g x ≠ 0)
    (h₃ : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n • g z) :
    leadCoeff f x = g x := by
  have h₄ : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h₃]
    fun_prop
  have : h₄.order = n := by
    simp only [h₄.order_eq_int_iff, ne_eq, zpow_natCast]
    use g, h₁, h₂
    exact h₃
  simp_all [leadCoeff_of_order_eq_finite h₄ h₁, this]

/--
If `f` is analytic and does not vanish at `x`, then the leading coefficient of `f` at `x` is `f x`.
-/
@[simp]
lemma _root_.AnalyticAt.leadCoeff_of_nonvanish (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x ≠ 0) :
    leadCoeff f x = f x := by
  rw [h₁.leadCoeff_of_order_eq_finite₁ (n := 0) h₂]
  filter_upwards
  simp

/--
If `f` is meromorphic at `x`, then the leading coefficient of `f` at `x` is the limit of the
function `(· - x) ^ (-h₁.order.untop₀) • f`.
-/
lemma leadCoeff_eq_limit (h : MeromorphicAt f x) :
    Tendsto ((· - x) ^ (-h.order.untop₀) • f) (𝓝[≠] x) (𝓝 (leadCoeff f x)) := by
  by_cases h₂ : h.order = ⊤
  · simp_all only [WithTop.untop₀_top, neg_zero, zpow_zero, one_smul,
      leadCoeff_of_order_eq_top]
    apply Tendsto.congr' (f₁ := 0)
    · filter_upwards [h.order_eq_top_iff.1 h₂] with y hy
      simp_all
    · apply Tendsto.congr' (f₁ := 0) (by rfl) continuousWithinAt_const.tendsto
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h.order_ne_top_iff.1 h₂
  apply Tendsto.congr' (f₁ := g)
  · filter_upwards [h₃g, self_mem_nhdsWithin] with y h₁y h₂y
    rw [zpow_neg, Pi.smul_apply', Pi.inv_apply, Pi.pow_apply, h₁y, ← smul_assoc, smul_eq_mul,
      ← zpow_neg, ← zpow_add', neg_add_cancel, zpow_zero, one_smul]
    left
    simp_all [sub_ne_zero]
  · rw [leadCoeff_of_order_eq_finite h h₁g h₂ h₃g]
    apply h₁g.continuousAt.continuousWithinAt

/-!
## Elementary Properties
-/

/--
If `f` is meromorphic of finite order at `x`, then the leading coefficient is not zero.
-/
lemma zero_ne_leadCoeff (h₁ : MeromorphicAt f x) (h₂ : h₁.order ≠ ⊤) :
    0 ≠ leadCoeff f x := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁.order_ne_top_iff.1 h₂
  simpa [h₁g.leadCoeff_of_order_eq_finite₁ h₂g h₃g] using h₂g.symm

/-!
## Congruence Lemma
-/

/--
If two functions agree in a punctured neighborhood, then their leading coefficients agree.
-/
lemma leadCoeff_congr_nhdNE {f₁ f₂ : 𝕜 → E} (h : f₁ =ᶠ[𝓝[≠] x] f₂) :
    leadCoeff f₁ x = leadCoeff f₂ x := by
  by_cases h₁ : ¬MeromorphicAt f₁ x
  · simp [h₁, (MeromorphicAt.meromorphicAt_congr h).not.1 h₁]
  rw [not_not] at h₁
  by_cases h₂ : h₁.order = ⊤
  · simp_all [h₁.congr h, h₁.order_congr h]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁.order_ne_top_iff.1 h₂
  rw [h₁g.leadCoeff_of_order_eq_finite₁ h₂g h₃g,
    h₁g.leadCoeff_of_order_eq_finite₁ h₂g (h.symm.trans h₃g)]

/-!
## Behavior under Arithmetic Operations
-/

/--
The leading coefficient of a scalar product is the scalar product of the leading coefficients.
-/
lemma leadCoeff_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (hf₁ : MeromorphicAt f₁ x)
    (hf₂ : MeromorphicAt f₂ x) :
    leadCoeff (f₁ • f₂) x = (leadCoeff f₁ x) • (leadCoeff f₂ x) := by
  by_cases h₁f₁ : hf₁.order = ⊤
  · simp_all [hf₁, hf₁.smul hf₂, hf₁.order_smul hf₂, h₁f₁]
  by_cases h₁f₂ : hf₂.order = ⊤
  · simp_all [hf₁, hf₁.smul hf₂, hf₁.order_smul hf₂, h₁f₁]
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hf₁.order_ne_top_iff.1 h₁f₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hf₂.order_ne_top_iff.1 h₁f₂
  have : f₁ • f₂ =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ (hf₁.smul hf₂).order.untop₀ • (g₁ • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with y h₁y h₂y h₃y
    simp_all [hf₁.order_smul hf₂]
    rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul, zpow_add₀ (sub_ne_zero.2 h₃y)]
    ring_nf
  rw [h₁g₁.leadCoeff_of_order_eq_finite₁ h₂g₁ h₃g₁,
    h₁g₂.leadCoeff_of_order_eq_finite₁ h₂g₂ h₃g₂,
    leadCoeff_of_order_eq_finite (hf₁.smul hf₂) (h₁g₁.smul h₁g₂)
      (by simp_all [hf₁.order_smul hf₂]) this]
  simp

/--
The leading coefficient of a product is the product of the leading coefficients.
-/
lemma leadCoeff_mul {f₁ f₂ : 𝕜 → 𝕜} (hf₁ : MeromorphicAt f₁ x)
    (hf₂ : MeromorphicAt f₂ x) :
    leadCoeff (f₁ * f₂) x = (leadCoeff f₁ x) * (leadCoeff f₂ x) := by
  exact leadCoeff_smul hf₁ hf₂

/--
The leading coefficient of the inverse function is the inverse of the leading coefficient.
-/
lemma leadCoeff_inv {f : 𝕜 → 𝕜} :
    leadCoeff f⁻¹ x = (leadCoeff f x)⁻¹ := by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : h₁.order = ⊤
    · simp_all [h₁.order_inv]
    have : f⁻¹ * f =ᶠ[𝓝[≠] x] 1 := by
      filter_upwards [h₁.order_ne_top_iff_eventually_ne_zero.1 h₂]
      simp_all
    rw [← mul_eq_one_iff_eq_inv₀ (h₁.zero_ne_leadCoeff h₂).symm,
      ← leadCoeff_mul h₁.inv h₁, leadCoeff_congr_nhdNE this,
      analyticAt_const.leadCoeff_of_order_eq_finite₁ (n := 0)]
    <;> simp_all
    exact eventuallyEq_nhdsWithin_of_eqOn fun _ ↦ congrFun rfl
  · simp_all

/--
Except for edge cases, the leading coefficient of the power of a function is the power of the
leading coefficient.
-/
lemma leadCoeff_zpow₁ {f : 𝕜 → 𝕜} (h₁ : MeromorphicAt f x) (h₂ : h₁.order ≠ ⊤) :
    leadCoeff (f ^ n) x = (leadCoeff f x) ^ n := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁.order_ne_top_iff.1 h₂
  rw [h₁g.leadCoeff_of_order_eq_finite₁ (n := h₁.order.untop₀) h₂g h₃g,
    (h₁g.zpow h₂g (n := n)).leadCoeff_of_order_eq_finite₁ (n := (h₁.zpow n).order.untop₀)
      (by simp_all [h₂g, zpow_ne_zero])]
  · simp only [Pi.pow_apply]
  · filter_upwards [h₃g] with a ha
    simp_all [ha, mul_zpow, ← zpow_mul, h₁.order_zpow, mul_comm]

/--
Except for edge cases, the leading coefficient of the power of a function is the power of the
leading coefficient.
-/
lemma leadCoeff_zpow₂ {f : 𝕜 → 𝕜} (h : MeromorphicAt f x) (hn : n ≠ 0):
    leadCoeff (f ^ n) x = (leadCoeff f x) ^ n := by
  by_cases h₁ : h.order = ⊤
  · simp_all [h.order_zpow, h₁, h.zpow n, zero_zpow n hn]
  apply leadCoeff_zpow₁ h h₁

/--
Except for edge cases, the leading coefficient of the power of a function is the power of the
leading coefficient.
-/
lemma leadCoeff_pow₁ {n : ℕ} {f : 𝕜 → 𝕜} (h₁ : MeromorphicAt f x) (h₂ : h₁.order ≠ ⊤) :
    leadCoeff (f ^ n) x = (leadCoeff f x) ^ n := by
  convert leadCoeff_zpow₁ h₁ h₂ (n := n)
  <;> simp

/--
Except for edge cases, the leading coefficient of the power of a function is the power of the
leading coefficient.
-/
lemma leadCoeff_pow₂ {n : ℕ} {f : 𝕜 → 𝕜} (h : MeromorphicAt f x) (hn : n ≠ 0):
    leadCoeff (f ^ n) x = (leadCoeff f x) ^ n := by
  convert leadCoeff_zpow₂ h (n := n) (Int.ofNat_ne_zero.mpr hn)
  <;> simp

end MeromorphicAt
