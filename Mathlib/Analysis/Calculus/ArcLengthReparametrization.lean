/-
Copyright (c) 2025 Michael Novak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Novak
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Order.BourbakiWitt

/-!
# Arc-Length Reparametrization of Parametrized Curves

In this file we define `arclengthParamTransform` and `arclengthReparam` for a parametrized curve,
which are a parameter transformation and its corresponding reparametrization which is an arc-length
reparametrization.

## Main results

- `arclength_reparametrization`: this theorem tells us that `arclengthParamTransform` is indeed a
  parameter transformation, it is orientation-preserving, and the resulting reparametrization -
  `arclengthReparam` is indeed a reparametrization by arc-length, i.e it has unit speed.

## Notation

 - `ψ` : local notation for the reverse (inverse) parameter transformation, which we used to define
         the parameter transformation.
 - `φ` : local notation for the parameter transformation.

## References
 - We roughly followed [Christian_Bar_2010].
-/

@[expose] public section

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ → E)

/-- Auxiliary definition, this is the reversed (inverse) parameter transformation used for
constructing the arc-length reparametrization of parametrized curve. -/
def arclengthParamTransformAux (t₀ : ℝ) : ℝ → ℝ := fun t ↦ ∫ τ in t₀..t, ‖deriv c τ‖

variable (I : Set ℝ) [I.OrdConnected]

/-- This is parameter transformation used to construct the arc-length reparametrization of
parametrized curve. -/
def arclengthParamTransform (t₀ : ℝ) :=
  letI ψ := arclengthParamTransformAux c t₀
  ψ.invFunOn I

/-- Unit speed / arc-length reparametrization of a parametrized curve. -/
def arclengthReparam (t₀ : ℝ) : ℝ → E :=
  c ∘ (arclengthParamTransform c I t₀)

variable {r : WithTop ℕ∞} {t₀ : ℝ}

-- Auxiliary definition, so we don't have to type the full long expression every time
local notation "ψ" => arclengthParamTransformAux c t₀

omit [I.OrdConnected] in
/-- The 'speed' function of a parametrized curve is continuous. -/
lemma speed_continuousOn (hI : IsOpen I) (hc : ContDiffOn ℝ r c I) (once_diff : 1 ≤ r) :
    ContinuousOn (fun t ↦ ‖deriv c t‖) I :=
  continuous_norm.comp_continuousOn' (hc.continuousOn_deriv_of_isOpen hI once_diff)

/-- An auxiliary lemma giving us the derivative of ψ on I. -/
lemma revParamTransform_deriv_eq_aux {t : ℝ} (ht : t ∈ I) (once_diff : 1 ≤ r) (ht₀ : t₀ ∈ I)
  (hc : ContDiffOn ℝ r c I) (hI : IsOpen I) : HasDerivWithinAt ψ ‖deriv c t‖ I t := by
  unfold arclengthParamTransformAux
  exact intervalIntegral.hasDerivWithinAt_of_continuousOn_interval
    (speed_continuousOn c I hI hc once_diff) ht₀ ht

/-- Auxiliary lemma - ψ is continuous. -/
lemma revParamTransform_continuousOn_aux (once_diff : 1 ≤ r) (ht₀ : t₀ ∈ I)
  (hc : ContDiffOn ℝ r c I) (hI : IsOpen I) : ContinuousOn ψ I :=
  fun _t ht ↦ (revParamTransform_deriv_eq_aux c I ht once_diff ht₀ hc hI).continuousWithinAt

/-- Auxiliary ψ is continuously differentiable on I. -/
lemma revParamTransform_contDiffOn_aux (once_diff : 1 ≤ r) (ht₀ : t₀ ∈ I)
  (hc : ContDiffOn ℝ r c I) (hI : IsOpen I) : ContDiffOn ℝ 1 ψ I := by
  apply (contDiffOn_iff_continuousOn_differentiableOn_deriv hI.uniqueDiffOn).mpr
  constructor
  · intro m hm
    have h'm : m=0 ∨ m=1 := by
      have h : m ≤ 1 := by simp_all
      apply m.le_one_iff_eq_zero_or_eq_one.mp h
    rcases h'm with h'm | h'm
    · rw [h'm, iteratedDerivWithin_zero]
      exact revParamTransform_continuousOn_aux c I once_diff ht₀ hc hI
    · rw [h'm, iteratedDerivWithin_one]
      apply (speed_continuousOn c I hI hc once_diff).congr
      intro t ht
      rw [(revParamTransform_deriv_eq_aux c I ht once_diff ht₀ hc hI).derivWithin]
      exact hI.uniqueDiffWithinAt ht
  · intro m hm
    have h'm : m=0 := by
      have h : m < 1 := by simp_all
      exact Nat.lt_one_iff.mp h
    rw [h'm, iteratedDerivWithin_zero]
    intro t ht
    exact (revParamTransform_deriv_eq_aux c I ht once_diff ht₀ hc hI).differentiableWithinAt

/-- Auxiliary lemma - ψ has positive derivative. -/
lemma revParamTrasform_has_pos_deriv_aux (once_diff : 1 ≤ r) (hc : ContDiffOn ℝ r c I)
    (regular : ∀ t ∈ I, deriv c t ≠ 0) (hI : IsOpen I) (ht₀ : t₀ ∈ I) :
    ∀ t ∈ I, 0 < derivWithin ψ I t := by
  intro t ht
  rw [(revParamTransform_deriv_eq_aux c I ht once_diff ht₀ hc hI).derivWithin]
  · apply norm_pos_iff.mpr (regular t ht)
  · apply hI.uniqueDiffWithinAt ht

/-- Auxiliary lemma - ψ is injective. -/
lemma revParamTransform_injOn_aux (once_diff : 1 ≤ r) (hc : ContDiffOn ℝ r c I)
  (regular : ∀ t ∈ I, deriv c t ≠ 0) (hIo : IsOpen I) (ht₀ : t₀ ∈ I) : I.InjOn ψ :=
  have hI : Convex ℝ I := convex_iff_ordConnected.mpr (by assumption)
  have hiI : interior I = I := hIo.interior_eq
  let speed : ℝ → ℝ := fun t ↦ ‖deriv c t‖
  have hψ : ContinuousOn ψ I := revParamTransform_continuousOn_aux c I once_diff ht₀ hc  hIo
  have hψ' : ∀ t ∈ interior I, HasDerivWithinAt ψ (speed t) (interior I) t := by
    rw [hiI]
    intro t htI
    exact revParamTransform_deriv_eq_aux c I htI once_diff ht₀ hc hIo
  have hψ'₀ : ∀ t ∈ interior I, 0 < speed t := by
    intro t
    unfold speed
    rw [hiI]
    intro htI
    have hnn : 0 ≤ ‖deriv c t‖ := norm_nonneg (deriv c t)
    obtain h₀ | h₁ := eq_or_lt_of_le' hnn
    · rw [norm_eq_zero] at h₀
      have h : deriv c t ≠ 0 := regular t htI
      contradiction
    · exact h₁
  have h : StrictMonoOn ψ I := strictMonoOn_of_hasDerivWithinAt_pos hI hψ hψ' hψ'₀
  h.injOn

/-- Auxiliary lemma - ψ is bijective. -/
lemma revParamTransform_bijOn_aux (once_diff : 1 ≤ r) (hc : ContDiffOn ℝ r c I)
  (regular : ∀ t ∈ I, deriv c t ≠ 0) (hIo : IsOpen I) (ht₀ : t₀ ∈ I) : Set.BijOn ψ I (ψ '' I) :=
  (revParamTransform_injOn_aux c I once_diff hc regular hIo ht₀).bijOn_image

/-- Auxiliary lemma the arc-length parameter transformation is bijective from the image of ψ. -/
lemma bijOn_arclengthParamTransform_aux (once_diff : 1 ≤ r) (hc : ContDiffOn ℝ r c I)
    (regular : ∀ t ∈ I, deriv c t ≠ 0) (ht₀ : t₀ ∈ I) (hIo : IsOpen I) :
    Set.BijOn (arclengthParamTransform c I t₀) (ψ '' I) I := by
  unfold arclengthParamTransform
  have h₀ := revParamTransform_bijOn_aux c I once_diff hc regular hIo ht₀
  have h₁ := Set.BijOn.invOn_invFunOn h₀
  exact (Set.bijOn_comm h₁).mpr h₀

omit [I.OrdConnected] in
/-- Auxiliary lemma ψ is left inverse of the arc-length parameter transformation on the image
of ψ. -/
lemma ψ_leftInvOn_arclengthParamTransform_aux :
  (ψ '' I).LeftInvOn ψ (arclengthParamTransform c I t₀) := by
  intro s hs
  unfold arclengthParamTransform
  apply Function.invFunOn_eq
  exact (Set.mem_image ψ I s).mp hs

/-- Auxiliary definition, so we don't have to type the full long expression every time -/
local notation "φ" => arclengthParamTransform c I t₀

/-- Auxiliary lemma that gives us the derivative of the parameter transformation -/
lemma arclengthParamTransform_deriv_eq_aux {s : ℝ} (hs : s ∈ ψ '' I) (once_diff : 1 ≤ r)
    (ht₀ : t₀ ∈ I) (hc : ContDiffOn ℝ r c I) (hI : IsOpen I) (regular : ∀ t ∈ I, deriv c t ≠ 0) :
    HasStrictDerivAt φ ‖deriv c (φ s)‖⁻¹ s := by
  have hφmT := (bijOn_arclengthParamTransform_aux c I once_diff hc regular ht₀ hI).mapsTo
  have hφsI : φ s ∈ I := hφmT hs
  have hψ : ContDiffAt ℝ 1 ψ (φ s) :=
    (revParamTransform_contDiffOn_aux c I once_diff ht₀ hc hI (φ s) hφsI).contDiffAt
    (hI.mem_nhds hφsI)
  have h1 :  (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hsd : HasStrictDerivAt ψ (deriv ψ (φ s)) (φ s) := hψ.hasStrictDerivAt h1
  have hd₁ : deriv ψ (φ s) = derivWithin ψ I (φ s) := by
    symm
    exact derivWithin_of_isOpen hI hφsI
  have hd₂ : deriv ψ (φ s) = ‖deriv c (φ s)‖ := by
    rw [hd₁, (revParamTransform_deriv_eq_aux c I hφsI once_diff ht₀ hc hI).derivWithin]
    exact hI.uniqueDiffWithinAt hφsI
  rw [hd₂] at hsd
  have h := hsd.to_local_left_inverse
  have hψ' : ‖deriv c (φ s)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact regular (φ s) hφsI
  have hhelp : (∀ᶠ (x : ℝ) in nhds (φ s), (arclengthParamTransform c I t₀) (ψ x) = x) := by
    apply Metric.eventually_nhds_iff_ball.mpr
    rcases Metric.isOpen_iff.mp hI (φ s) hφsI with ⟨ε, hεp, hεb⟩
    use ε
    constructor
    · exact hεp
    · intro τ hτ
      have hτI : τ ∈ I := Set.mem_of_mem_of_subset hτ hεb
      have hψτ : ψ τ ∈ (ψ '' I) := Set.mem_image_of_mem ψ hτI
      have hinjψ := (revParamTransform_injOn_aux c I once_diff hc regular hI ht₀)
      have heq := ψ_leftInvOn_arclengthParamTransform_aux c I hψτ
      have hφψτI : arclengthParamTransform c I t₀ (ψ τ) ∈ I := hφmT hψτ
      exact hinjψ hφψτI hτI heq
  have hinv : ψ (φ s) = s := ψ_leftInvOn_arclengthParamTransform_aux c I hs
  have hfinal := h hψ' hhelp
  rw [hinv] at hfinal
  exact hfinal

/-- This is the main theorem: `arclengthParamTransform` is an orientation-preserving parameter
transformation, that is: a bijection from some interval J to the given interval I with a positive
derivative; and the resulting reparametrization, i.e `arclengthReparam` is indeed a
reparametrization by arc-length, i.e. with unit speed. -/
theorem arclength_reparametrization (once_diff : 1 ≤ r) (hc : ContDiffOn ℝ r c I)
    (regular : ∀ t ∈ I, deriv c t ≠ 0) (ht₀ : t₀ ∈ I) (hIo : IsOpen I) :
    ∃ J : Set ℝ, J.OrdConnected ∧ (Set.BijOn (arclengthParamTransform c I t₀) J I)
               ∧ (∀ s ∈ J, deriv (arclengthParamTransform c I t₀) s > 0)
               ∧ (∀ s ∈ J, ‖deriv (arclengthReparam c I t₀) s‖ = 1):= by
  use ψ '' I
  have h₂ := bijOn_arclengthParamTransform_aux c I once_diff hc regular ht₀ hIo
  have hφmT := (bijOn_arclengthParamTransform_aux c I once_diff hc regular ht₀ hIo).mapsTo
  have hφd {s : ℝ}(hs : s ∈ ψ '' I) :=
    arclengthParamTransform_deriv_eq_aux c I hs once_diff ht₀ hc hIo regular
  constructor
  · rw [Set.ordConnected_iff_uIcc_subset]
    intro s₁ hs₁ s₂ hs₂
    let t₁ := φ s₁
    let t₂ := φ s₂
    have ht₁ : t₁ ∈ I := h₂.mapsTo hs₁
    have ht₂ : t₂ ∈ I := h₂.mapsTo hs₂
    have h :=
      (revParamTransform_continuousOn_aux c I once_diff ht₀ hc hIo).surjOn_uIcc ht₁ ht₂
    have hψt₁ : ψ t₁ = s₁ := (ψ_leftInvOn_arclengthParamTransform_aux c I) hs₁
    have hψt₂ : ψ t₂ = s₂ := (ψ_leftInvOn_arclengthParamTransform_aux c I) hs₂
    rw [hψt₁, hψt₂] at h
    exact h
  · constructor
    · exact h₂
    · constructor
      · intro s hs
        rw [(hφd hs).hasDerivAt.deriv]
        have hφsI : φ s ∈ I := hφmT hs
        have hc' : deriv c (φ s) ≠ 0 := regular (φ s) hφsI
        have hnc' : ‖deriv c (φ s)‖ ≠ 0 := by
          rw [norm_ne_zero_iff]
          exact hc'
        apply norm_pos_iff.mpr at hnc'
        simp_all
      · intro s hs
        unfold arclengthReparam
        have hφsI : φ s ∈ I := hφmT hs
        have hcdφs : DifferentiableAt ℝ c (φ s) :=
          have hr : r ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp once_diff
          ((hIo.contDiffOn_iff.mp hc) hφsI).differentiableAt hr
        have hφds : DifferentiableAt ℝ φ s := (hφd hs).differentiableAt
        rw [deriv.scomp s hcdφs hφds, (hφd hs).hasDerivAt.deriv]
        have hc' : deriv c (φ s) ≠ 0 := regular (φ s) hφsI
        have hnc' : ‖deriv c (φ s)‖ ≠ 0 := by
          rw [norm_ne_zero_iff]
          exact hc'
        have hnn : 0 ≤ ‖deriv c (φ s)‖⁻¹ := by simp_all
        rw [norm_smul_of_nonneg hnn]
        norm_num [hnc']
