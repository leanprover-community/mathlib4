/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
public import Mathlib.Analysis.Meromorphic.RCLike

/-!
# The First Main Theorem of Value Distribution Theory

The First Main Theorem of Value Distribution Theory is a two-part statement, establishing invariance
of the characteristic function `characteristic f ⊤` under modifications of `f`.

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f⁻¹` agree up to a constant, see Proposition 2.1 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677].

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f - const` agree up to a constant, see Proposition 2.2 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677]

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

public section
namespace ValueDistribution

open Asymptotics Filter Function.locallyFinsuppWithin MeromorphicOn Metric Real

section FirstPart

variable {f : ℂ → ℂ} {R : ℝ}

/-!
## First Part of the First Main Theorem
-/

/--
Helper lemma for the first part of the First Main Theorem: Given a meromorphic function `f`, compute
difference between the characteristic functions of `f` and of its inverse.
-/
lemma characteristic_sub_characteristic_inv (h : Meromorphic f) :
    characteristic f ⊤ - characteristic f⁻¹ ⊤ =
      circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
  calc characteristic f ⊤ - characteristic f⁻¹ ⊤
  _ = proximity f ⊤ - proximity f⁻¹ ⊤ - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    unfold characteristic
    ring
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    rw [proximity_sub_proximity_inv_eq_circleAverage h]
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f 0 - logCounting f ⊤) := by
    rw [logCounting_inv]
  _ = circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
    rw [← ValueDistribution.log_counting_zero_sub_logCounting_top]

/--
Helper lemma for the first part of the First Main Theorem: Away from zero, the difference between
the characteristic functions of `f` and `f⁻¹` equals `log ‖meromorphicTrailingCoeffAt f 0‖`.
-/
lemma characteristic_sub_characteristic_inv_of_ne_zero
    (hf : Meromorphic f) (hR : R ≠ 0) :
    characteristic f ⊤ R - characteristic f⁻¹ ⊤ R = log ‖meromorphicTrailingCoeffAt f 0‖ := by
  calc characteristic f ⊤ R - characteristic f⁻¹ ⊤ R
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) R := by simp
  _ = circleAverage (log ‖f ·‖) 0 R - (divisor f Set.univ).logCounting R := by
    rw [characteristic_sub_characteristic_inv hf, Pi.sub_apply]
  _ = log ‖meromorphicTrailingCoeffAt f 0‖ := by
    rw [MeromorphicOn.circleAverage_log_norm hR hf.meromorphicOn]
    unfold Function.locallyFinsuppWithin.logCounting
    have : (divisor f (closedBall 0 |R|)) = (divisor f Set.univ).toClosedBall R :=
      (divisor_restrict hf.meromorphicOn (by tauto)).symm
    simp [this, toClosedBall_apply, restrict_apply]

/--
Helper lemma for the first part of the First Main Theorem: At 0, the difference between the
characteristic functions of `f` and `f⁻¹` equals `log ‖f 0‖`.
-/
lemma characteristic_sub_characteristic_inv_at_zero (h : Meromorphic f) :
    characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0 = log ‖f 0‖ := by
  calc characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) 0 := by simp
  _ = circleAverage (log ‖f ·‖) 0 0 - (divisor f Set.univ).logCounting 0 := by
    rw [ValueDistribution.characteristic_sub_characteristic_inv h, Pi.sub_apply]
  _ = log ‖f 0‖ := by
    simp

/--
First part of the First Main Theorem, quantitative version: If `f` is meromorphic on the complex
plane, then the difference between the characteristic functions of `f` and `f⁻¹` is bounded by an
explicit constant.
-/
theorem characteristic_sub_characteristic_inv_le (hf : Meromorphic f) :
    |characteristic f ⊤ R - characteristic f⁻¹ ⊤ R|
      ≤ max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  by_cases h : R = 0
  · simp [h, characteristic_sub_characteristic_inv_at_zero hf]
  · simp [characteristic_sub_characteristic_inv_of_ne_zero hf h]

/--
First part of the First Main Theorem, qualitative version: If `f` is meromorphic on the complex
plane, then the characteristic functions of `f` and `f⁻¹` agree asymptotically up to a bounded
function.
-/
theorem isBigO_characteristic_sub_characteristic_inv (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic f⁻¹ ⊤) =O[atTop] (1 : ℝ → ℝ) :=
  isBigO_of_le' (c := max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖|) _
    (fun R ↦ by simpa using characteristic_sub_characteristic_inv_le h (R := R))

end FirstPart

section SecondPart

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a₀ : E} {f : ℂ → E}

/-!
## Second Part of the First Main Theorem
-/

/--
Second part of the First Main Theorem of Value Distribution Theory, quantitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions (for value `⊤`) of `f` and
`f - a₀` differ at most by `log⁺ ‖a₀‖ + log 2`.
-/
theorem abs_characteristic_sub_characteristic_shift_le {r : ℝ} (h : Meromorphic f) :
    |characteristic f ⊤ r - characteristic (f · - a₀) ⊤ r| ≤ log⁺ ‖a₀‖ + log 2 := by
  have h₁f : CircleIntegrable (fun x ↦ log⁺ ‖f x‖) 0 r :=
    h.meromorphicOn.circleIntegrable_posLog_norm
  have h₂f : CircleIntegrable (fun x ↦ log⁺ ‖f x - a₀‖) 0 r := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    fun_prop
  rw [← Pi.sub_apply, characteristic_sub_characteristic_eq_proximity_sub_proximity h]
  simp only [proximity, reduceDIte, Pi.sub_apply, ← circleAverage_sub h₁f h₂f]
  apply le_trans abs_circleAverage_le_circleAverage_abs
  apply circleAverage_mono_on_of_le_circle
  · apply (h₁f.sub h₂f).abs
  · intro θ hθ
    simp only [Pi.abs_apply, Pi.sub_apply]
    by_cases h : 0 ≤ log⁺ ‖f θ‖ - log⁺ ‖f θ - a₀‖
    · simpa [abs_of_nonneg h, sub_le_iff_le_add, add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
        using (posLog_norm_add_le (f θ - a₀) a₀)
    · simp only [abs_of_nonpos (le_of_not_ge h), neg_sub, tsub_le_iff_right,
        add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
      convert! posLog_norm_add_le (-f θ) a₀ using 2
      · rw [← norm_neg]
        abel_nf
      · simp

/--
Second part of the First Main Theorem of Value Distribution Theory, qualitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions for the value `⊤` of the
function `f` and `f - a₀` agree asymptotically up to a bounded function.
-/
theorem isBigO_characteristic_sub_characteristic_shift (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic (f · - a₀) ⊤) =O[atTop] (1 : ℝ → ℝ) :=
  isBigO_of_le' (c := log⁺ ‖a₀‖ + log 2) _
    (fun R ↦ by simpa using abs_characteristic_sub_characteristic_shift_le h)

end SecondPart

section moebius

/-!
## Postcomposition with an Automorphism of the Projective Line
-/

/-
Private transitivity lemma, used in the proof of `isBigO_characteristic_sub_characteristic_moebius`:
if `f₁` and `f₃` both differ from the characteristic function of `f₂` only by bounded functions,
then `f₁ - f₃` is bounded.
-/
private lemma transitivity₁ {f₁ f₃ : ℝ → ℝ} (f₂ : ℂ → ℂ)
    (h₂₃ : (characteristic f₂ ⊤ - f₃) =O[atTop] (1 : ℝ → ℝ))
    (h₁₂ : (f₁ - characteristic f₂ ⊤) =O[atTop] (1 : ℝ → ℝ)) :
    (f₁ - f₃) =O[atTop] (1 : ℝ → ℝ) := by
  simpa using! h₁₂.add h₂₃

/-
Private transitivity lemma, used in the proof of `isBigO_characteristic_sub_characteristic_moebius`:
replacing `f₂` by a function that agrees with it outside a discrete set does not affect boundedness
of the difference of the characteristic functions.
-/
private lemma transitivity₂ {f₁ f₂ f₃ : ℂ → ℂ} (h₂₃ : f₂ =ᶠ[codiscrete ℂ] f₃)
    (h₁₂ : (characteristic f₁ ⊤ - characteristic f₂ ⊤) =O[atTop] (1 : ℝ → ℝ)) :
    (characteristic f₁ ⊤ - characteristic f₃ ⊤) =O[atTop] (1 : ℝ → ℝ) := by
  apply EventuallyEq.trans_isBigO ?_ h₁₂
  filter_upwards [Ioi_mem_atTop 0] with x hx
  simpa using characteristic_congr_codiscrete h₂₃.symm (by grind)

/--
Reformulation of the first main theorem: Postcomposing a meromorphic function `f : ℂ → ℂ` with a
Moebius transformation (=an automorphism of the projective line) changes the characteristic function
for the value `⊤` only by a bounded function.
-/
theorem isBigO_characteristic_sub_characteristic_moebius {a b c d : ℂ} {f : ℂ → ℂ}
    (hf : Meromorphic f) (hΔ : a * d - b * c ≠ 0) :
    (characteristic f ⊤ - characteristic ((a * f · + b) / (c * f · + d)) ⊤)
      =O[atTop] (1 : ℝ → ℝ) := by
  /-
  The group of Moebius transformations is generated by translations `w ↦ w + t`, scalings
  `w ↦ s * w` and the inversion `w ↦ w⁻¹`. For these, the assertion is shown in
  `isBigO_characteristic_sub_characteristic_shift`,
  `isBigO_characteristic_sub_characteristic_const_mul` and
  `isBigO_characteristic_sub_characteristic_inv`, respectively. The general case follows by
  decomposing arbitrary transformations into these elementary factors. To minimize technical
  overhead, the proof avoid general machinery and carries the decomposition out by hand.
  -/
  by_cases hc : c = 0
  · -- Affine case `c = 0`: the map is `w ↦ (a / d) * w + b / d`.
    subst hc
    ring_nf at *
    apply transitivity₁ (a * f · + b)
    · convert isBigO_characteristic_sub_characteristic_const_mul (s := d⁻¹) (f := (a * f · + b))
        (by fun_prop) (by aesop)
      ext x
      simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
      field
    apply transitivity₁ (a * f ·)
    · convert isBigO_characteristic_sub_characteristic_shift (a₀ := -b) (f := a • f) (by fun_prop)
      simp
    apply transitivity₁ f
    · convert isBigO_characteristic_sub_characteristic_const_mul (s := a) (f := f)
        (by fun_prop) (by aesop)
    simp [IsBigO.of_norm_le]
  · -- Case `c ≠ 0`.
    by_cases hord : ∀ z, meromorphicOrderAt (c * f · + d) z ≠ ⊤
    · have hne : ∀ᶠ z in codiscrete ℂ, c * f z + d ≠ 0 :=
        MeromorphicOn.codiscreteWithin_setOfPred_ne_zero (by fun_prop) (fun u _ ↦ hord u)
      apply transitivity₂ (f₂ := (fun z ↦ a / c + (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹))
      · filter_upwards [hne] with z hz
        rw [Pi.div_apply]
        field_simp [hc, hz, show f z * c + d ≠ 0 by grind, show f z + d / c ≠ 0 by grind]
        ring
      apply transitivity₁ (fun z ↦ (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹)
      · simp_rw [add_comm (a := a / c), ← sub_neg_eq_add (b := a / c)]
        apply isBigO_characteristic_sub_characteristic_shift (by fun_prop)
      apply transitivity₁ (f · + d / c)⁻¹
      · apply isBigO_characteristic_sub_characteristic_const_mul (by fun_prop)
        grind
      apply transitivity₁ (f · + d / c) (isBigO_characteristic_sub_characteristic_inv (by fun_prop))
      apply transitivity₁
      · simp_rw [← sub_neg_eq_add]
        apply isBigO_characteristic_sub_characteristic_shift (by fun_prop)
      rw [sub_self]
      apply Asymptotics.isBigO_const_one
    · -- Degenerate case: the denominator vanishes away from a codiscrete set.
      simp only [ne_eq, not_forall, Decidable.not_not] at hord
      rw [Meromorphic.exists_meromorphicOrderAt_eq_top_iff_eventually_zero (by fun_prop)] at hord
      apply transitivity₁ fun _ ↦ -(d / c)
      · apply transitivity₂ (f₂ := 0)
        · filter_upwards [hord] with z hz
          simp_all
        · simp [Pi.one_def, isBoundedUnder_const]
      · apply transitivity₂ (f₂ := f) (f₃ := fun _ ↦ -(d / c))
        · filter_upwards [hord] with z hz
          rw [Pi.zero_apply] at hz
          field_simp
          linear_combination hz
        · rw [sub_self]
          apply Asymptotics.isBigO_const_one

end moebius

end ValueDistribution
