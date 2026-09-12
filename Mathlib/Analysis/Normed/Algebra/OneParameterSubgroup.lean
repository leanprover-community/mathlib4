/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

/-!
# One-parameter subgroups of real Banach algebras

Let `E` be a real Banach algebra. This file proves that every continuous one-parameter subgroup of
`Eˣ` is of the form `t ↦ exp (t • A)` for a unique `A : E`.

The parameter group is `Multiplicative ℝ`. Let `F` be a function-like type from `Multiplicative ℝ`
to `Eˣ`, equipped with `MonoidHomClass` and `ContinuousMapClass` instances. Coercion from `Eˣ` to
`E` associates to each `U : F` an `E`-valued curve to which integration, differentiation, and the
algebra exponential apply.

## Main result

* `OneParameterSubgroup.existsUnique_generator`: A continuous one-parameter subgroup of a real
  Banach algebra has a unique exponential generator.

## Proof outline

Continuity at zero implies that, for sufficiently small `d > 0`, the integral of `U` over `[0, d]`
is close to `d • 1` and therefore invertible. If `I` is the indefinite integral of `U`, the
homomorphism law gives `U(t) * I(d) = I(t + d) - I(t)`. This identity proves that `U` is
differentiable. Setting `A` to the derivative at zero then gives the differential equation
`U'(t) = U(t)A`. Consequently `U(t) * exp (-tA)` has zero derivative and is constant. Uniqueness
follows by differentiating two exponential representations at zero.
-/

public section

open Filter Topology

noncomputable section

namespace OneParameterSubgroup

variable {E F : Type*} [NormedRing E] [FunLike F (Multiplicative ℝ) Eˣ]
  [MonoidHomClass F (Multiplicative ℝ) Eˣ] [ContinuousMapClass F (Multiplicative ℝ) Eˣ]

private def ambientValue (U : F) (t : ℝ) : E := U (.ofAdd t)

omit [ContinuousMapClass F (Multiplicative ℝ) Eˣ] in
@[simp] private theorem ambientValue_zero (U : F) : ambientValue U 0 = 1 := by
  simp [ambientValue]

omit [ContinuousMapClass F (Multiplicative ℝ) Eˣ] in
@[simp] private theorem ambientValue_add (U : F) (s t : ℝ) :
    ambientValue U (s + t) = ambientValue U s * ambientValue U t := by
  exact congrArg Units.val (map_mul U (.ofAdd s) (.ofAdd t))

omit [MonoidHomClass F (Multiplicative ℝ) Eˣ] in
private theorem continuous_ambientValue (U : F) : Continuous (ambientValue U) := by
  exact Units.continuous_val.comp ((map_continuous U).comp continuous_ofAdd)

variable [NormedAlgebra ℝ E] [CompleteSpace E]

private def scalarUnit (d : ℝ) (hd : d ≠ 0) : Eˣ where
  val := d • 1
  inv := d⁻¹ • 1
  val_inv := by rw [smul_mul_smul_comm, mul_inv_cancel₀ hd, one_smul, one_mul]
  inv_val := by rw [smul_mul_smul_comm, inv_mul_cancel₀ hd, one_smul, one_mul]

private theorem exists_isUnit_intervalIntegral [Nontrivial E] (U : F) :
    ∃ d : ℝ, 0 < d ∧ IsUnit (∫ x in (0 : ℝ)..d, ambientValue U x) := by
  let c : ℝ := ‖(1 : E)‖⁻¹ / 2
  have hone : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero
  have hc : 0 < c := by dsimp [c]; positivity
  have hevent : ∀ᶠ x : ℝ in 𝓝 0, ‖ambientValue U x - 1‖ < c := by
    have hnorm : Continuous (fun x : ℝ => ‖ambientValue U x - 1‖) :=
      continuous_norm.comp ((continuous_ambientValue U).sub continuous_const)
    have hmem : Set.Iio c ∈ 𝓝 ‖ambientValue U 0 - 1‖ := by simpa using Iio_mem_nhds hc
    exact hnorm.continuousAt hmem
  rw [Metric.eventually_nhds_iff] at hevent
  obtain ⟨r, hr, hrU⟩ := hevent
  let d := r / 2
  have hd : 0 < d := by dsimp [d]; positivity
  let q : Eˣ := scalarUnit d hd.ne'
  have hnear : ‖(∫ x in (0 : ℝ)..d, ambientValue U x) - (q : E)‖ < ‖(↑q⁻¹ : E)‖⁻¹ := by
    have hqd : (q : E) = d • 1 := rfl
    have hrewrite : (∫ x in (0 : ℝ)..d, ambientValue U x) - (q : E) =
        ∫ x in (0 : ℝ)..d, (ambientValue U x - 1) := by
      rw [hqd]
      calc
        (∫ x in (0 : ℝ)..d, ambientValue U x) - d • 1 =
            (∫ x in (0 : ℝ)..d, ambientValue U x) - ∫ _x in (0 : ℝ)..d, (1 : E) := by
              rw [intervalIntegral.integral_const, sub_zero]
        _ = ∫ x in (0 : ℝ)..d, (ambientValue U x - 1) :=
          (intervalIntegral.integral_sub ((continuous_ambientValue U).intervalIntegrable 0 d)
            (continuous_const.intervalIntegrable 0 d)).symm
    rw [hrewrite]
    have hle : ‖∫ x in (0 : ℝ)..d, (ambientValue U x - 1)‖ ≤ c * d := by
      calc
        _ ≤ c * |d - 0| := intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
          apply le_of_lt
          apply hrU
          rw [Real.dist_0_eq_abs]
          rw [Set.uIoc_of_le hd.le] at hx
          rw [abs_of_nonneg hx.1.le]
          exact hx.2.trans_lt (by dsimp [d]; linarith))
        _ = c * d := by rw [sub_zero, abs_of_pos hd]
    have hright : ‖(↑q⁻¹ : E)‖⁻¹ = d * ‖(1 : E)‖⁻¹ := by
      have hqinv : (↑q⁻¹ : E) = d⁻¹ • (1 : E) := rfl
      rw [hqinv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd]
      field_simp
    rw [hright]
    refine hle.trans_lt ?_
    dsimp [c]
    nlinarith [inv_pos.mpr hone]
  exact ⟨d, hd, (Units.ofNearby q _ hnear).isUnit⟩

private theorem differentiable_ambientValue [Nontrivial E] (U : F) :
    Differentiable ℝ (ambientValue U) := by
  obtain ⟨d, _, hV⟩ := exists_isUnit_intervalIntegral U
  let V : E := ∫ x in (0 : ℝ)..d, ambientValue U x
  let v : Eˣ := hV.unit
  have hv : (v : E) = V := hV.unit_spec
  let F : ℝ → E := fun t => ∫ x in (0 : ℝ)..t, ambientValue U x
  have hF (t : ℝ) : HasDerivAt F (ambientValue U t) t :=
    ((continuous_ambientValue U).integral_hasStrictDerivAt 0 t).hasDerivAt
  have htranslate (t : ℝ) : ambientValue U t * V = F (t + d) - F t := by
    have hmul : ambientValue U t * V = ∫ x in (0 : ℝ)..d, ambientValue U (t + x) := by
      let L : E →L[ℝ] E :=
        (LinearMap.mulLeft ℝ (ambientValue U t)).mkContinuous ‖ambientValue U t‖
          (fun x => norm_mul_le _ _)
      change ambientValue U t * (∫ x in (0 : ℝ)..d, ambientValue U x) = _
      calc
        _ = L (∫ x in (0 : ℝ)..d, ambientValue U x) := rfl
        _ = ∫ x in (0 : ℝ)..d, L (ambientValue U x) :=
          (L.intervalIntegral_comp_comm ((continuous_ambientValue U).intervalIntegrable 0 d)).symm
        _ = ∫ x in (0 : ℝ)..d, ambientValue U (t + x) := by
          apply intervalIntegral.integral_congr
          intro x _
          change ambientValue U t * ambientValue U x = ambientValue U (t + x)
          exact (ambientValue_add U t x).symm
    rw [hmul]
    dsimp only [F]
    rw [intervalIntegral.integral_comp_add_left]
    simp only [add_zero]
    rw [eq_sub_iff_add_eq, add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) ((continuous_ambientValue U).intervalIntegrable 0 t)
      ((continuous_ambientValue U).intervalIntegrable t (t + d))
  intro t
  have hR : HasDerivAt (fun s : ℝ => F (s + d) - F s)
      (ambientValue U (t + d) - ambientValue U t) t := by
    exact (HasDerivAt.comp_add_const t d (hF (t + d))).sub (hF t)
  have heq : ambientValue U = fun s : ℝ => (F (s + d) - F s) * (↑v⁻¹ : E) := by
    funext s
    calc
      ambientValue U s = (ambientValue U s * (v : E)) * (↑v⁻¹ : E) := by simp
      _ = (F (s + d) - F s) * (↑v⁻¹ : E) := by rw [hv, htranslate]
  rw [heq]
  exact (hR.mul_const (↑v⁻¹ : E)).differentiableAt

private theorem exists_generator_of_nontrivial [Nontrivial E] (U : F) :
    ∃ A : E, ∀ t : ℝ, (U (.ofAdd t) : E) = NormedSpace.exp (t • A) := by
  let +nondep : NormedAlgebra ℚ E := .restrictScalars ℚ ℝ E
  have hdiff : Differentiable ℝ (ambientValue U) := differentiable_ambientValue U
  let A : E := deriv (ambientValue U) 0
  have hU (t : ℝ) : HasDerivAt (ambientValue U) (ambientValue U t * A) t := by
    have ht : HasDerivAt (ambientValue U) (deriv (ambientValue U) t) t :=
      hdiff.differentiableAt.hasDerivAt
    have h0 : HasDerivAt (ambientValue U) (deriv (ambientValue U) 0) 0 :=
      hdiff.differentiableAt.hasDerivAt
    have hleft : HasDerivAt (fun s : ℝ => ambientValue U (t + s))
        (deriv (ambientValue U) t) 0 :=
      HasDerivAt.comp_const_add t 0 (by simpa using ht)
    have hright : HasDerivAt (fun s : ℝ => ambientValue U t * ambientValue U s)
        (ambientValue U t * A) 0 := by
      dsimp only [A]
      exact HasDerivAt.const_mul (ambientValue U t) h0
    have heq : (fun s : ℝ => ambientValue U (t + s)) =
        fun s : ℝ => ambientValue U t * ambientValue U s := by
      funext s
      exact ambientValue_add U t s
    have hder : deriv (ambientValue U) t = ambientValue U t * A := hleft.unique (heq ▸ hright)
    rwa [← hder]
  have hE (t : ℝ) : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (-A)))
      (NormedSpace.exp (t • (-A)) * (-A)) t := hasDerivAt_exp_smul_const (-A) t
  let G : ℝ → E := fun t => ambientValue U t * NormedSpace.exp (t • (-A))
  have hG : Differentiable ℝ G := fun t => ((hU t).mul (hE t)).differentiableAt
  have hGder (t : ℝ) : deriv G t = 0 := by
    apply ((hU t).mul (hE t)).deriv.trans
    have hcomm : Commute A (NormedSpace.exp (t • (-A))) := by
      exact ((Commute.refl A).neg_right.smul_right t).exp_right
    rw [mul_assoc, hcomm.eq]
    noncomm_ring
  have hconst (t : ℝ) : G t = G 0 := is_const_of_deriv_eq_zero hG hGder t 0
  refine ⟨A, fun t => ?_⟩
  have hone : ambientValue U t * NormedSpace.exp (t • (-A)) = 1 := by
    simpa [G] using hconst t
  have hneg : t • (-A) = -(t • A) := by module
  have hinv : NormedSpace.exp (t • (-A)) = Ring.inverse (NormedSpace.exp (t • A)) := by
    rw [hneg]
    exact (Ring.inverse_exp (t • A)).symm
  rw [hinv] at hone
  have hexp : IsUnit (NormedSpace.exp (t • A)) := NormedSpace.isUnit_exp (t • A)
  let e : Eˣ := hexp.unit
  have he : (e : E) = NormedSpace.exp (t • A) := hexp.unit_spec
  rw [← he, Ring.inverse_unit] at hone
  calc
    ambientValue U t = (ambientValue U t * (↑e⁻¹ : E)) * (e : E) := by simp
    _ = NormedSpace.exp (t • A) := by
      rw [hone, one_mul, he]

/-- Every continuous one-parameter subgroup of the unit group of a real Banach algebra is the
exponential of a unique element of the algebra. -/
theorem existsUnique_generator (U : F) :
    ∃! A : E, ∀ t : ℝ, (U (.ofAdd t) : E) = NormedSpace.exp (t • A) := by
  let +nondep : NormedAlgebra ℚ E := .restrictScalars ℚ ℝ E
  cases subsingleton_or_nontrivial E with
  | inl h =>
      let : Subsingleton E := h
      refine ⟨0, fun _ => Subsingleton.elim _ _, fun A _ => Subsingleton.elim A 0⟩
  | inr h =>
      let : Nontrivial E := h
      obtain ⟨A, hA⟩ := exists_generator_of_nontrivial U
      refine ⟨A, hA, fun B hB => ?_⟩
      have hfun : (fun t : ℝ => NormedSpace.exp (t • A)) =
          fun t : ℝ => NormedSpace.exp (t • B) := by
        funext t
        exact (hA t).symm.trans (hB t)
      have hder := congrArg (fun f : ℝ → E => deriv f 0) hfun
      have h_exp (C : E) : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • C)) C 0 := by
        simpa using hasDerivAt_exp_smul_const C (0 : ℝ)
      exact (h_exp B).deriv.symm.trans (hder.symm.trans (h_exp A).deriv)

end OneParameterSubgroup
