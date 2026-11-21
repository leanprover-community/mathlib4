/-
Copyright (c) 2026 Michael Novak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Novak
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Plane curves

In this file we introduce basic definitions related to plane curves: `orientedCurvature`, which is
usually called just the curvature of a plane curve, `normal`, the normal vector to every point of a
plane curve and `frameAt` the so called Frenet moving frame. We also prove some classic results in
the subject of differential geometry of plane curves: the Frenet equations and the fundamental
theorem of plane curves.

## Main results

- `second_deriv_eq_orientedCurvature_times_normal`: the first Frenet equation for plane curves.
- `deriv_normal_eq_minus_orientedCurvature_times_deriv`: the second Frenet equation for plane
  curves.
- `initialCurve_of_orientedCurvature`: the construction of a plane curve from a given curvature
  function, initial position, initial direction (angle) for the velocity vector, as given by the
  fundamental theorem of plane curves.
- `_root_.ContDiffOn.initialCurve_of_orientedCurvature`: Showing that the curve we construct in the
  fundamental theorem of plane curves is twice continuously differentiable.
- `initialCurve_of_orientedCurvature_has_unit_speed`: Showing that the curve we construct in the
  fundamental theorem of plane curves is parametrized by arc-length, or in other words has unit
  speed.
- `orientedCurvature_initialCurve_of_orientedCurvature`: Showing that the curve we construct in the
  fundamental theorem of plane curves has the given curvature function.
- `position_initial_condition_initialCurve_of_orientedCurvature`: Showing that the curve we
  construct in the fundamental theorem of plane curves has the desired initial position.
- `velocity_initial_condition_initialCurve_of_orientedCurvature`: Showing that the curve we
  construct in the fundamental theorem of plane curves has the desired initial velocity vector.
- `initialCurve_of_orientedCurvature_is_unique`: The uniqueness part of the fundamental theorem of
  plane curves.

## References

We mainly followed [zbMATH07533267], especially for the fundamental theorem of plane curves.
-/

@[expose] public section

noncomputable section

namespace PlaneCurve

variable {I : Set ℝ} {c : ℝ → EuclideanSpace ℝ (Fin 2)} {t : ℝ}

/-- Oriented curvature of a plane curve `c` at `t`.
This curvature expresses a direction / orientation in the following way:
Denote `v = deriv c t`, `a = iteratedDeriv 2 c t`, `n = normal c t` and `κ = orientedCurvature c t`.
Then for a general plane curve, if (`v`, `a`) is a positvely oriented, then `κ` is positive, and if
it's negatively oriented, then `κ` is negative (geometrically the orientation of a basis of the
plane is positive when the basis vectors are ordered anti-clockwise and negative when ordered
clockwise). It's useful for understanding also to consider the case in which `c` is parametrized by
arc-length, in which case `a` is in the span of `n` and `κ` is positive if `a` is in the same
direction as `n` and negative if `a` is in the opposite direction of `n`.
This definition is meaningful only when `c` is two times differentiable at `t` with a non-zero
derivative; otherwise it has junk value `0`. -/
def orientedCurvature (c : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℝ :=
  !![deriv c t 0, deriv c t 1; iteratedDeriv 2 c t 0, iteratedDeriv 2 c t 1].det / (‖deriv c t‖ ^ 3)

/-- See also `orientedCurvature_of_norm_deriv_eq_one` for the special case where `‖deriv c t‖ = 1`.
(this is useful usually for plane curves parametrized by arc-length). -/
lemma orientedCurvature_eq : orientedCurvature c t = !![deriv c t 0, deriv c t 1;
    iteratedDeriv 2 c t 0, iteratedDeriv 2 c t 1].det / (‖deriv c t‖ ^ 3) := rfl

/-- Normal vector at a point of a plane curve.
This definition is only meaningful when `c` is differentiable at `t` with non-zero derivative. -/
def normal (c : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    EuclideanSpace ℝ (Fin 2) := ‖deriv c t‖⁻¹ • !₂[-(deriv c t 1), deriv c t 0]

lemma normal_eq : normal c t = ‖deriv c t‖⁻¹ • !₂[-(deriv c t 1), deriv c t 0] := rfl

/-- A lemma that gives us a formula for the normal when the derivative has length 1, this is
useful especially for plane curves parametrized by arc-length (with unit speed). -/
lemma normal_eq_of_norm_deriv_eq_one (h : ‖deriv c t‖ = 1) :
    normal c t = !₂[-(deriv c t 1), deriv c t 0] := by
  simp [normal_eq, h]

variable (c t) in
/-- The `normal` vector at point of a plane curve is orthogonal to the velocity vector at the point.
-/
theorem inner_deriv_normal_eq_zero : inner ℝ (deriv c t) (normal c t) = 0 := by
  rw [normal_eq, real_inner_smul_right]
  simp [PiLp.inner_apply, real_inner_eq_re_inner, mul_comm]

/-- The `normal` vector at point with a non-zero derivative of a plane curve has length 1 (is a unit
vector). -/
theorem norm_normal_eq_one_of_non_zero_deriv (h : deriv c t ≠ 0) : ‖normal c t‖ = 1 := by
  rw [normal_eq, NormSMulClass.norm_smul, norm_inv, norm_norm]
  simp only [Fin.isValue, EuclideanSpace.norm_eq !₂[-(deriv c t).ofLp 1, (deriv c t).ofLp 0],
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_two, Matrix.cons_val_zero, even_two, Even.neg_pow,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, add_comm]
  rw [show √((deriv c t).ofLp 0 ^ 2 + (deriv c t).ofLp 1 ^ 2) = √(∑ i, ‖(deriv c t).ofLp i‖ ^ 2) by
    simp, ← EuclideanSpace.norm_eq (deriv c t), show ‖deriv c t‖⁻¹ * ‖deriv c t‖ = ‖deriv c t‖ /
    ‖deriv c t‖ by ring, div_self (norm_ne_zero_iff.mpr h)]

/-- A special useful case, unit speed at a point implies that the normal is a unit vector as well -/
theorem norm_normal_eq_one_of_norm_deriv_eq_one (h : ‖deriv c t‖ = 1) : ‖normal c t‖ = 1 :=
  have h' : deriv c t ≠ 0 := by
    rw [← norm_ne_zero_iff, h]
    exact one_ne_zero
  norm_normal_eq_one_of_non_zero_deriv h'

/-- For every plane curve `c` parametrized by arc-length, the velocity vector `deriv c` and the
`normal` vector at each point form an orthonormal basis of the plane, which is sometimes called the
moving frame of the curve or the Frenet frame, which we call `frameAt`. -/
def frameAt (hc : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  let B := ![deriv c t, normal c t]
  have hBon : Orthonormal ℝ B := by
    constructor
    · intro i
      fin_cases i
      <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.isValue]
      · exact hc t ht
      · exact norm_normal_eq_one_of_norm_deriv_eq_one (hc t ht)
    · intro i j hinej
      fin_cases i
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ne_eq] at hinej
        have h : j=1 := Fin.eq_one_of_ne_zero j fun a ↦ hinej (id (Eq.symm a))
        simp only [h, Fin.isValue]
        exact inner_deriv_normal_eq_zero c t
      · simp at hinej
        have h : j=0 := by fin_cases j <;> trivial
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, h, real_inner_comm]
        exact inner_deriv_normal_eq_zero c t
  have hBsp : ⊤ ≤ Submodule.span ℝ (Set.range B) := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, top_le_iff]
    apply hBon.linearIndependent.span_eq_top_of_card_eq_finrank; simp
  OrthonormalBasis.mk (v := B) (hon := hBon) (hsp := hBsp)

set_option backward.isDefEq.respectTransparency false in
/-- A simpler formula for the curvature (`orientedCurvature`) of a plane curve `c` with unit
derivative at `t` (usually used when `c` is parametrized by arc-length, i.e, with unit speed). -/
theorem orientedCurvature_of_norm_deriv_eq_one (h : ‖deriv c t‖ = 1) :
    orientedCurvature c t = inner ℝ (iteratedDeriv 2 c t) (normal c t) := by
  simp only [orientedCurvature_eq, normal_eq_of_norm_deriv_eq_one h, h,
    Fin.isValue, Matrix.det_fin_two_of, one_pow, div_one, EuclideanSpace.inner_eq_star_dotProduct,
    Fin.isValue, star_trivial, Matrix.cons_dotProduct, neg_mul, Matrix.dotProduct_of_isEmpty,
    add_zero]
  exact sub_eq_neg_add ((deriv c t).ofLp 0 * (iteratedDeriv 2 c t).ofLp 1)
    ((deriv c t).ofLp 1 * (iteratedDeriv 2 c t).ofLp 0)

universe u

variable {ι : Type u} [Fintype ι] {γ : ℝ → EuclideanSpace ℝ ι}

/-- If `γ` is a twice continuously differentiable parametrized curve on an interval
`I`, then the velocity vector `deriv γ` has a derivative at every point of `I`. -/
lemma hasDerivAt_deriv_of_contDiffOn (hI : IsOpen I) (hγ : ContDiffOn ℝ 2 γ I) (ht : t ∈ I) :
    HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t := by
  have hd : ContDiffOn ℝ 1 (deriv γ) I := hγ.deriv_of_isOpen hI (by norm_num)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (hd.differentiableOn (by norm_num)).hasDerivAt (hI.mem_nhds ht)

/-- Given a continuously differentiable parametrized curve `c` whose position has the same magnitude
at all time, i.e, at constant radius distance from the origin (the curve `γ` is contained in a
sphere of radius `r` from the origin), then the velocity vector `deriv γ` is always perpendicular to
the position vector of the curve at every point (in other words their dot product is zero). -/
theorem inner_deriv_curve_eq_zero_of_const_norm_curve (hI : IsOpen I)
    (hγ₁ : ContDiffOn ℝ 1 γ I) {r : ℝ} (hγ₂ : ∀ t ∈ I, ‖γ t‖ = r) (ht : t ∈ I) :
    inner ℝ (deriv γ t) (γ t) = 0 := by
  have h : I.EqOn (fun x ↦ inner ℝ (γ x) (γ x)) (fun x ↦ r ^ 2) := fun x hx ↦ by simp [hγ₂ x hx]
  have hd : HasDerivAt γ (deriv γ t) t :=
    (hγ₁.contDiffAt (hI.mem_nhds ht)).differentiableAt_one.hasDerivAt
  suffices 2 * inner ℝ (deriv γ t) (γ t) = 0 by simpa
  rw [← inners_sum_eq_zero_of_const_inner_on_open hI ht hd hd h, real_inner_comm, two_mul]

/-- For any twice continuously differentiable parametrized curve with constant speed, at any given
point the velocity vector is perpendicular to the acceleration vector. -/
theorem inner_second_deriv_deriv_eq_zero_of_const_norm_deriv (hI : IsOpen I)
    (hγ₁ : ContDiffOn ℝ 2 γ I) {r : ℝ} (hγ₂ : ∀ t ∈ I, ‖deriv γ t‖ = r) (ht : t ∈ I) :
    inner ℝ (iteratedDeriv 2 γ t) (deriv γ t) = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, inner_deriv_curve_eq_zero_of_const_norm_curve hI
    ((contDiffOn_succ_iff_deriv_of_isOpen hI).mp (by assumption)).2.2 hγ₂ ht]

/-- The first Frenet equation for plane curves: For any twice continously differentiable plane curve
parametrized by arc-length (i.e., with unit speed), the second derivative, i.e. acceleration vector
is equal to the curvature times the normal vector. -/
theorem second_deriv_eq_orientedCurvature_times_normal (hI : IsOpen I) (hc₁ : ContDiffOn ℝ 2 c I)
    (hc₂ : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    iteratedDeriv 2 c t = (orientedCurvature c t)•(normal c t) := by
  rw [orientedCurvature_of_norm_deriv_eq_one (hc₂ t ht)]
  nth_rewrite 1 [← (frameAt hc₂ ht).sum_repr' (iteratedDeriv 2 c t)]
  simp only [frameAt, Nat.succ_eq_add_one, Nat.reduceAdd, OrthonormalBasis.coe_mk, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [real_inner_comm , real_inner_comm (iteratedDeriv 2 c t),
    inner_second_deriv_deriv_eq_zero_of_const_norm_deriv hI hc₁ hc₂ ht]; simp

/-- Auxiliary lemma: If `c` is a twice continuously differentiable plane curve on an interval `I`,
then the normal has a derivative at every point of `I`. -/
protected lemma _root_.HasDerivAt.normal (hI : IsOpen I) (hc₁ : ContDiffOn ℝ 2 c I) (ht : t ∈ I)
    (hc₂ : ∀ t ∈ I, ‖deriv c t‖ = 1) : HasDerivAt (normal c) (deriv (normal c) t) t := by
  have hd : ContDiffOn ℝ 1 (deriv c) I := hc₁.deriv_of_isOpen hI (by norm_num)
  have hD : DifferentiableOn ℝ (deriv c) I := hd.differentiableOn (by norm_num)
  simp only [hasDerivAt_deriv_iff]
  have h : DifferentiableOn ℝ (fun τ ↦  normal c τ) I := by
    have hn : ∀ τ ∈ I, normal c τ = !₂[-(deriv c τ 1), deriv c τ 0] :=
      fun τ hτ ↦ normal_eq_of_norm_deriv_eq_one (hc₂ τ hτ)
    rw [differentiableOn_congr hn, differentiableOn_piLp] at *
    intro i
    fin_cases i <;> simp [hD]
  exact h.differentiableAt (hI.mem_nhds ht)

@[fun_prop]
lemma _root_.ContDiffOn.normal_of_twice_contDiffOn (hI : IsOpen I) (hc₁ : ContDiffOn ℝ 2 c I)
    (hc₂ : ∀ t ∈ I, ‖deriv c t‖ = 1) : ContDiffOn ℝ 1 (normal c) I := by
  have hd : ContDiffOn ℝ 1 (deriv c) I := hc₁.deriv_of_isOpen hI (by norm_num)
  have hn : ∀ τ ∈ I, normal c τ = !₂[-(deriv c τ 1), deriv c τ 0] :=
    fun τ hτ ↦ normal_eq_of_norm_deriv_eq_one (hc₂ τ hτ)
  rw [contDiffOn_congr hn, contDiffOn_piLp] at *
  intro i
  fin_cases i
  · simp [ContDiffOn.neg, hd 1]
  · simp [hd 0]

/-- For any twice continuously differentiable plane curve with constant speed, at any given point
the normal vector is perpendicular to the derivative of the normal vector. -/
theorem inner_deriv_normal_normal_eq_zero_of_norm_deriv_eq_one (hI : IsOpen I)
    (hc₁ : ContDiffOn ℝ 2 c I) (hc₂ : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    inner ℝ  (deriv (normal c) t) (normal c t) = 0 :=
  inner_deriv_curve_eq_zero_of_const_norm_curve hI (by fun_prop (disch := assumption))
    (fun _ ht ↦  norm_normal_eq_one_of_norm_deriv_eq_one (hc₂ _ ht)) ht

theorem inner_deriv_deriv_normal_eq_minus_orientedCurvature (hI : IsOpen I)
    (hc₁ : ContDiffOn ℝ 2 c I) (hc₂ : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    inner ℝ (deriv c t) (deriv (normal c) t) = - orientedCurvature c t := by
  rw [← add_eq_zero_iff_eq_neg', add_comm]
  symm
  have hci : Set.EqOn (fun x ↦ inner ℝ (normal c x) (deriv c x)) (fun x ↦ 0) I := by
    intro x hx
    simp only
    rw [real_inner_comm, inner_deriv_normal_eq_zero]
  rw [← inners_sum_eq_zero_of_const_inner_on_open hI ht (HasDerivAt.normal hI hc₁ ht hc₂)
    (hasDerivAt_deriv_of_contDiffOn hI hc₁ ht) hci, second_deriv_eq_orientedCurvature_times_normal
    hI hc₁ hc₂ ht, real_inner_comm, inner_smul_left_eq_smul]
  simp only [inner_self_eq_norm_sq_to_K, norm_normal_eq_one_of_norm_deriv_eq_one (hc₂ t ht),
    RCLike.ofReal_real_eq_id, id_eq, one_pow, smul_eq_mul, mul_one, add_comm, real_inner_comm]

/-- The second Frenet equation for plane curves: For any twice continously differentiable plane
curve parametrized by arc-length (i.e., with unit speed), the derivative of the normal vector is
equal to minus the curvature times the velocity vector (first derivative). -/
theorem deriv_normal_eq_minus_orientedCurvature_times_deriv (hI : IsOpen I)
    (hc₁ : ContDiffOn ℝ 2 c I) (hc₂ : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    deriv (normal c) t = -(orientedCurvature c t)•(deriv c t) := by
  rw [← (frameAt hc₂ ht).sum_repr' (deriv (normal c) t)]
  simp only [frameAt, Nat.succ_eq_add_one, Nat.reduceAdd, OrthonormalBasis.coe_mk, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_smul,
    real_inner_comm (deriv (normal c) t) (normal c t),
    inner_deriv_normal_normal_eq_zero_of_norm_deriv_eq_one hI hc₁ hc₂ ht]
  simp [inner_deriv_deriv_normal_eq_minus_orientedCurvature hI hc₁ hc₂ ht]

/-- This is the plane curve we construct in the fundamental theorem of plane curves, given curvature
function κ, initial position p₀ at time t₀ and initial velocity vector condition given by an angle
θ₀ (this angle is a choice of direction for the unit velocity vector at time t₀). This definition is
only meaningful when κ is continuous on some given interval. -/
def initialCurve_of_orientedCurvature (κ : ℝ → ℝ) (t₀ : ℝ) (p₀ : EuclideanSpace ℝ (Fin 2))
    (θ₀ : ℝ) : ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun t ↦  !₂[p₀ 0 + ∫τ in t₀..t, Real.cos (θ₀ + ∫ξ in t₀..τ, κ ξ),
    p₀ 1 + ∫τ in t₀..t, Real.sin (θ₀ + ∫ξ in t₀..τ, κ ξ)]

variable {κ : ℝ → ℝ} {t₀ : ℝ} (θ₀ : ℝ) (p₀ : EuclideanSpace ℝ (Fin 2)) {t : ℝ}
  [hIoC : I.OrdConnected]

/-- Auxiliary lemma which says that the angle function (fun x ↦ θ₀ + ∫ξ in t₀..x, κ ξ) is continuous
on the interval I. -/
@[fun_prop]
lemma continuousOn_angle_fun_aux (hI : IsOpen I) (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) :
    ContinuousOn (fun x ↦ θ₀ + ∫ (ξ : ℝ) in t₀..x, κ ξ) I := by
  have h : ContinuousOn (fun x ↦ ∫ (ξ : ℝ) in t₀..x, κ ξ) I := by
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, Metric.ball t₀ ε ⊆ I := Metric.isOpen_iff.mp hI t₀ ht₀
    intro x hx
    exact (intervalIntegral.hasDerivAt_integral_of_continuousOn_open_interval
           hI hκ ht₀ hx).continuousAt.continuousWithinAt
  fun_prop

protected lemma _root_.HasDerivWithinAt.initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivWithinAt (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)
    !₂[Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ), Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ)] I t := by
  rw [hasDerivWithinAt_pi_euclidean]
  unfold initialCurve_of_orientedCurvature
  have h := continuousOn_angle_fun_aux θ₀ hI hκ ht₀
  intro i
  fin_cases i
  all_goals
    simp only [Fin.zero_eta,Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
               hasDerivWithinAt_const_add_iff]
    exact intervalIntegral.hasDerivWithinAt_of_continuousOn_interval (by fun_prop) ht₀ ht

lemma _root_.HasDerivAt.initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivAt (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)
    !₂[Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ), Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ)] t :=
  (HasDerivWithinAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht).hasDerivAt
    (hI.mem_nhds ht)

/-- Auxiliary lemma giving us the `derivWithin` the interval `I` of a certain function. -/
lemma hasDerivWithinAt_some_function₀_aux (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivWithinAt (fun x ↦  θ₀ + ∫ξ in t₀..x, κ ξ) (κ t) I t := by
  rw [← zero_add (κ t)]
  exact (hasDerivWithinAt_const t I θ₀).add
    (intervalIntegral.hasDerivWithinAt_of_continuousOn_interval hκ ht₀ ht)

/-- Auxiliary lemma giving us the `derivWithin` the interval `I` of a certain function. -/
lemma hasDerivWithinAt_some_function₁_aux (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivWithinAt (fun x ↦ Real.cos (θ₀ + ∫ (ξ : ℝ) in t₀..x, κ ξ))
                     (-(κ t * Real.sin (θ₀ + ∫ (ξ : ℝ) in t₀..t, κ ξ))) I t := by
  rw [show -(κ t * Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ)) = -Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ) * κ t
    by ring, show (fun t ↦  Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ))
    = Real.cos ∘ (fun x ↦  θ₀ + ∫ξ in t₀..x, κ ξ) from rfl]
  have h : HasDerivAt Real.cos (-Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ))
    ((fun τ ↦  θ₀ + ∫ξ in t₀..τ, κ ξ) t) := by simp [Real.hasDerivAt_cos]
  exact h.comp_hasDerivWithinAt t (hasDerivWithinAt_some_function₀_aux θ₀ hκ ht₀ ht)

/-- Auxiliary lemma giving us the `derivWithin` the interval `I` of a certain function. -/
lemma hasDerivWithinAt_some_function₂_aux (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivWithinAt (fun x ↦ Real.sin (θ₀ + ∫ (ξ : ℝ) in t₀..x, κ ξ))
                     (κ t * Real.cos (θ₀ + ∫ (ξ : ℝ) in t₀..t, κ ξ)) I t:= by
  rw [show κ t * Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ) = Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ) * κ t
    by ring, show (fun t ↦  Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ))
    = Real.sin ∘ (fun x ↦  θ₀ + ∫ξ in t₀..x, κ ξ) from rfl]
  have h : HasDerivAt Real.sin (Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ))
   ((fun τ ↦  θ₀ + ∫ξ in t₀..τ, κ ξ) t) := by simp [Real.hasDerivAt_sin]
  exact h.comp_hasDerivWithinAt t (hasDerivWithinAt_some_function₀_aux θ₀ hκ ht₀ ht)

lemma _root_.HasDerivAt.deriv_initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivAt (deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀))
    !₂[-(κ t)*Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ), (κ t)*Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ)] t := by
  have h : I.EqOn (deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀))
    (fun x ↦  !₂[Real.cos (θ₀+∫ξ in t₀..x, κ ξ), Real.sin (θ₀+∫ξ in t₀..x, κ ξ)]) :=
    fun x hx ↦  (HasDerivAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ hx).deriv
  have h' : HasDerivWithinAt (fun x ↦ !₂[Real.cos (θ₀ + ∫ξ in t₀..x, κ ξ), Real.sin (θ₀
    + ∫ξ in t₀..x, κ ξ)]) !₂[-κ t *Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ),κ t *Real.cos (θ₀
    + ∫ξ in t₀..t, κ ξ)] I t := by
    rw [hasDerivWithinAt_pi_euclidean]
    intro i
    fin_cases i <;> simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_mul]
    · exact hasDerivWithinAt_some_function₁_aux θ₀ hκ ht₀ ht
    · exact hasDerivWithinAt_some_function₂_aux θ₀ hκ ht₀ ht
  exact (h'.congr h (h ht)).hasDerivAt (hI.mem_nhds ht)

lemma second_deriv_of_initialCurve_of_orientedCurvature (hI : IsOpen I) (hκ : ContinuousOn κ I)
    (ht₀ : t₀ ∈ I) (ht : t ∈ I) : iteratedDeriv 2 (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) t
    = !₂[-(κ t)*Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ), (κ t)*Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ)] := by
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    (HasDerivAt.deriv_initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht).deriv]

@[fun_prop]
lemma _root_.ContinuousOn.initialCurve_of_orientedCurvature (hI : IsOpen I) (hκ : ContinuousOn κ I)
    (ht₀ : t₀ ∈ I) : ContinuousOn (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) I :=
  HasDerivAt.continuousOn
    (fun _ h ↦  HasDerivAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ h)

@[fun_prop]
lemma _root_.ContinuousOn.deriv_initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) :
    ContinuousOn (deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)) I :=
  HasDerivAt.continuousOn
    (fun _ h ↦  HasDerivAt.deriv_initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ h)

@[fun_prop]
lemma _root_.DifferentiableOn.initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) :
    DifferentiableOn ℝ (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) I :=
  fun _ h ↦  (HasDerivAt.initialCurve_of_orientedCurvature
    θ₀ p₀ hI hκ ht₀ h).differentiableAt.differentiableWithinAt

@[fun_prop]
lemma _root_.DifferentiableOn.deriv_initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) :
    DifferentiableOn ℝ (deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)) I :=
  fun _ h ↦  (HasDerivAt.deriv_initialCurve_of_orientedCurvature
    θ₀ p₀ hI hκ ht₀ h).differentiableAt.differentiableWithinAt

/-- The plane curve we construct from the given orientedCurvature function `κ` is twice continuously
differentiable on the given interval `I`. -/
@[fun_prop]
protected theorem _root_.ContDiffOn.initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) :
    ContDiffOn ℝ 2 (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) I := by
  apply contDiffOn_of_continuousOn_differentiableOn_deriv <;> intro m hm
  on_goal 1 =>
    rw [continuousOn_congr (iteratedDerivWithin_of_isOpen (n:=m)
      (f:=(initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)) hI)]
    have hm' : m ≤ 2 := ENat.coe_le_coe.mp hm
    interval_cases m
  on_goal 3 =>
    intro t ht
    rw [continuousWithinAt_congr_of_mem
      (fun y hy ↦  second_deriv_of_initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ hy) ht]
    have hcd : ContDiffWithinAt ℝ 0 (fun t ↦ !₂[-κ t * Real.sin (θ₀+∫ξ in t₀..t, κ ξ),
      κ t * Real.cos (θ₀+∫ξ in t₀..t, κ ξ)]) I t := by
      apply contDiffWithinAt_piLp'
      intro i
      fin_cases i
      all_goals
        simp only [neg_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, contDiffWithinAt_zero ht]
        use I
        constructor
        · exact self_mem_nhdsWithin
        · simp only [Set.inter_self]
          fun_prop (disch := assumption)
    exact hcd.continuousWithinAt
  on_goal 3 =>
    rw [differentiableOn_congr (iteratedDerivWithin_of_isOpen (n:=m)
      (f:=(initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)) hI)]
    have hm' : m < 2 := ENat.coe_lt_coe.mp hm
    interval_cases m
  all_goals
    all_goals
      simp only [iteratedDeriv_zero, iteratedDeriv_one]
      fun_prop (disch := assumption)

/-- The plane curve we construct from the given curvature function `κ` is parametrized by
  arc-length or in other words has unit speed. -/
theorem initialCurve_of_orientedCurvature_has_unit_speed (hI : IsOpen I) (hκ : ContinuousOn κ I)
    (ht₀ : t₀ ∈ I) (ht : t ∈ I) : ‖deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) t‖ = 1 := by
  simp [(HasDerivAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht).deriv,
    EuclideanSpace.norm_eq]

/-- The plane curve we construct from a given function `κ` has orientedCurvature function `κ`. -/
theorem orientedCurvature_initialCurve_of_orientedCurvature (hI : IsOpen I) (hκ : ContinuousOn κ I)
    (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    orientedCurvature (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) t = κ t := by
  unfold orientedCurvature
  rw [(HasDerivAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht).deriv,
    second_deriv_of_initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht, EuclideanSpace.norm_eq]
  simp; ring_nf
  calc
    Real.cos (θ₀ + ∫ (ξ : ℝ) in t₀..t, κ ξ) ^ 2 * κ t +
    κ t * Real.sin (θ₀ + ∫ (ξ : ℝ) in t₀..t, κ ξ) ^ 2 =
    (κ t)*((Real.cos (θ₀ + ∫(ξ : ℝ) in t₀..t, κ ξ))^2
    + (Real.sin (θ₀ + ∫ (ξ : ℝ) in t₀..t, κ ξ))^2) := by ring
    _ = κ t := by simp

/-- The plane curve we construct is at the point `p₀` at time `t₀` (position initial condition). -/
theorem position_initial_condition_initialCurve_of_orientedCurvature (κ : ℝ → ℝ) (t₀ : ℝ) :
    (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) t₀ = p₀ := by
  unfold initialCurve_of_orientedCurvature
  ext i
  simp only [Fin.isValue, intervalIntegral.integral_same, add_zero]
  fin_cases i <;> simp

/-- The plane curve we construct has unit velocity vector at the direction of the angle `θ₀` at time
`t₀` (velocity initial condition). -/
theorem velocity_initial_condition_initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) :
    deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) t₀ = !₂[Real.cos θ₀, Real.sin θ₀] := by
  rw [(HasDerivAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht₀).deriv]; simp

omit hIoC in
lemma deriv_differentiableAt_of_2_contDiffOn_open (hI : IsOpen I) (hγ₁ : ContDiffOn ℝ 2 γ I) (i : ι)
    (ht : t ∈ I) : DifferentiableAt ℝ (fun t ↦  (deriv γ t) i) t := by
  apply (differentiableAt_piLp 2).mp
  have h : I.EqOn (deriv γ) (iteratedDerivWithin 1 γ I) := by
    intro x hx
    rw [← (derivWithin_of_isOpen hI hx)]; simp
  exact ((((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hI.uniqueDiffOn).mp hγ₁).2 1
    (by norm_num)).differentiableAt (hI.mem_nhds ht)).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (hI.mem_nhds ht) h)

lemma left_eq_zero_of_sum_sq_eq_zero {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  have : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  simpa

lemma right_eq_zero_of_sum_sq_eq_zero {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : y = 0 := by
  have : y ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  simpa

omit hIoC in
@[fun_prop]
lemma _root_.DifferentiableAt.deriv_parametrized_curve_of_contDiffOn_open (hI : IsOpen I)
    (ht : t ∈ I) (hγ : ContDiffOn ℝ 2 γ I) : DifferentiableAt ℝ (deriv γ) t :=
  ((hγ.deriv_of_isOpen hI (m:=1) (by norm_num)).differentiableOn_one t ht).differentiableAt
    (hI.mem_nhds ht)

@[fun_prop]
lemma _root_.DifferentiableAt.deriv_initialCurve_of_orientedCurvature (hI : IsOpen I) (ht : t ∈ I)
    (ht₀ : t₀ ∈ I) (hκ : ContinuousOn κ I) :
    DifferentiableAt ℝ (deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)) t := by
  have := ContDiffOn.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀
  fun_prop (disch := assumption)

lemma eq_euclidean_plane_vectors {u v : EuclideanSpace ℝ (Fin 2)}
    (h₀ : u 0 = v 0) (h₁ : u 1 = v 1) : u = v := by
  ext i
  fin_cases i <;> assumption

omit hIoC in
lemma deriv_fun_proj_deriv_eq_proj_deriv_deriv (i : ι) (hI : IsOpen I) (ht : t ∈ I)
    (hγ : ContDiffOn ℝ 2 γ I) : deriv (fun x ↦ (deriv γ x) i) t = (deriv (deriv γ) t) i := by
  change deriv (EuclideanSpace.proj i ∘ deriv γ) t = _
  rw [fderiv_comp_deriv t (by fun_prop) (by fun_prop (disch := assumption)),
      ContinuousLinearMap.fderiv]; simp

/-- This is the uniqueness part of the fundamental theorem of plane curves: given a curvature
function κ and initial conditions (position p₀ at some time t₀ and unit velocity vector at time t₀
at direction given by angle θ₀) the plane curve we construct is the only such twice continuously
differentiable plane curve parametrized by arc-length with curvature κ and satisfying the initial
position and velocity conditions. -/
theorem initialCurve_of_orientedCurvature_is_unique (hI : IsOpen I) (hκ : ContinuousOn κ I)
    (ht₀ : t₀ ∈ I) (hc₁ : ContDiffOn ℝ 2 c I) (hc₂ : ∀ t ∈ I, ‖deriv c t‖ = 1)
    (hc₃ : ∀ t ∈ I, orientedCurvature c t = κ t) (hc₄ : c t₀ = p₀)
    (hc₅ : deriv c t₀ = !₂[Real.cos θ₀, Real.sin θ₀]) :
    I.EqOn c (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) := by
  let α := initialCurve_of_orientedCurvature κ t₀ p₀ θ₀
  have hα₁ := ContDiffOn.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀
  have hα₂ : ∀s ∈ I, ‖deriv α s‖=1 :=
    fun s hs ↦  initialCurve_of_orientedCurvature_has_unit_speed θ₀ p₀ hI hκ ht₀ hs
  have hα₃ : ∀s ∈ I, orientedCurvature α s = κ s :=
    fun s hs ↦  orientedCurvature_initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ hs
  have hα₄ : α t₀ = p₀ := position_initial_condition_initialCurve_of_orientedCurvature θ₀ p₀ κ t₀
  have hα₅ : deriv α t₀ = !₂[Real.cos θ₀, Real.sin θ₀] :=
    velocity_initial_condition_initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀
  have hαFre₁ {s : ℝ} (hs : s ∈ I) : deriv (deriv α) s = κ s • normal α s := by
    rw [← iteratedDeriv_one (f:=α), ← iteratedDeriv_succ,
        second_deriv_eq_orientedCurvature_times_normal hI hα₁ hα₂ hs, hα₃ s hs]
  have hcFre₁ {s : ℝ} (hs : s ∈ I) : deriv (deriv c) s = κ s • normal c s := by
    rw [← iteratedDeriv_one (f:=c), ← iteratedDeriv_succ,
        second_deriv_eq_orientedCurvature_times_normal hI hc₁ hc₂ hs, hc₃ s hs]
  have hαFre₂ {s : ℝ} (hs : s ∈ I) : deriv (normal α) s = - κ s • deriv α s := by
    rw [deriv_normal_eq_minus_orientedCurvature_times_deriv hI hα₁ hα₂ hs, hα₃ s hs]
  have hcFre₂ {s : ℝ} (hs : s ∈ I) : deriv (normal c) s = - κ s • deriv c s := by
    rw [deriv_normal_eq_minus_orientedCurvature_times_deriv hI hc₁ hc₂ hs, hc₃ s hs]
  let f (s : ℝ) := (deriv c s) 0 - (deriv α s) 0
  let g (s : ℝ) := (deriv c s) 1 - (deriv α s) 1
  let h (s : ℝ) := (f s)^2 + (g s)^2
  have hDh {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ h s := by fun_prop (disch := assumption)
  have hdf {s : ℝ} (hs : s ∈ I) : deriv f s = - κ s * g s := by
    simp only [Fin.isValue, neg_mul, f, g]
    rw [deriv_fun_sub (by fun_prop (disch := assumption)) (by fun_prop (disch := assumption))]
    have hddc₀s : deriv (fun t ↦ (deriv c t) 0) s = - κ s * (deriv c s) 1 := by
      simp [deriv_fun_proj_deriv_eq_proj_deriv_deriv 0 hI hs hc₁, PiLp.ext_iff.mp (hcFre₁ hs) 0,
        normal_eq_of_norm_deriv_eq_one (hc₂ s hs)]
    have hddα₀s : deriv (fun t ↦ (deriv α t) 0) s = - κ s * (deriv α s) 1 := by
      simp [deriv_fun_proj_deriv_eq_proj_deriv_deriv 0 hI hs hα₁, α, PiLp.ext_iff.mp (hαFre₁ hs) 0,
        normal_eq_of_norm_deriv_eq_one (hα₂ s hs)]
    rw [hddc₀s, hddα₀s]; ring
  have hdg {s : ℝ} (hs : s ∈ I) : deriv g s = κ s * f s := by
    simp only [Fin.isValue, g, f]
    rw [deriv_fun_sub (by fun_prop (disch := assumption)) (by fun_prop (disch := assumption))]
    have hddc₁s : deriv (fun t ↦ (deriv c t) 1) s = κ s * (deriv c s) 0 := by
      simp [deriv_fun_proj_deriv_eq_proj_deriv_deriv 1 hI hs hc₁, PiLp.ext_iff.mp (hcFre₁ hs) 1,
        normal_eq_of_norm_deriv_eq_one (hc₂ s hs)]
    have hddα₁s : deriv (fun t ↦ (deriv α t) 1) s = κ s * (deriv α s) 0 := by
      simp [deriv_fun_proj_deriv_eq_proj_deriv_deriv 1 hI hs hα₁, α, PiLp.ext_iff.mp (hαFre₁ hs) 1,
        normal_eq_of_norm_deriv_eq_one (hα₂ s hs)]
    rw [hddc₁s, hddα₁s]; ring
  have hdh : Set.EqOn (deriv h) 0 I := by
    intro s hs
    unfold h
    rw [deriv_fun_add (by fun_prop (disch := assumption)) (by fun_prop (disch := assumption)),
      deriv_fun_pow (by fun_prop (disch := assumption)) 2,
      deriv_fun_pow (by fun_prop (disch := assumption)) 2, hdf hs, hdg hs]
    ring_nf; simp
  have hh {s : ℝ} (hs : s ∈ I) : h s = 0 := by
    let ⟨a, ha⟩ := hI.exists_is_const_of_deriv_eq_zero hIoC.isPreconnected
     (fun s hs ↦  (hDh hs).differentiableWithinAt) hdh
    simp [ha s hs, ← ha t₀ ht₀, h, f, g, hc₅, hα₅]
  exact hI.eqOn_of_deriv_eq hIoC.isPreconnected (hc₁.differentiableOn (by decide))
    (hα₁.differentiableOn (by decide)) (fun s hs ↦  eq_euclidean_plane_vectors
    (by linarith [left_eq_zero_of_sum_sq_eq_zero (hh hs), f])
    (by linarith [right_eq_zero_of_sum_sq_eq_zero (hh hs), g])) ht₀ (by simp [hc₄, α, hα₄])

end PlaneCurve
