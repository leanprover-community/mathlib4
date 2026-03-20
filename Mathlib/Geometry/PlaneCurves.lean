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

section

variable (c : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ)

/-- Curvature for plane curves. This is usually called just the curvature function of a plane curve
in most elementary differential geometry texts, but because this definition is slightly different
from the general definition of the curvature function of a general parametrized curve (which is
always non-negative and only expresses magnitude as opposed to this definition which can also be
negative and expresses also direction) we call this the oriented curvature, this is also the name
given in the Wikipedia article about curvature in the section about plane curves. This definition is
meaningful only for regular plane curves which are twice continuously differentiable on an
interval I. -/
def orientedCurvature : ℝ :=
  let c' := deriv c t
  let c'' := iteratedDeriv 2 c t
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![c' 0, c' 1; c'' 0, c'' 1]
  M.det / (‖deriv c t‖^3)

/-- Normal vector at a point of a plane curve. This definition is only meaningful when c is
differentiable at t, and it's supposed to be used for plane curves parametrized by arc-length. -/
def normal : EuclideanSpace ℝ (Fin 2) :=
  let c' := deriv c t
  !₂[-(c' 1), c' 0]

/-- The normal vector at point of a plane curve is orthogonal to the velocity vector at the point.
-/
theorem inner_of_velocity_normal_eq_zero : inner ℝ (deriv c t) (normal c t) = 0 := by
  simp [normal, inner]; ring

end

variable {I : Set ℝ} {c : ℝ → EuclideanSpace ℝ (Fin 2)} {t : ℝ}

/-- The normal vector at point of a plane curve parametrized by arc-length (i.e., with unit-speed)
has length 1 (is a unit vector). -/
theorem norm_normal_eq_one_of_unit_speed (hc : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    ‖normal c t‖ = 1 := by
  simp only [norm, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, normal, Fin.isValue,
             ENNReal.toReal_ofNat,Real.rpow_ofNat, sq_abs, Fin.sum_univ_two, Matrix.cons_val_zero,
             even_two, Even.neg_pow, Matrix.cons_val_one,Matrix.cons_val_fin_one, one_div]
  rw [add_comm, ← hc t ht]
  simp [norm]

/-- For every plane curve parametrized by arc-length, the velocity vector and the normal vector at
each point form an orthonormal basis of the plane, which is sometimes called the moving frame of the
curve or the Frenet frame, which we call `frameAt`. -/
def frameAt (hc : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  let B := ![deriv c t, normal c t]
  have hBon : Orthonormal ℝ B := by
    constructor
    · intro i
      fin_cases i
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue]
        exact hc t ht
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue]
        exact norm_normal_eq_one_of_unit_speed hc ht
    · intro i j hinej
      fin_cases i
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ne_eq] at hinej
        have h : j=1 := Fin.eq_one_of_ne_zero j fun a ↦ hinej (id (Eq.symm a))
        simp only [h, Fin.isValue]; exact inner_of_velocity_normal_eq_zero c t
      · simp at hinej
        have h : j=0 := by fin_cases j <;> trivial
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, h]
        rw [real_inner_comm]; exact inner_of_velocity_normal_eq_zero c t
  have hBsp : ⊤ ≤ Submodule.span ℝ (Set.range B) := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, top_le_iff]
    apply hBon.linearIndependent.span_eq_top_of_card_eq_finrank
    simp
  OrthonormalBasis.mk (v:=B) (hon:=hBon) (hsp:=hBsp)

set_option backward.isDefEq.respectTransparency false in
/-- A simpler formula for the curvature of a plane curve parametrized by arc-length, or in other
words with unit speed. -/
theorem orientedCurvature_of_unit_speed_curve (hc : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    orientedCurvature c t = inner ℝ (iteratedDeriv 2 c t) (normal c t) := by
  unfold orientedCurvature normal
  rw [hc t ht]
  simp only [Fin.isValue, Matrix.det_fin_two_of, one_pow, div_one]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Fin.isValue, star_trivial, Matrix.cons_dotProduct, neg_mul,
             Matrix.dotProduct_of_isEmpty, add_zero]
  exact sub_eq_neg_add ((deriv c t).ofLp 0 * (iteratedDeriv 2 c t).ofLp 1)
    ((deriv c t).ofLp 1 * (iteratedDeriv 2 c t).ofLp 0)

universe u

variable {ι : Type u} [Fintype ι] {γ : ℝ → EuclideanSpace ℝ ι}

/-- Auxiliary lemma: If `γ` is a twice continuously differentiable parametrized curve on an interval
`I`, then the velocity vector `deriv γ` has a derivative at every point of `I`. -/
lemma velocity_hasDerivAt_aux (hI : IsOpen I) (hγ : ContDiffOn ℝ 2 γ I)
    (ht : t ∈ I) : HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t := by
  have hd : ContDiffOn ℝ 1 (deriv γ) I := hγ.deriv_of_isOpen hI (by norm_num)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (hd.differentiableOn (by norm_num)).hasDerivAt (hI.mem_nhds ht)

lemma inners_sum_eq_zero_of_const_inner_on_open {α β : ℝ → EuclideanSpace ℝ ι} (hI : IsOpen I)
    {s : ℝ} (ht : t ∈ I) {α' β' : EuclideanSpace ℝ ι} (hdα : HasDerivAt α α' t)
    (hdβ : HasDerivAt β β' t) (hci : Set.EqOn (fun t ↦ inner ℝ (α t) (β t)) (fun _ ↦ s) I) :
    inner ℝ (α t) β' + inner ℝ α' (β t) = 0 := by
  let f := fun t ↦  inner ℝ (α t) (β t)
  symm
  calc
    (0 : ℝ) = deriv f t := by
      rw [← derivWithin_of_isOpen hI ht, derivWithin_congr hci (hci ht)]
      simp
    _ = inner ℝ (α t) β' + inner ℝ α' (β t) := by
      unfold f
      apply (HasDerivAt.inner ℝ hdα hdβ).deriv

/-- Given a continuously differentiable parametrized curve whose position has the same magnitude at
all time, i.e, at constant radius distance from the origin (the curve `γ` is contained in a sphere
of radius `r` from the origin), then the velocity vector is always perpendicular to the position
vector of the curve at every point (in other words their dot product is zero). -/
theorem inner_of_deriv_curve_eq_zero_of_const_magnitude_curve (hI : IsOpen I)
    (hγ₁ : ContDiffOn ℝ 1 γ I) {r : ℝ} (hγ₂ : ∀ t ∈ I, ‖γ t‖ = r) (ht : t ∈ I) :
    inner ℝ (deriv γ t) (γ t) = 0 := by
  have h : Set.EqOn (fun x ↦  inner ℝ (γ x) (γ x)) (fun x ↦  r^2) I := by
    intro x hx
    simp [hγ₂ x hx]
  have hd : HasDerivAt γ (deriv γ t) t :=
    (hγ₁.contDiffAt (hI.mem_nhds ht)).differentiableAt_one.hasDerivAt
  symm
  calc
    (0 : ℝ) = 0 / 2 := by norm_num
    _ = inner ℝ (deriv γ t) (γ t) := by
            rw [← inners_sum_eq_zero_of_const_inner_on_open hI ht hd hd h,
                real_inner_comm (deriv γ t)]; ring

/-- For any twice continuously differentiable parametrized curve with constant speed, at any given
point the velocity vector is perpendicular to the acceleration vector. -/
theorem inner_of_accel_velocity_of_const_speed_eq_zero (hI : IsOpen I) (hγ₁ : ContDiffOn ℝ 2 γ I)
    {r : ℝ} (hγ₂ : ∀ t ∈ I, ‖deriv γ t‖ = r) (ht : t ∈ I) :
    inner ℝ (iteratedDeriv 2 γ t) (deriv γ t) = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h : ContDiffOn ℝ (1+1) γ I := by assumption
  have h' := ((contDiffOn_succ_iff_deriv_of_isOpen hI).mp h).2.2
  exact inner_of_deriv_curve_eq_zero_of_const_magnitude_curve hI h' hγ₂ ht

/-- The first Frenet equation for plane curves: For any twice continously differentiable plane curve
parametrized by arc-length (i.e., with unit speed), the second derivative, i.e. acceleration vector
is equal to the curvature times the normal vector. -/
theorem second_deriv_eq_orientedCurvature_times_normal (hI : IsOpen I) (hc₁ : ContDiffOn ℝ 2 c I)
    (hc₂ : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    iteratedDeriv 2 c t = (orientedCurvature c t)•(normal c t) := by
  rw [orientedCurvature_of_unit_speed_curve hc₂ ht]
  nth_rewrite 1 [← (frameAt hc₂ ht).sum_repr' (iteratedDeriv 2 c t)]
  simp only [frameAt, Nat.succ_eq_add_one, Nat.reduceAdd, OrthonormalBasis.coe_mk, Fin.sum_univ_two,
             Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [real_inner_comm (iteratedDeriv 2 c t), real_inner_comm (iteratedDeriv 2 c t),
      inner_of_accel_velocity_of_const_speed_eq_zero hI hc₁ hc₂ ht]
  simp

/-- Auxiliary lemma: If `c` is a twice continuously differentiable plane curve on an interval `I`,
then the normal has a derivative at every point of `I`. -/
lemma normal_hasDerivAt_aux (hI : IsOpen I) (hc : ContDiffOn ℝ 2 c I) (ht : t ∈ I) :
    HasDerivAt (normal c) (deriv (normal c) t) t := by
  have hd : ContDiffOn ℝ 1 (deriv c) I := hc.deriv_of_isOpen hI (by norm_num)
  have hD : DifferentiableOn ℝ (deriv c) I := hd.differentiableOn (by norm_num)
  unfold normal
  simp only [Fin.isValue, hasDerivAt_deriv_iff]
  have h : DifferentiableOn ℝ (fun t ↦ !₂[-(deriv c t) 1, (deriv c t) 0]) I := by
    rw [differentiableOn_piLp] at *
    intro i
    fin_cases i <;> simp [hD]
  exact h.differentiableAt (hI.mem_nhds ht)

@[fun_prop]
lemma _root_.ContDiffOn.normal_of_twice_contDiffOn_curve (hI : IsOpen I) (hc : ContDiffOn ℝ 2 c I) :
    ContDiffOn ℝ 1 (normal c) I := by
  have hd : ContDiffOn ℝ 1 (deriv c) I := hc.deriv_of_isOpen hI (by norm_num)
  unfold normal
  rw [contDiffOn_piLp] at *
  intro i
  fin_cases i
  · simp [ContDiffOn.neg, hd 1]
  · simp [hd 0]

/-- For any twice continuously differentiable plane curve with constant speed, at any given point
the normal vector is perpendicular to the derivative of the normal vector. -/
theorem inner_of_deriv_normal_normal_of_unit_speed_eq_zero (hI : IsOpen I)
    (hc₁ : ContDiffOn ℝ 2 c I) (hc₂ : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    inner ℝ  (deriv (normal c) t) (normal c t) = 0 :=
  inner_of_deriv_curve_eq_zero_of_const_magnitude_curve hI (by fun_prop (disch := assumption))
    (fun _ ht ↦  norm_normal_eq_one_of_unit_speed hc₂ ht) ht

/-- The second Frenet equation for plane curves: For any twice continously differentiable plane
curve parametrized by arc-length (i.e., with unit speed), the derivative of the normal vector is
equal to minus the curvature times the velocity vector (first derivative). -/
theorem deriv_normal_eq_minus_orientedCurvature_times_deriv (hI : IsOpen I)
    (hc₁ : ContDiffOn ℝ 2 c I) (hc₂ : ∀ t ∈ I, ‖deriv c t‖ = 1) (ht : t ∈ I) :
    deriv (normal c) t = -(orientedCurvature c t)•(deriv c t) := by
  rw [← (frameAt hc₂ ht).sum_repr' (deriv (normal c) t)]
  simp only [frameAt, Nat.succ_eq_add_one, Nat.reduceAdd, OrthonormalBasis.coe_mk,
             Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.cons_val_fin_one, neg_smul]
  rw [real_inner_comm (deriv (normal c) t) (normal c t),
      inner_of_deriv_normal_normal_of_unit_speed_eq_zero hI hc₁ hc₂ ht]; simp
  have hdn : HasDerivAt (normal c) (deriv (normal c) t) t := normal_hasDerivAt_aux hI hc₁ ht
  have hddc : HasDerivAt (deriv c) (iteratedDeriv 2 c t) t := velocity_hasDerivAt_aux hI hc₁ ht
  have h : inner ℝ (deriv c t) (deriv (normal c) t) = - orientedCurvature c t := by
    have h' : inner ℝ (deriv c t) (deriv (normal c) t) + orientedCurvature c t = 0 := by
      symm
      have hci : Set.EqOn (fun x ↦ inner ℝ (normal c x) (deriv c x)) (fun x ↦ 0) I := by
        intro x hx
        simp only
        rw [real_inner_comm, inner_of_velocity_normal_eq_zero c x]
      calc
        (0 : ℝ) = (orientedCurvature c t)•(inner ℝ (normal c t) (normal c t))
                  + inner ℝ (deriv (normal c) t) (deriv c t) := by
          rw [← inners_sum_eq_zero_of_const_inner_on_open hI ht hdn hddc hci,
              second_deriv_eq_orientedCurvature_times_normal hI hc₁ hc₂ ht,
              real_inner_comm (orientedCurvature c t • normal c t),
              inner_smul_left_eq_smul (normal c t) (normal c t)]
        _ = inner ℝ (deriv c t) (deriv (normal c) t) + (orientedCurvature c t) := by
          simp only [inner_self_eq_norm_sq_to_K, norm_normal_eq_one_of_unit_speed hc₂ ht,
                     RCLike.ofReal_real_eq_id, id_eq, one_pow, smul_eq_mul, mul_one]
          rw [add_comm, real_inner_comm]
    linarith [h']
  simp [h]

/-- This is the plane curve we construct in the fundamental theorem of plane curves, given curvature
function κ, initial position p₀ at time t₀ and initial velocity vector condition given by an angle
θ₀ (this angle is a choice of direction for the unit velocity vector at time t₀). This definition is
only meaningful when κ is continuous on some given interval. -/
def initialCurve_of_orientedCurvature (κ : ℝ → ℝ) (t₀ : ℝ) (p₀ : EuclideanSpace ℝ (Fin 2))
    (θ₀ : ℝ) : ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun t ↦  !₂[p₀ 0 + ∫τ in t₀..t, Real.cos (θ₀ + ∫ξ in t₀..τ, κ ξ),
              p₀ 1 + ∫τ in t₀..t, Real.sin (θ₀ + ∫ξ in t₀..τ, κ ξ)]

variable {κ : ℝ → ℝ} {t₀ : ℝ} (θ₀ : ℝ) (p₀ : EuclideanSpace ℝ (Fin 2)) {t : ℝ}

section

variable [hIoC : I.OrdConnected]

/-- Auxiliary lemma which says that the angle function (fun x ↦ θ₀ + ∫ξ in t₀..x, κ ξ) is continuous
on the interval I. -/
@[fun_prop]
lemma continuousOn_angle_fun_aux (hI : IsOpen I) (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) :
    ContinuousOn (fun x ↦ θ₀ + ∫ (ξ : ℝ) in t₀..x, κ ξ) I := by
  have h₁ : ContinuousOn (fun x ↦ θ₀) I := continuousOn_const
  have h₂ : ContinuousOn (fun x ↦ ∫ (ξ : ℝ) in t₀..x, κ ξ) I := by
    -- Since I is open, we can find an ε  > 0 such that (t₀ - ε, t₀ + ε) ⊆  I.
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, Metric.ball t₀ ε ⊆ I := Metric.isOpen_iff.mp hI t₀ ht₀
    intro x hx
    have hd : HasDerivAt (fun x => ∫ ξ in t₀..x, κ ξ) (κ x) x := by
      apply_rules [intervalIntegral.integral_hasDerivAt_right]
      · apply_rules [ContinuousOn.intervalIntegrable, hκ]
        exact hκ.mono (hIoC.uIcc_subset ht₀ hx)
      · exact ContinuousOn.stronglyMeasurableAtFilter hI hκ x hx
      · exact hκ.continuousAt (hI.mem_nhds hx)
    exact hd.continuousAt.continuousWithinAt
  exact h₁.add h₂

protected lemma _root_.HasDerivAt.initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivAt (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)
    !₂[Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ), Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ)] t := by
  apply HasDerivWithinAt.hasDerivAt (s := I)
  · rw [hasDerivWithinAt_pi_euclidean]
    unfold initialCurve_of_orientedCurvature
    have h := continuousOn_angle_fun_aux θ₀ hI hκ ht₀
    intro i
    fin_cases i
    all_goals
      simp only [Fin.zero_eta,Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
                 hasDerivWithinAt_const_add_iff]
      exact intervalIntegral.hasDerivWithinAt_of_continuousOn_interval (by fun_prop) ht₀ ht
  · exact hI.mem_nhds ht

lemma _root_.HasDerivAt.deriv_initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivAt (deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀))
    !₂[-(κ t)*Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ), (κ t)*Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ)] t := by
  have h₀ : HasDerivWithinAt (fun x ↦  θ₀ + ∫ξ in t₀..x, κ ξ) (κ t) I t := by
    have hyp₁ : HasDerivWithinAt (fun x ↦ θ₀) 0 I t := by apply hasDerivWithinAt_const
    have hyp₂ :=  intervalIntegral.hasDerivWithinAt_of_continuousOn_interval hκ ht₀ ht
    have hyp₃ := hyp₁.add hyp₂
    have help : (fun x↦ θ₀)+(fun t↦ ∫τ in t₀..t, κ τ) = fun x↦ θ₀+∫ξ in t₀..x, κ ξ := by rfl
    rw [help, zero_add] at hyp₃
    exact hyp₃
  have h : I.EqOn (deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀))
           (fun x ↦  !₂[Real.cos (θ₀+∫ξ in t₀..x, κ ξ), Real.sin (θ₀+∫ξ in t₀..x, κ ξ)]) :=
    fun x hx ↦  (HasDerivAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ hx).deriv
  have h' : HasDerivWithinAt (fun x ↦ !₂[Real.cos (θ₀ + ∫ ξ in t₀..x, κ ξ),
                                         Real.sin (θ₀ + ∫ ξ in t₀..x, κ ξ)])
            !₂[-κ t *Real.sin (θ₀+∫ξ in t₀..t, κ ξ),κ t *Real.cos (θ₀+∫ξ in t₀..t, κ ξ)] I t := by
    rw [hasDerivWithinAt_pi_euclidean]
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, neg_mul]
      have h₁ : HasDerivAt Real.cos (-Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ))
        ((fun τ ↦  θ₀ + ∫ξ in t₀..τ, κ ξ) t) := by simp [Real.hasDerivAt_cos]
      have hint := h₁.comp_hasDerivWithinAt t h₀
      have help : (fun t↦ Real.cos (θ₀+∫ξ in t₀..t, κ ξ)) =
                  Real.cos ∘ (fun x↦ θ₀+∫ξ in t₀..x, κ ξ) := by rfl
      rw [help]
      have help' : -Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ) * κ t =
                   -(κ t * Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ)) := by ring
      rw [help'] at hint
      exact hint
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_mul]
      have h₁ : HasDerivAt Real.sin (Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ))
        ((fun τ ↦  θ₀ + ∫ξ in t₀..τ, κ ξ) t) := by simp [Real.hasDerivAt_sin]
      have hint := h₁.comp_hasDerivWithinAt t h₀
      have help : (fun t↦ Real.sin (θ₀+∫ξ in t₀..t, κ ξ)) =
                  Real.sin ∘ (fun x↦ θ₀+∫ξ in t₀..x, κ ξ) := by rfl
      rw [help]
      have help' : Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ) * κ t =
                   κ t * Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ) := by ring
      rw [help'] at hint
      exact hint
  apply HasDerivWithinAt.hasDerivAt
  · exact h'.congr h (h ht)
  · exact hI.mem_nhds ht

lemma second_deriv_of_initialCurve_of_orientedCurvature (hI : IsOpen I) (hκ : ContinuousOn κ I)
    (ht₀ : t₀ ∈ I) (ht : t ∈ I) : iteratedDeriv 2 (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) t =
    !₂[-(κ t)*Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ), (κ t)*Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ)] := by
  rw [iteratedDeriv_succ, iteratedDeriv_one,
      (HasDerivAt.deriv_initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht).deriv]

@[fun_prop]
lemma _root_.ContinuousOn.initialCurve_of_orientedCurvature (hI : IsOpen I) (hκ : ContinuousOn κ I)
    (ht₀ : t₀ ∈ I) : ContinuousOn (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) I := by
  apply HasDerivAt.continuousOn
  exact fun _ h ↦  HasDerivAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ h

@[fun_prop]
lemma _root_.ContinuousOn.deriv_initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) :
    ContinuousOn (deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)) I := by
  apply HasDerivAt.continuousOn
  exact fun _ h ↦  HasDerivAt.deriv_initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ h

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

set_option backward.isDefEq.respectTransparency false in
/-- The plane curve we construct from the given orientedCurvature function κ is twice continuously
differentiable on the given interval I. -/
@[fun_prop]
protected theorem _root_.ContDiffOn.initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) :
    ContDiffOn ℝ 2 (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) I := by
  apply contDiffOn_of_continuousOn_differentiableOn_deriv
  · intro m hm
    have help := iteratedDerivWithin_of_isOpen (n:=m)
                 (f:=(initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)) hI
    rw [continuousOn_congr help]
    have hm' : m ≤ 2 := by simp_all
    interval_cases m
    pick_goal 3
    · intro t ht
      have h' : ∀ y ∈ I, (iteratedDeriv 2 (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)) y
                       = (fun t ↦ !₂[-(κ t)*Real.sin (θ₀ + ∫ξ in t₀..t, κ ξ),
                         (κ t)*Real.cos (θ₀ + ∫ξ in t₀..t, κ ξ)]) y :=
        fun y hy ↦  second_deriv_of_initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ hy
      rw [continuousWithinAt_congr_of_mem h' ht]
      have hcd : ContDiffWithinAt ℝ 0 (fun t ↦ !₂[-κ t * Real.sin (θ₀+∫ξ in t₀..t, κ ξ),
        κ t * Real.cos (θ₀+∫ξ in t₀..t, κ ξ)]) I t := by
        apply contDiffWithinAt_piLp'
        intro i
        fin_cases i
        all_goals
          simp only [neg_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
                       Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [contDiffWithinAt_zero ht]
          use I
          constructor
          · exact self_mem_nhdsWithin
          · simp only [Set.inter_self]
            fun_prop (disch := assumption)
      exact hcd.continuousWithinAt
    all_goals
      simp only [iteratedDeriv_zero, iteratedDeriv_one]
      fun_prop (disch := assumption)
  · intro m hm
    have help := iteratedDerivWithin_of_isOpen (n:=m)
                 (f:=(initialCurve_of_orientedCurvature κ t₀ p₀ θ₀)) hI
    rw [differentiableOn_congr help]
    have hm' : m < 2 := by simp_all
    interval_cases m
    all_goals
      simp only [iteratedDeriv_zero, iteratedDeriv_one]
      fun_prop (disch := assumption)

variable {t : ℝ}

/-- The plane curve we construct from the given curvature function κ is parametrized by
  arc-length or in other words has unit speed. -/
theorem initialCurve_of_orientedCurvature_has_unit_speed (hI : IsOpen I) (hκ : ContinuousOn κ I)
    (ht₀ : t₀ ∈ I) (ht : t ∈ I) : ‖deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) t‖ = 1 := by
  rw [(HasDerivAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht).deriv,
      EuclideanSpace.norm_eq]
  simp

/-- The plane curve we construct from a given function κ has orientedCurvature function κ. -/
theorem orientedCurvature_initialCurve_of_orientedCurvature (hI : IsOpen I) (hκ : ContinuousOn κ I)
    (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    orientedCurvature (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) t = κ t := by
  unfold orientedCurvature
  rw [(HasDerivAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht).deriv,
      second_deriv_of_initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht, EuclideanSpace.norm_eq]
  simp
  ring_nf
  calc
    Real.cos (θ₀ + ∫ (ξ : ℝ) in t₀..t, κ ξ) ^ 2 * κ t +
    κ t * Real.sin (θ₀ + ∫ (ξ : ℝ) in t₀..t, κ ξ) ^ 2 =
    (κ t)*((Real.cos (θ₀ + ∫(ξ : ℝ) in t₀..t, κ ξ))^2
    + (Real.sin (θ₀ + ∫ (ξ : ℝ) in t₀..t, κ ξ))^2) := by ring
    _ = κ t := by simp

/-- The plane curve we construct is at the point p₀ at time t₀ (position initial condition). -/
theorem position_initial_condition_initialCurve_of_orientedCurvature (κ : ℝ → ℝ) (t₀ : ℝ) :
    (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) t₀ = p₀ := by
  unfold initialCurve_of_orientedCurvature
  ext i
  simp only [Fin.isValue, intervalIntegral.integral_same, add_zero]
  fin_cases i <;> simp

/-- The plane curve we construct has unit velocity vector at the direction of the angle θ₀ at time
t₀ (velocity initial condition). -/
theorem velocity_initial_condition_initialCurve_of_orientedCurvature (hI : IsOpen I)
    (hκ : ContinuousOn κ I) (ht₀ : t₀ ∈ I) :
    deriv (initialCurve_of_orientedCurvature κ t₀ p₀ θ₀) t₀ = !₂[Real.cos θ₀, Real.sin θ₀] := by
  rw [(HasDerivAt.initialCurve_of_orientedCurvature θ₀ p₀ hI hκ ht₀ ht₀).deriv]
  simp

omit hIoC in
lemma deriv_differentiableAt_of_2_contDiffOn_open (hI : IsOpen I) (hγ₁ : ContDiffOn ℝ 2 γ I) (i : ι)
    (ht : t ∈ I) : DifferentiableAt ℝ (fun t ↦  (deriv γ t) i) t := by
  apply (differentiableAt_piLp 2).mp
  have h : I.EqOn (deriv γ) (iteratedDerivWithin 1 γ I) := by
    intro x hx
    rw [← (derivWithin_of_isOpen hI hx)]
    simp
  apply ((((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hI.uniqueDiffOn).mp hγ₁).2
          1 (by norm_num)).differentiableAt (hI.mem_nhds ht)).congr_of_eventuallyEq
  exact Filter.eventuallyEq_of_mem (hI.mem_nhds ht) h

lemma left_eq_zero_of_sum_sq_eq_zero {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  have : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  simpa

lemma right_eq_zero_of_sum_sq_eq_zero {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : y = 0 := by
  have : y ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  simpa

set_option backward.isDefEq.respectTransparency false in
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
  have hDdc {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ (deriv c) s :=
    have help := (hc₁.deriv_of_isOpen hI (m:=1) (by norm_num)).differentiableOn_one
    (help s hs).differentiableAt (hI.mem_nhds hs)
  have hDdα {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ (deriv α) s :=
    have help := (hα₁.deriv_of_isOpen hI (m:=1) (by norm_num)).differentiableOn_one
    (help s hs).differentiableAt (hI.mem_nhds hs)
  have hDdc₀ {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ (fun t ↦  (deriv c t) 0) s := by
    fun_prop (disch := assumption)
  have hDdα₀ {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ (fun t ↦  (deriv α t) 0) s := by
    fun_prop (disch := assumption)
  have hDdc₁ {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ (fun t ↦  (deriv c t) 1) s := by
    fun_prop (disch := assumption)
  have hDdα₁ {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ (fun t ↦  (deriv α t) 1) s := by
    fun_prop (disch := assumption)
  have hDf {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ f s := by simp [f, hDdc₀ hs, hDdα₀ hs]
  have hDff {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ (fun t ↦ (f t)^2) s := by simp [hDf hs]
  have hDg {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ g s := by simp [g, hDdc₁ hs, hDdα₁ hs]
  have hDgg {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ (fun t ↦ (g t)^2) s := by simp [hDg hs]
  have hDh {s : ℝ} (hs : s ∈ I) : DifferentiableAt ℝ h s := by simp [h, hDff hs, hDgg hs]
  have hDOnh : DifferentiableOn ℝ h I := fun s hs ↦  (hDh hs).differentiableWithinAt
  have hdf : ∀s ∈ I, deriv f s = - κ s * g s := by
    intro s hs
    simp only [Fin.isValue, neg_mul, f, g]
    rw [deriv_fun_sub (hDdc₀ hs) (hDdα₀ hs)]
    have hddc₀s : deriv (fun t ↦ (deriv c t) 0) s = - κ s * (deriv c s) 1 := by
      have help₁ : deriv (fun t ↦ (deriv c t) 0) s = (deriv (deriv c) s) 0 := by
        change deriv (EuclideanSpace.proj 0 ∘ deriv c) s = _
        have hproj : DifferentiableAt ℝ (EuclideanSpace.proj 0) (deriv c s) := by fun_prop
        rw [fderiv_comp_deriv s hproj (hDdc hs), ContinuousLinearMap.fderiv]
        simp
      have help₂ := PiLp.ext_iff.mp (hcFre₁ hs) 0
      simp [help₁, help₂, normal]
    have hddα₀s : deriv (fun t ↦ (deriv α t) 0) s = - κ s * (deriv α s) 1 := by
      have help₁ : deriv (fun t ↦ (deriv α t) 0) s = (deriv (deriv α) s) 0 := by
        change deriv (EuclideanSpace.proj 0 ∘ deriv α) s = _
        have hproj : DifferentiableAt ℝ (EuclideanSpace.proj 0) (deriv α s) := by fun_prop
        rw [fderiv_comp_deriv s hproj (hDdα hs), ContinuousLinearMap.fderiv]
        simp
      have help₂ := PiLp.ext_iff.mp (hαFre₁ hs) 0
      simp [help₁, help₂, normal]
    rw [hddc₀s, hddα₀s]
    ring
  have hdg : ∀s ∈ I, deriv g s = κ s * f s := by
    intro s hs
    simp only [Fin.isValue, g, f]
    rw [deriv_fun_sub (hDdc₁ hs) (hDdα₁ hs)]
    have hddc₁s : deriv (fun t ↦ (deriv c t) 1) s = κ s * (deriv c s) 0 := by
      have help : deriv (fun t ↦ (deriv c t) 1) s = (deriv (deriv c) s) 1 := by
        change deriv (EuclideanSpace.proj 1 ∘ deriv c) s = _
        rw [fderiv_comp_deriv s (by fun_prop) (hDdc hs), ContinuousLinearMap.fderiv]
        simp
      simp [help, PiLp.ext_iff.mp (hcFre₁ hs) 1, normal]
    have hddα₁s : deriv (fun t ↦ (deriv α t) 1) s = κ s * (deriv α s) 0 := by
      have help : deriv (fun t ↦ (deriv α t) 1) s = (deriv (deriv α) s) 1 := by
        change deriv (EuclideanSpace.proj 1 ∘ deriv α) s = _
        rw [fderiv_comp_deriv s (by fun_prop) (hDdα hs), ContinuousLinearMap.fderiv]
        simp
      simp [help, PiLp.ext_iff.mp (hαFre₁ hs) 1, normal]
    rw [hddc₁s, hddα₁s]
    ring
  have hdh : Set.EqOn (deriv h) 0 I := by
    intro s hs
    unfold h
    calc
       deriv (fun s ↦ f s ^ 2 + g s ^ 2) s = 2*((f s)*(deriv f s)+(g s)*(deriv g s)) := by
         rw [deriv_fun_add (hDff hs) (hDgg hs), deriv_fun_pow (hDf hs) 2, deriv_fun_pow (hDg hs) 2]
         ring
       _ = 2*((f s)*(- κ s * g s)+(g s)*(κ s * f s)) := by rw [hdf s hs, hdg s hs]
       _ = 0 := by ring
  have hh : ∀s ∈ I, h s = 0 := by
    let ⟨a, ha⟩ := hI.exists_is_const_of_deriv_eq_zero hIoC.isPreconnected hDOnh hdh
    intro s hs
    rw [ha s hs, ← ha t₀ ht₀]
    simp [h, f, g, hc₅, hα₅]
  have heqd₀ : ∀s ∈ I, (deriv c s) 0 = (deriv α s) 0 := by
    intro s hs
    have help := left_eq_zero_of_sum_sq_eq_zero (hh s hs)
    simp [f] at help
    linarith
  have heqd₁ : ∀s ∈ I, (deriv c s) 1 = (deriv α s) 1 := by
    intro s hs
    have help := right_eq_zero_of_sum_sq_eq_zero (hh s hs)
    simp [g] at help
    linarith
  have heqd : ∀s ∈ I, deriv c s = deriv α s := by
    intro s hs
    ext i
    fin_cases i
    · simp [heqd₀ s hs]
    · simp [heqd₁ s hs]
  exact hI.eqOn_of_deriv_eq hIoC.isPreconnected (hc₁.differentiableOn (by norm_num))
    (hα₁.differentiableOn (by norm_num)) heqd ht₀ (by simp [hc₄, α, hα₄])

end

end PlaneCurve
