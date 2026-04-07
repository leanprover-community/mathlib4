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
theorem of plane curves (in a future PR).

## Main results

- `second_deriv_eq_orientedCurvature_times_normal`: the first Frenet equation for plane curves.
- `deriv_normal_eq_minus_orientedCurvature_times_deriv`: the second Frenet equation for plane
  curves.

## References

We mainly followed [zbMATH07533267], especially for the fundamental theorem of plane curves (in a
future PR).
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

/-- See also `orientedCurvature_of_norm_deriv_eq_one` for the special case where `‖deriv c t‖ = 1`. -/
is useful usually for plane curves parametrized by arc-length). -/
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
        exact inner_deriv_normal_eq_zero
      · simp at hinej
        have h : j=0 := by fin_cases j <;> trivial
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, h, real_inner_comm]
        exact inner_deriv_normal_eq_zero
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

end PlaneCurve
