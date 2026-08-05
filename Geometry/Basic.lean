/-!
  Euclid's Elements, Book I, Proposition 1
  "On a given finite straight line, to construct an equilateral triangle."

  The very first theorem in the Elements (c. 300 BCE).
  Given any line segment AB, there exists a point C such that
  triangle ABC is equilateral: |AB| = |AC| = |BC|.

  We work in EuclideanSpace ℝ (Fin 2), i.e. ℝ² with the standard
  inner product. The third vertex C is constructed by rotating
  the vector AB by π/3 (60°) about A — the classical compass
  construction.

  Author: Warren Wong
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

namespace Euclid.BookI.Prop1

noncomputable def angle : ℝ := Real.pi / 3

noncomputable def thirdVertex
    (A B : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  let θ := angle
  WithLp.toLp 2
    ![A 0 + (B 0 - A 0) * cos θ - (B 1 - A 1) * sin θ,
     A 1 + (B 0 - A 0) * sin θ + (B 1 - A 1) * cos θ]

theorem equilateral_triangle_exists
    (A B : EuclideanSpace ℝ (Fin 2)) (_h : A ≠ B) :
    ∃ C : EuclideanSpace ℝ (Fin 2),
      dist A C = dist A B ∧ dist B C = dist A B := by
  refine ⟨thirdVertex A B, ?_, ?_⟩
  · -- |AC| = |AB|: C is on the circle of radius |AB| centered at A
    -- C - A is a rotation of B - A by π/3, so |C-A| = |B-A|
    have hAC : dist A (thirdVertex A B) ^ 2 = dist A B ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq,
          Fin.sum_univ_two, Fin.sum_univ_two]
      rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
      rw [sq_abs, sq_abs, sq_abs, sq_abs]
      simp only [thirdVertex, angle, PiLp.toLp_apply,
                 Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [cos_pi_div_three, sin_pi_div_three]
      have h_sqrt3 : (√3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
      nlinarith [h_sqrt3]
    exact (sq_eq_sq₀ (dist_nonneg) (dist_nonneg)).mp hAC
  · -- |BC| = |AB|: by law of cosines with angle π/3
    -- C - B = R(B-A) - (B-A), |C-B|² = 2|B-A|²(1-cos(π/3)) = |B-A|²
    have hBC : dist B (thirdVertex A B) ^ 2 = dist A B ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq,
          Fin.sum_univ_two, Fin.sum_univ_two]
      rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
      rw [sq_abs, sq_abs, sq_abs, sq_abs]
      simp only [thirdVertex, angle, PiLp.toLp_apply,
                 Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [cos_pi_div_three, sin_pi_div_three]
      have h_sqrt3 : (√3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
      nlinarith [h_sqrt3]
    exact (sq_eq_sq₀ (dist_nonneg) (dist_nonneg)).mp hBC

end Euclid.BookI.Prop1
