import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Derivative

open Real Polynomial

noncomputable def f : Polynomial ℝ := 3 * X - 4 * X ^ 3

lemma derivf : derivative f = 3 - 12 * X ^ 2 := by
  have eq1 : derivative (3 * X : Polynomial ℝ) = 3 := by simp
  have eq2 : derivative (4 * X ^ 3 : Polynomial ℝ) = 12 * X ^ 2 := by
    have : derivative (X ^ 3) = (3 * X ^ 2 : Polynomial ℝ) := by
      rw [derivative_X_pow]
      simp; rfl
    rw [derivative_mul, derivative_ofNat, zero_mul, zero_add, this,
      Mathlib.Tactic.RingNF.mul_assoc_rev]
    norm_num
  rw [f, derivative_sub, eq1, eq2]


/- Obviously $0<y< 1 / 2=\sin 30^{\circ}$. The function $f(x)=3 x-4 x^3$ is strictly increasing
on $[0,1 / 2)$ because $f^{\prime}(x)=3-12 x^2>0$ for $0 \leq x<1 / 2$.
-/
lemma monof : StrictMonoOn (fun (x : ℝ) => (eval x) f) (Set.Ioo 0 (1 / 2 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 (1 / 2 : ℝ)) (Polynomial.continuousOn_aeval f)
  intro x hx
  rw [interior_Ioo, Set.mem_Ioo] at hx
  rw [Polynomial.deriv_aeval]
  simp only [derivf, coe_aeval_eq_eval, eval_sub, eval_ofNat, eval_mul, eval_pow, eval_X, sub_pos]
  have : x ^ 2 < 1 / 4 := by
    refine (lt_sqrt ?_).mp ?_
    linarith[hx]
    have : √(1 / 4) = 1 / 2 := by
      refine sqrt_eq_cases.mpr ?_
      simp; norm_num
    rw [this]
    exact hx.2
  linarith

lemma calc1 : 1.732 < √3 := (lt_sqrt (by linarith)).mpr (by norm_num)

lemma calc2 : √3 ≤ 1.733 := (sqrt_le_left (by linarith)).mpr (by norm_num)

lemma yin {y}(hy : y = sin (π / 9)) : y ∈ Set.Ioo 0 (1 / 2) := by
  rw [hy]
  constructor
  · refine sin_pos_of_pos_of_le_one ?_ ?_
    simp [pi_pos]
    refine div_le_one_of_le₀ ?_ ?_
    repeat linarith[pi_le_four]
  · rw [← sin_pi_div_six]
    apply strictMonoOn_sin
    repeat {
    constructor
    · ring_nf; simp [pi_pos]; norm_num
    · ring_nf; simp [pi_pos]; norm_num}
    · ring_nf; simp [pi_pos]; norm_num

/-
Problem
13. (HEL 1) Show that $\frac{20}{60}<\sin 20^{\circ}<\frac{21}{60}$.
-/
theorem HEL1 : 20 / 60 < sin (π / 9) ∧ sin (π / 9) < 21 / 60 := by
  set y := sin (π / 9) with hy
  /- 13. From elementary trigonometry we have $\sin 3 t=3 \sin t-4 \sin ^3 t$.
  Hence, if we denote $y=\sin 20^{\circ}$, we have $\sqrt{3} / 2=\sin 60^{\circ}=3 y-4 y^3$.-/
  have calc3: √3 / 2 = 3 * y - 4 * y ^ 3 := by calc
    _ = sin (π / 3) := by rw [sin_pi_div_three]
    _ = _ := by
      rw [← sin_three_mul]
      ring_nf
  have : (eval y) f = 3 * y - 4 * y ^ 3 := by simp [f]
  rw [← this] at calc3

  /- Now the desired inequality
  $\frac{20}{60}=\frac{1}{3}<\sin 20^{\circ}<\frac{21}{60} =\frac{7}{20}$
  follows from $f\left(\frac{1}{3}\right)<\frac{\sqrt{3}}{2}<f\left(\frac{7}{20}\right)$
  which is directly verified. -/

  constructor
  · apply MonotoneOn.reflect_lt (StrictMonoOn.monotoneOn monof) (by norm_num) (yin hy)
    calc
    _ = (eval (1 / 3)) f := by norm_num
    _ ≤ 1.732 / 2 := by simp [f]; norm_num
    _ < _ := by
      rw [← calc3]
      refine (div_lt_div_iff_of_pos_right ?_).mpr calc1
      linarith
  · apply MonotoneOn.reflect_lt (StrictMonoOn.monotoneOn monof) (yin hy) (by norm_num)
    calc
    _ = √3 / 2 := by rw[calc3]
    _ ≤ 1.733 / 2 := by
      refine (div_le_div_iff_of_pos_right ?_).mpr calc2
      linarith
    _ < _ := by simp [f]; norm_num
