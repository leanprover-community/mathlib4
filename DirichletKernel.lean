/-
Copyright (c) 2025 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
import Mathlib

/-!
# Dirichlet kernel

This file contains the definitions of Dirichlet kernel.

## TODO : $S_n(f)(x) = (D_n * f)(x)$

-/

@[expose] public section

open Real

section

theorem sum_cos_arith_progression1 (n : ℕ) (x a : ℝ) (hx : sin (x / 2) ≠ 0) :
    ∑ k ∈ Finset.range n, cos ((k : ℝ) * x + a)
    = sin (n * x / 2) / sin (x / 2) * cos ((n - 1 : ℝ) * x / 2 + a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Finset.sum_range_succ, ih, field]
    have : 2 * sin ((n + 1) * x / 2) * cos (n * x / 2 + a)
         - 2 * sin (n * x / 2) * cos ((n - 1) * x / 2 + a)
         = 2 * sin (x / 2) * cos (n * x + a) := by
      rw [two_mul_sin_mul_cos, two_mul_sin_mul_cos, two_mul_sin_mul_cos]
      ring_nf
      rw [sub_eq_add_neg, ← sin_neg]
      ring_nf
    linarith

theorem sum_sin_arith_progression2 (n : ℕ) (x a : ℝ) (hx : sin (x / 2) ≠ 0) :
    ∑ k ∈ Finset.range n, sin ((k : ℝ) * x + a)
    = sin (n * x / 2) / sin (x / 2) * sin ((n - 1 : ℝ) * x / 2 + a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Finset.sum_range_succ, ih, field]
    have : 2 * sin (↑n * x / 2) * sin ((↑n - 1) * x / 2 + a)
         + 2 * sin (x / 2) * sin (↑n * x + a)
         = 2 * sin ((↑n + 1) * x / 2) * sin (↑n * x / 2 + a) := by
      rw [two_mul_sin_mul_sin, two_mul_sin_mul_sin, two_mul_sin_mul_sin]
      nth_rw 3 [← cos_neg]
      ring_nf
    linarith

end



noncomputable section

/-- Real-valued Dirichlet kernel `D_N`. Away from the points `x = 2 * k * π` it agrees with the
closed form `sin ((N + 1/2) * x) / sin (x / 2)`, and it is defined to be `2 * N + 1` at those
points to match the limiting value. -/
def dirichletKernel (N : ℕ) (x : ℝ) : ℝ :=
  if sin (x / 2) = 0 then (2 * (N : ℝ) + 1)
  else sin (((N : ℝ) + 1 / 2) * x) / sin (x / 2)

@[simp] lemma dirichletKernel_of_sin_half_eq_zero {N : ℕ} {x : ℝ} (hx : sin (x / 2) = 0) :
    dirichletKernel N x = 2 * (N : ℝ) + 1 := by
  simp [dirichletKernel, hx]

lemma dirichletKernel_of_sin_half_ne_zero {N : ℕ} {x : ℝ} (hx : sin (x / 2) ≠ 0) :
    dirichletKernel N x = sin (((N : ℝ) + 1 / 2) * x) / sin (x / 2) := by
  simp [dirichletKernel, hx]

/-- At integer multiples of `2π` the Dirichlet kernel takes the value `2 * N + 1`. -/
lemma dirichletKernel_at_two_pi_zmultiples (N : ℕ) (k : ℤ) :
    dirichletKernel N (2 * π * (k : ℝ)) = 2 * (N : ℝ) + 1 := by
  have hx : sin ((2 * π * (k : ℝ)) / 2) = 0 := by
    have hscale : (2 * π * (k : ℝ)) / 2 = (k : ℝ) * π := by
      simp [field]
    simp [hscale]
  simp [dirichletKernel, hx]

/-
D_N(x) & =\sum_{-N \leqslant k \leqslant N} e^{i k x} \\
proof : =\frac{e^{i(N+1) x}-e^{-i N x}}{e^{i x}-1} \\
& D_N(x) =\frac{e^{i\left(N+\frac{1}{2}\right) x}-e^{-i\left(N+\frac{1}{2}\right) x}}{e^{i \frac{x}{2}}-e^{-i \frac{x}{2}}}=\frac{\sin \left(\left(N+\frac{1}{2}\right) x\right)}{\sin \left(\frac{1}{2} x\right)} .
-/

/-- Base value of the Dirichlet kernel. -/
@[simp] lemma dirichletKernel_zero (x : ℝ) : dirichletKernel 0 x = 1 := by
  by_cases hx : sin (x / 2) = 0
  · simp [dirichletKernel, hx]
  · have h' : (((0 : ℝ) + 1 / 2) * x) = x / 2 := by
      simp [field]
    simp [dirichletKernel, hx, field]
    congr 1
    simp [field]

/-- The real Dirichlet kernel as the usual trigonometric sum of cosines. -/
theorem dirichletKernel_sum_cos (N : ℕ) (x : ℝ) (hx : sin (x / 2) ≠ 0) :
    dirichletKernel N x = 1 + 2 * ∑ k ∈ Finset.Icc (1 : ℕ) N, cos ((k : ℝ) * x) := by
  simp [dirichletKernel, hx]
  

  sorry




/-- A one-step recurrence for the Dirichlet kernel. -/
lemma dirichletKernel_succ (N : ℕ) (x : ℝ) :
    dirichletKernel (N.succ) x = dirichletKernel N x + 2 * cos ((N.succ : ℝ) * x) := by
  classical
  by_cases hx : sin (x / 2) = 0
  · -- At multiples of `2π` the cosine term collapses to `1`.
    obtain ⟨k, hk⟩ := (Real.sin_eq_zero_iff).1 hx
    have hx' : x = 2 * π * (k : ℝ) := by
      have hx'' : (k : ℝ) * π = x / 2 := hk
      calc
        x = 2 * (x / 2) := by ring
        _ = 2 * ((k : ℝ) * π) := by simpa [hx'']
        _ = 2 * π * (k : ℝ) := by ring
    have hcos : cos ((N.succ : ℝ) * x) = 1 := by
      have hmul :
          ((N.succ : ℝ) * x) =
            ((N.succ : ℤ) * k : ℝ) * (2 * π) := by
        calc
          (N.succ : ℝ) * x
              = (N.succ : ℝ) * (2 * π * (k : ℝ)) := by simpa [hx']
          _ = ((N.succ : ℝ) * (k : ℝ)) * (2 * π) := by ring
          _ = ((N.succ : ℤ) * k : ℝ) * (2 * π) := by
                norm_cast
      simp [hmul, mul_comm]-- using Real.cos_int_mul_two_pi ((N.succ : ℤ) * k)
      sorry
    simp [dirichletKernel, hx, hcos, add_comm, add_left_comm, add_assoc, two_mul, mul_add]
    sorry
  · -- Generic case: use the standard trigonometric identity.
    have hx_ne : sin (x / 2) ≠ 0 := hx
    have hsub :
        sin (((N.succ : ℝ) + 1 / 2) * x) -
          sin (((N : ℝ) + 1 / 2) * x)
          = 2 * sin (x / 2) * cos ((N.succ : ℝ) * x) := by
      have h := Real.sin_sub_sin (((N.succ : ℝ) + 1 / 2) * x) (((N : ℝ) + 1 / 2) * x)
      have hdiff :
          (((N.succ : ℝ) + 1 / 2) * x - ((N : ℝ) + 1 / 2) * x) / 2 = x / 2 := by sorry
      have hsum :
          (((N.succ : ℝ) + 1 / 2) * x + ((N : ℝ) + 1 / 2) * x) / 2
            = (N.succ : ℝ) * x := by sorry
      -- `sin_sub_sin` gives exactly the needed expression after simplification.
      -- simpa [hdiff, hsum, mul_comm, mul_left_comm, mul_assoc] using h
      sorry
    have hadd :
        sin (((N.succ : ℝ) + 1 / 2) * x)
          = sin (((N : ℝ) + 1 / 2) * x) + 2 * sin (x / 2) * cos ((N.succ : ℝ) * x) := by
      linarith
    have hquot :
        sin (((N.succ : ℝ) + 1 / 2) * x) / sin (x / 2)
          = sin (((N : ℝ) + 1 / 2) * x) / sin (x / 2)
              + 2 * cos ((N.succ : ℝ) * x) := by
      calc
        sin (((N.succ : ℝ) + 1 / 2) * x) / sin (x / 2)
            = (sin (((N : ℝ) + 1 / 2) * x) +
                2 * sin (x / 2) * cos ((N.succ : ℝ) * x)) / sin (x / 2) := by
              simp [hadd]
        _ = sin (((N : ℝ) + 1 / 2) * x) / sin (x / 2)
              + (2 * sin (x / 2) * cos ((N.succ : ℝ) * x)) / sin (x / 2) := by
              simp [add_div]
        _ = sin (((N : ℝ) + 1 / 2) * x) / sin (x / 2)
              + 2 * cos ((N.succ : ℝ) * x) := by
              field_simp [hx_ne, mul_comm, mul_left_comm, mul_assoc]
    simp [dirichletKernel, hx, hquot]
    sorry

/-- The image of `Finset.range N` under `Nat.succ` is the interval `{1, …, N}`. -/
lemma image_succ_range (N : ℕ) :
    (Finset.range N).image Nat.succ = Finset.Icc (1 : ℕ) N := by
  classical
  ext k
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
    have hm_lt : m < N := Finset.mem_range.mp hm
    have hm_le : m.succ ≤ N := Nat.succ_le_of_lt hm_lt
    have hm_one : 1 ≤ m.succ := Nat.succ_le_succ (Nat.zero_le _)
    simp [Finset.mem_Icc, hm_one, hm_le]
  · intro hk
    have hk_one : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_le : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hk_pos : 0 < k := (Nat.succ_le_iff).1 hk_one
    have hk_pred_lt : k.pred < N := by
      have hk_succ : k.pred.succ = k := Nat.succ_pred_eq_of_pos hk_pos
      have hk_le' : k.pred.succ ≤ N := by simpa [hk_succ] using hk_le
      exact Nat.lt_of_succ_le hk_le'
    have hk_pred_mem : k.pred ∈ Finset.range N := Finset.mem_range.mpr hk_pred_lt
    have hk_succ : Nat.succ k.pred = k := Nat.succ_pred_eq_of_pos hk_pos
    exact Finset.mem_image.mpr ⟨k.pred, hk_pred_mem, hk_succ⟩



end
