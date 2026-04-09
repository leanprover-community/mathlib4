/-
Copyright (c) 2026 J. York Seale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. York Seale
-/
module
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Schwarz Reflection for the Completed Riemann Zeta Function

We prove that `completedRiemannZeta₀` satisfies the Schwarz reflection
principle: `Λ₀(conj s) = conj(Λ₀(s))`. As a corollary, we establish that
`completedRiemannZeta₀` is real-valued on the critical line `Re(s) = 1/2`.

## Main results

* `completedRiemannZeta₀_conj`: The Schwarz reflection identity
  `completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s)`.

* `completedRiemannZeta₀_im_eq_zero_on_half`: On the critical line,
  `Im(completedRiemannZeta₀(1/2 + it)) = 0` for all real `t`.

* `completedRiemannZeta₀_deriv_re_eq_zero_on_half`: The derivative has vanishing
  real part on the critical line: `Re(Λ₀'(1/2 + it)) = 0` for all real `t`.

## Proof strategy

The Schwarz reflection follows from the Mellin representation of
`completedRiemannZeta₀`. The kernel `(hurwitzEvenFEPair 0).f_modif`
is real-valued (its imaginary part vanishes), so the Mellin integral
commutes with complex conjugation via `integral_conj`. The power
`t^(s/2 - 1)` conjugates correctly for positive real `t` by `cpow_conj`.

The critical-line reality result composes Schwarz reflection with the
functional equation: at `s = 1/2 + it`, we have `conj(s) = 1 - s`,
so `conj(Λ₀(s)) = Λ₀(conj s) = Λ₀(1 - s) = Λ₀(s)`.
-/

@[expose] public section


open Complex HurwitzZeta MeasureTheory Set

section SchwarzReflection

/-- The modified kernel of the Hurwitz even FE pair at `a = 0` is real-valued:
its complex conjugate equals itself. This is because it is built from
real-valued functions (exponentials of real quadratic forms). -/
private lemma hurwitzEvenFEPair_f_modif_conj_fixed (t : ℝ) :
    (hurwitzEvenFEPair 0).f_modif t = starRingEnd ℂ ((hurwitzEvenFEPair 0).f_modif t) := by
  rw [eq_comm, Complex.conj_eq_iff_im]
  simp only [WeakFEPair.f_modif, Pi.add_apply, indicator_apply]
  split_ifs <;> simp [Complex.add_im, Complex.sub_im, Complex.ofReal_im,
    Complex.one_im, Complex.zero_im, hurwitzEvenFEPair]

/-- **Schwarz reflection for the completed Riemann zeta function.**
The completed Riemann zeta function `Λ₀` satisfies
`Λ₀(conj(s)) = conj(Λ₀(s))` for all `s : ℂ`.

This follows from the Mellin representation: the kernel is real-valued,
positive-real powers conjugate correctly, and the integral commutes
with conjugation. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta₀ s) := by
  change mellin (hurwitzEvenFEPair 0).f_modif (starRingEnd ℂ s / 2) / 2 =
    starRingEnd ℂ (mellin (hurwitzEvenFEPair 0).f_modif (s / 2) / 2)
  rw [map_div₀, show (starRingEnd ℂ) (2 : ℂ) = 2 from by exact_mod_cast conj_ofReal 2]
  congr 1
  simp only [mellin]
  have hpt {t : ℝ} (ht : t ∈ Ioi 0) :
    (↑t : ℂ) ^ ((starRingEnd ℂ) s / 2 - 1) • (hurwitzEvenFEPair 0).f_modif t =
      (starRingEnd ℂ) ((↑t : ℂ) ^ (s / 2 - 1) • (hurwitzEvenFEPair 0).f_modif t) := by
    simp only [smul_eq_mul, map_mul]
    congr 1
    · -- Inline conj_half_sub_one + cpow_conj_pos_real
      have harg : ((t : ℂ)).arg ≠ Real.pi := by
        rw [arg_ofReal_of_nonneg (le_of_lt ht)]; exact Real.pi_pos.ne
      rw [show starRingEnd ℂ s / 2 - 1 = starRingEnd ℂ (s / 2 - 1) from by
        rw [map_sub, map_div₀, show (starRingEnd ℂ) (2 : ℂ) = 2 from by
          exact_mod_cast conj_ofReal 2, map_one]]
      rw [cpow_conj _ _ harg]; simp [conj_ofReal]
    · exact hurwitzEvenFEPair_f_modif_conj_fixed t
  calc ∫ t in Ioi (0 : ℝ), (↑t : ℂ) ^ ((starRingEnd ℂ) s / 2 - 1) •
        (hurwitzEvenFEPair 0).f_modif t
      = ∫ t in Ioi (0 : ℝ), (starRingEnd ℂ) ((↑t : ℂ) ^ (s / 2 - 1) •
        (hurwitzEvenFEPair 0).f_modif t) :=
          setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt ht
    _ = (starRingEnd ℂ) (∫ t in Ioi (0 : ℝ), (↑t : ℂ) ^ (s / 2 - 1) •
        (hurwitzEvenFEPair 0).f_modif t) :=
          integral_conj

end SchwarzReflection

section CriticalLine

/-- At `s = 1/2 + it` on the critical line, conjugation gives `1 - s`. -/
private lemma conj_half_add_mul_I (t : ℝ) :
    (starRingEnd ℂ) (⟨1 / 2, t⟩ : ℂ) = 1 - (⟨1 / 2, t⟩ : ℂ) := by
  apply Complex.ext_iff.mpr
  constructor
  · simp [Complex.conj_re, Complex.sub_re, Complex.one_re]; ring
  · simp [Complex.conj_im, Complex.sub_im, Complex.one_im]

/-- **The completed Riemann zeta function is real-valued on the critical line.**
At every point `1/2 + it` on the critical line, `Im(Λ₀(1/2 + it)) = 0`.

Proof: Schwarz reflection gives `conj(Λ₀(s)) = Λ₀(conj s)`,
the functional equation gives `Λ₀(1 - s) = Λ₀(s)`,
and at `s = 1/2 + it` we have `conj(s) = 1 - s`. -/
theorem completedRiemannZeta₀_im_eq_zero_on_half (t : ℝ) :
    (completedRiemannZeta₀ ⟨1/2, t⟩).im = 0 := by
  suffices h :
      (starRingEnd ℂ) (completedRiemannZeta₀ ⟨1 / 2, t⟩) = completedRiemannZeta₀ ⟨1 / 2, t⟩ from
    conj_eq_iff_im.mp h
  conv_lhs => rw [← completedRiemannZeta₀_conj ⟨1 / 2, t⟩]
  rw [conj_half_add_mul_I]
  exact completedRiemannZeta₀_one_sub ⟨1 / 2, t⟩

/-- The completed Riemann zeta function is real-valued at `1/2 + it`,
stated as `conj(Λ₀(1/2 + it)) = Λ₀(1/2 + it)`. -/
theorem completedRiemannZeta₀_conj_eq_self_on_half (t : ℝ) :
    (starRingEnd ℂ) (completedRiemannZeta₀ ⟨1 / 2, t⟩) = completedRiemannZeta₀ ⟨1 / 2, t⟩ := by
  rw [← completedRiemannZeta₀_conj, conj_half_add_mul_I]
  exact completedRiemannZeta₀_one_sub ⟨1 / 2, t⟩

end CriticalLine

section DerivativeCriticalLine

/-- The affine map `z ↦ 1/2 + z * I` has complex derivative `I`. -/
private lemma hasDerivAt_half_add_mul_I (z : ℂ) :
    HasDerivAt (fun w : ℂ => (1/2 : ℂ) + w * I) I z := by
  convert (hasDerivAt_const z (1/2 : ℂ)).add ((hasDerivAt_id z).mul_const I) using 1; simp

/-- The rotated function `z ↦ Λ₀(1/2 + z · I)` has complex derivative
`Λ₀'(1/2 + z · I) · I` at `z`. -/
private lemma hasDerivAt_completedRiemannZeta₀_rotated (z : ℂ) :
    HasDerivAt (fun w => completedRiemannZeta₀ (1/2 + w * I))
      (deriv completedRiemannZeta₀ (1/2 + z * I) * I) z :=
  differentiable_completedZeta₀.differentiableAt.hasDerivAt.comp z (hasDerivAt_half_add_mul_I z)

/-- On the real line, `1/2 + t * I = ⟨1/2, t⟩`. -/
private lemma half_add_ofReal_mul_I (t : ℝ) :
    (1/2 : ℂ) + (↑t) * I = ⟨1/2, t⟩ := by
  apply Complex.ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- Imaginary-part analogue of `HasDerivAt.real_of_complex`: if a complex function
is ℂ-differentiable at a real point, then the imaginary part of its restriction to ℝ
is ℝ-differentiable with derivative equal to the imaginary part of the complex derivative. -/
private lemma HasDerivAt.im_of_complex {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}
    (h : HasDerivAt e e' z) :
    HasDerivAt (fun x : ℝ => (e x).im) e'.im z := by
  have A : HasFDerivAt ((↑) : ℝ → ℂ) ofRealCLM z := ofRealCLM.hasFDerivAt
  have B :
    HasFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealCLM z) :=
    h.hasFDerivAt.restrictScalars ℝ
  have C : HasFDerivAt im imCLM (e (ofRealCLM z)) := imCLM.hasFDerivAt
  simpa using (C.comp z (B.comp z A)).hasDerivAt

/-- **The derivative of the completed Riemann zeta function has vanishing
real part on the critical line:** `Re(Λ₀'(1/2 + it)) = 0` for all real `t`.

Proof: The rotated function `e(z) = Λ₀(1/2 + z · I)` is entire with
`e'(z) = Λ₀'(1/2 + z · I) · I`. Restricting to ℝ, `Im(e(t)) = 0` for all
real `t` (by `completedRiemannZeta₀_im_eq_zero_on_half`), so the ℝ-derivative
of `Im(e(t))` vanishes. But this derivative equals `(e'(t)).im = (Λ₀'(1/2+it) · I).im
= Re(Λ₀'(1/2 + it))`, giving the result. -/
theorem completedRiemannZeta₀_deriv_re_eq_zero_on_half (t : ℝ) :
    (deriv completedRiemannZeta₀ ⟨1/2, t⟩).re = 0 := by
  have hderiv := hasDerivAt_completedRiemannZeta₀_rotated (↑t)
  have him_deriv := hderiv.im_of_complex
  simp only [half_add_ofReal_mul_I] at him_deriv
  have him_const : HasDerivAt (fun s : ℝ => (completedRiemannZeta₀ ⟨1/2, s⟩).im) 0 t := by
    have : (fun s : ℝ => (completedRiemannZeta₀ ⟨1/2, s⟩).im) = fun _ => 0 :=
      funext completedRiemannZeta₀_im_eq_zero_on_half
    rw [this]; exact hasDerivAt_const t (0 : ℝ)
  have h_eq := him_deriv.unique him_const
  simp only [mul_im, I_re, I_im] at h_eq
  linarith

end DerivativeCriticalLine
