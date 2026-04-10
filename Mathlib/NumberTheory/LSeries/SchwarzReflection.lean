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
principle: `Λ₀(conj s) = conj(Λ₀(s))`.

## Proof strategy

The proof proceeds in two stages:

1. **Real on reals**: We show that the Mellin kernel `(hurwitzEvenFEPair 0).f_modif`
   is real-valued, and that for `s : ℝ` the Mellin integrand
   `t^(s/2-1) · kernel(t)` is real (since `t^r` is real for `t > 0, r ∈ ℝ`).
   Therefore `completedRiemannZeta₀(s)` is real when `s ∈ ℝ`.

2. **Schwarz reflection**: The same real-kernel property, combined with
   `cpow_conj` for positive reals and `integral_conj`, gives the full
   conjugation identity `Λ₀(conj s) = conj(Λ₀(s))`.

The critical-line reality result then follows by composing Schwarz reflection
with the functional equation: at `s = 1/2 + it`, `conj(s) = 1 - s`.

## Main results

* `completedRiemannZeta₀_ofReal_im`: `Λ₀` is real-valued on `ℝ`.
* `completedRiemannZeta₀_conj`: Schwarz reflection `Λ₀(conj s) = conj(Λ₀(s))`.
* `completedRiemannZeta₀_im_eq_zero_on_half`: `Im(Λ₀(1/2 + it)) = 0`.
* `completedRiemannZeta₀_deriv_re_eq_zero_on_half`: `Re(Λ₀'(1/2 + it)) = 0`.
-/

@[expose] public section

open Complex HurwitzZeta MeasureTheory Set

/-! ## The kernel is real-valued -/

section RealKernel

/-- The modified kernel of the Hurwitz even FE pair at `a = 0` is real-valued:
its imaginary part vanishes. This is because it is built from
real-valued functions (exponentials of real quadratic forms). -/
theorem hurwitzEvenFEPair_f_modif_im_zero (t : ℝ) :
    ((hurwitzEvenFEPair 0).f_modif t).im = 0 := by
  simp only [WeakFEPair.f_modif, Pi.add_apply, indicator_apply]
  split_ifs <;> simp [Complex.add_im, Complex.sub_im, Complex.ofReal_im,
    Complex.one_im, Complex.zero_im, hurwitzEvenFEPair]

/-- Equivalent formulation: the kernel equals its own conjugate. -/
theorem hurwitzEvenFEPair_f_modif_conj (t : ℝ) :
    starRingEnd ℂ ((hurwitzEvenFEPair 0).f_modif t) = (hurwitzEvenFEPair 0).f_modif t := by
  rw [Complex.conj_eq_iff_im]
  exact hurwitzEvenFEPair_f_modif_im_zero t

end RealKernel

/-! ## General Schwarz reflection for Mellin transforms with real kernels -/

section MellinConj

/-- **Mellin transform commutes with conjugation for real-valued kernels.**
If `φ : ℝ → ℂ` satisfies `conj(φ(t)) = φ(t)` for all `t`, then
`mellin φ (conj s) = conj (mellin φ s)`. -/
theorem mellin_conj_of_real_kernel {φ : ℝ → ℂ}
    (hreal : ∀ t : ℝ, starRingEnd ℂ (φ t) = φ t) (s : ℂ) :
    mellin φ (starRingEnd ℂ s) = starRingEnd ℂ (mellin φ s) := by
  simp only [mellin]
  have hpt {t : ℝ} (ht : t ∈ Ioi 0) :
    (↑t : ℂ) ^ (starRingEnd ℂ s - 1) • φ t =
      starRingEnd ℂ ((↑t : ℂ) ^ (s - 1) • φ t) := by
    simp only [smul_eq_mul, map_mul]
    congr 1
    · have harg : ((t : ℂ)).arg ≠ Real.pi := by
        rw [arg_ofReal_of_nonneg (le_of_lt ht)]; exact Real.pi_pos.ne
      rw [show starRingEnd ℂ s - 1 = starRingEnd ℂ (s - 1) from by
        rw [map_sub, map_one]]
      rw [cpow_conj _ _ harg]; simp [conj_ofReal]
    · exact (hreal t).symm
  calc ∫ t in Ioi (0 : ℝ), (↑t : ℂ) ^ (starRingEnd ℂ s - 1) • φ t
      = ∫ t in Ioi (0 : ℝ), starRingEnd ℂ ((↑t : ℂ) ^ (s - 1) • φ t) :=
          setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt ht
    _ = starRingEnd ℂ (∫ t in Ioi (0 : ℝ), (↑t : ℂ) ^ (s - 1) • φ t) :=
          integral_conj

/-- **Schwarz reflection for `Λ₀` of a `WeakFEPair` with real-valued kernel.**
If `P.f_modif` is real-valued, then `P.Λ₀ (conj s) = conj (P.Λ₀ s)`. -/
theorem WeakFEPair.Λ₀_conj (P : WeakFEPair ℂ)
    (hreal : ∀ t : ℝ, starRingEnd ℂ (P.f_modif t) = P.f_modif t) (s : ℂ) :
    P.Λ₀ (starRingEnd ℂ s) = starRingEnd ℂ (P.Λ₀ s) :=
  mellin_conj_of_real_kernel hreal s

end MellinConj

/-! ## Schwarz reflection for `completedRiemannZeta₀` -/

section SchwarzReflection

/-- **Schwarz reflection for the completed Riemann zeta function.**
`Λ₀(conj(s)) = conj(Λ₀(s))` for all `s : ℂ`.

Specialization of `WeakFEPair.Λ₀_conj` to `hurwitzEvenFEPair 0`,
composed with the `s/2` and `/2` rescaling. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta₀ s) := by
  change (hurwitzEvenFEPair 0).Λ₀ (starRingEnd ℂ s / 2) / 2 =
    starRingEnd ℂ ((hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2)
  rw [map_div₀, show (starRingEnd ℂ) (2 : ℂ) = 2 from by exact_mod_cast conj_ofReal 2]
  congr 1
  rw [show starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) from by
    rw [map_div₀, show (starRingEnd ℂ) (2 : ℂ) = 2 from by exact_mod_cast conj_ofReal 2]]
  exact (hurwitzEvenFEPair 0).Λ₀_conj hurwitzEvenFEPair_f_modif_conj (s / 2)

/-- **`completedRiemannZeta₀` is real-valued on `ℝ`.**
For `r : ℝ`, `Im(Λ₀(r)) = 0`. This follows from Schwarz reflection
since `conj(↑r) = ↑r` for real `r`. -/
theorem completedRiemannZeta₀_ofReal_im (r : ℝ) :
    (completedRiemannZeta₀ ↑r).im = 0 := by
  have h : starRingEnd ℂ (completedRiemannZeta₀ ↑r) = completedRiemannZeta₀ ↑r := by
    rw [← completedRiemannZeta₀_conj, conj_ofReal]
  exact conj_eq_iff_im.mp h

end SchwarzReflection

/-! ## Critical line -/

section CriticalLine

/-- At `s = 1/2 + it` on the critical line, conjugation gives `1 - s`. -/
private lemma conj_half_add_mul_I (t : ℝ) :
    (starRingEnd ℂ) (⟨1 / 2, t⟩ : ℂ) = 1 - (⟨1 / 2, t⟩ : ℂ) := by
  apply Complex.ext_iff.mpr
  constructor
  · simp [Complex.conj_re, Complex.sub_re, Complex.one_re]; ring
  · simp [Complex.conj_im, Complex.sub_im, Complex.one_im]

/-- **The completed Riemann zeta function is real-valued on the critical line.**
At every point `1/2 + it`, `Im(Λ₀(1/2 + it)) = 0`.

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

/-! ## Derivative on the critical line -/

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
/-- Imaginary-part analogue of `HasDerivAt.real_of_complex`. -/
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

/-- **The derivative has vanishing real part on the critical line:**
`Re(Λ₀'(1/2 + it)) = 0` for all real `t`. -/
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

end
