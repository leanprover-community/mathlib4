/-
Copyright (c) 2026 interleaves. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: interleaves
-/
module
public import Mathlib.NumberTheory.LSeries.RiemannZeta

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

private lemma conj_ofReal_two : (starRingEnd ℂ) (2 : ℂ) = 2 := by
  exact_mod_cast conj_ofReal 2

private lemma arg_pos_real_ne_pi (t : ℝ) (ht : 0 < t) : ((t : ℂ)).arg ≠ Real.pi := by
  rw [arg_ofReal_of_nonneg (le_of_lt ht)]
  exact Real.pi_pos.ne

private lemma cpow_conj_pos_real (t : ℝ) (ht : 0 < t) (w : ℂ) :
    (↑t : ℂ) ^ (starRingEnd ℂ w) = starRingEnd ℂ (t ^ w) := by
  rw [cpow_conj _ _ (arg_pos_real_ne_pi t ht)]
  simp [conj_ofReal]

private lemma conj_div_two (s : ℂ) :
    starRingEnd ℂ (s / 2) = starRingEnd ℂ s / 2 := by
  rw [map_div₀, conj_ofReal_two]

private lemma conj_half_sub_one (s : ℂ) :
    starRingEnd ℂ s / 2 - 1 = starRingEnd ℂ (s / 2 - 1) := by
  rw [map_sub, conj_div_two, map_one]

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
  rw [map_div₀, conj_ofReal_two]
  congr 1
  simp only [mellin]
  have hpt {t : ℝ} (ht : t ∈ Ioi 0) :
    (↑t : ℂ) ^ ((starRingEnd ℂ) s / 2 - 1) • (hurwitzEvenFEPair 0).f_modif t =
      (starRingEnd ℂ) ((↑t : ℂ) ^ (s / 2 - 1) • (hurwitzEvenFEPair 0).f_modif t) := by
    simp only [smul_eq_mul, map_mul]
    congr 1
    · rw [conj_half_sub_one]
      exact cpow_conj_pos_real t ht (s / 2 - 1)
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

Proof: At `s = 1/2 + it`, conjugation gives `conj(s) = 1/2 - it = 1 - s`.
By Schwarz reflection: `conj(Λ₀(s)) = Λ₀(conj s) = Λ₀(1 - s)`.
By the functional equation: `Λ₀(1 - s) = Λ₀(s)`.
Therefore `conj(Λ₀(s)) = Λ₀(s)`, which holds iff `Im(Λ₀(s)) = 0`.

This establishes that zeros of `Λ₀` on the critical line are sign changes
of a real-valued function (codimension 1), while off-line zeros would
require the simultaneous vanishing of both real and imaginary parts
(codimension 2). -/
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
