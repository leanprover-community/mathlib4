/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Embedding the upper half-plane into the projective line
-/

@[expose] public noncomputable section

open UpperHalfPlane
open Matrix GeneralLinearGroup

lemma toOnePoint_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (τ : ℍ) :
    (↑(g • τ) : OnePoint ℂ) = (g.map Complex.ofRealHom) • τ := by
  have : g 1 0 * (τ : ℂ) + g 1 1 ≠ 0 := UpperHalfPlane.denom_ne_zero g τ
  simp [OnePoint.smul_some_eq_ite, this, UpperHalfPlane.coe_smul_of_det_pos hg, num, denom]

/-- Parabolicity is preserved under extension of scalars. -/
lemma Matrix.GeneralLinearGroup.IsParabolic.map {A B : Type*} [Field A] [CommRing B] [Nontrivial B]
    {g : GL (Fin 2) A} (hgp : g.IsParabolic) (f : A →+* B) :
    (g.map f).IsParabolic := by
  have hfi : Function.Injective f := RingHom.injective f
  constructor
  · rintro ⟨a, ha⟩
    obtain rfl : a = f (g 0 0) := by simpa using congr_arg (· 0 0) ha
    apply hgp.1
    use g 0 0
    simpa [← (Matrix.map_injective <| RingHom.injective f).eq_iff] using ha
  · -- should we make `Matrix.discr_map`? Or `Polynomial.discr_map`?
    convert (map_eq_zero_iff _ hfi).mpr hgp.2
    simp [discr_fin_two, AddMonoidHom.map_trace, map_ofNat, RingHom.map_det]

/-- If `g` is parabolic, then `g` has no fixed points in `ℍ`. -/
lemma UpperHalfPlane.smul_ne_self_of_isParabolic
    {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (hgp : g.IsParabolic) (τ : ℍ) :
    g • τ ≠ τ := by
  rw [Ne, UpperHalfPlane.ext_iff, ← OnePoint.coe_eq_coe, toOnePoint_smul hg,
    (hgp.map _).smul_eq_self_iff]
  intro hτ
  apply τ.im_ne_zero
  simp only [parabolicFixedPoint, Fin.isValue, GeneralLinearGroup.map_apply,
    Complex.ofRealHom_eq_coe, Complex.ofReal_eq_zero] at hτ
  split_ifs at hτ
  · exact (OnePoint.infty_ne_coe _ hτ.symm).elim
  · simp only [Fin.isValue, OnePoint.some_eq_iff] at hτ
    simp [← coe_im, hτ, Complex.div_im]

/-- If `g` is hyperbolic, then `g` has no fixed points in `ℍ`. -/
lemma UpperHalfPlane.smul_ne_self_of_isHyperbolic {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    (hgh : g.IsHyperbolic) (τ : ℍ) :
    g • τ ≠ τ := by
  rw [Ne, UpperHalfPlane.ext_iff, ← OnePoint.coe_eq_coe, toOnePoint_smul hg,
    ← fixpointPolynomial_aeval_eq_zero_iff]
  rcases τ with ⟨τ, hτ⟩
  simp only [coe_mk_subtype, fixpointPolynomial, Fin.isValue, GeneralLinearGroup.map_apply,
    Complex.ofRealHom_eq_coe, map_sub, Polynomial.coe_aeval_eq_eval, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub]
  contrapose! hτ
  by_cases hc : g 1 0 = 0
  · -- silly case : c = 0
    simp only [Fin.isValue, hc, Complex.ofReal_zero, zero_mul, zero_add] at hτ
    by_cases hd : g 1 1 = g 0 0
    · contrapose! hgh
      simp only [GeneralLinearGroup.IsHyperbolic, Matrix.IsHyperbolic, discr_fin_two, trace_fin_two,
        det_fin_two, hc]
      grind
    rw [sub_eq_zero, mul_comm, ← div_eq_iff_mul_eq] at hτ
    · simp [← hτ, Complex.div_im]
    · norm_cast
      grind
  have := Real.sq_sqrt hgh.le
  rw [sq, ← Complex.ofReal_inj, Complex.ofReal_mul] at this
  rw [sq, sub_eq_add_neg, quadratic_eq_zero_iff (mod_cast hc) (s := ↑√g.val.discr)] at hτ
  · rcases hτ with hτ | hτ <;> simp [hτ, Complex.div_im]
  · convert this.symm
    simp [discrim, discr_fin_two, trace_fin_two, det_fin_two]
    ring

end
