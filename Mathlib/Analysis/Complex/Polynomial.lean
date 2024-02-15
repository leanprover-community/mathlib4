/-
Copyright (c) 2019 Chris Hughes All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Yury Kudryashov
-/
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Algebra.Polynomial

#align_import analysis.complex.polynomial from "leanprover-community/mathlib"@"17ef379e997badd73e5eabb4d38f11919ab3c4b3"

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root using Liouville's theorem.

As a consequence, the complex numbers are algebraically closed.

We also show that an irreducible real polynomial has degree at most two.
-/

open Polynomial Bornology Complex

open scoped ComplexConjugate

namespace Complex

/-- **Fundamental theorem of algebra**: every non constant complex polynomial
  has a root -/
theorem exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z := by
  by_contra! hf'
  /- Since `f` has no roots, `f⁻¹` is differentiable. And since `f` is a polynomial, it tends to
  infinity at infinity, thus `f⁻¹` tends to zero at infinity. By Liouville's theorem, `f⁻¹ = 0`. -/
  have (z : ℂ) : (f.eval z)⁻¹ = 0 :=
    (f.differentiable.inv hf').apply_eq_of_tendsto_cocompact z <|
      Metric.cobounded_eq_cocompact (α := ℂ) ▸ (Filter.tendsto_inv₀_cobounded.comp <| by
        simpa only [tendsto_norm_atTop_iff_cobounded]
          using f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop)
  -- Thus `f = 0`, contradicting the fact that `0 < degree f`.
  obtain rfl : f = C 0 := Polynomial.funext fun z ↦ inv_injective <| by simp [this]
  simp at hf
#align complex.exists_root Complex.exists_root

instance isAlgClosed : IsAlgClosed ℂ :=
  IsAlgClosed.of_exists_root _ fun _p _ hp => Complex.exists_root <| degree_pos_of_irreducible hp
#align complex.is_alg_closed Complex.isAlgClosed

end Complex

lemma Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero (p : ℝ[X]) {z : ℂ} (h0 : aeval z p = 0)
    (hz : z.im ≠ 0) : (X - C ((starRingEnd ℂ) z)) * (X - C z) ∣ map (algebraMap ℝ ℂ) p := by
  apply IsCoprime.mul_dvd
  · exact isCoprime_X_sub_C_of_isUnit_sub <| .mk0 _ <| sub_ne_zero.2 <| mt conj_eq_iff_im.1 hz
  · simpa [dvd_iff_isRoot, aeval_conj]
  · simpa [dvd_iff_isRoot]

/-- If `z` is a non-real complex root of a real polynomial,
then `p` is divisible by a quadratic polynomial. -/
lemma Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero (p : ℝ[X]) {z : ℂ} (h0 : aeval z p = 0)
    (hz : z.im ≠ 0) : X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) ∣ p := by
  rw [← map_dvd_map' (algebraMap ℝ ℂ)]
  convert p.mul_star_dvd_of_aeval_eq_zero_im_ne_zero h0 hz
  calc
    map (algebraMap ℝ ℂ) (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2))
    _ = X ^ 2 - C (↑(2 * z.re) : ℂ) * X + C (‖z‖ ^ 2 : ℂ) := by simp
    _ = (X - C (conj z)) * (X - C z) := by
      rw [← add_conj, map_add, ← mul_conj', map_mul]
      ring

/-- An irreducible real polynomial has degree at most two. -/
lemma Irreducible.degree_le_two {p : ℝ[X]} (hp : Irreducible p) : degree p ≤ 2 := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z p = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne'
  cases eq_or_ne z.im 0 with
  | inl hz0 =>
    lift z to ℝ using hz0
    erw [aeval_ofReal, IsROrC.ofReal_eq_zero] at hz
    exact (degree_eq_one_of_irreducible_of_root hp hz).trans_le one_le_two
  | inr hz0 =>
    obtain ⟨q, rfl⟩ := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hz0
    have hd : degree (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)) = 2 := by
      compute_degree!
    have hq : IsUnit q := by
      refine (of_irreducible_mul hp).resolve_left (mt isUnit_iff_degree_eq_zero.1 ?_)
      rw [hd]
      exact two_ne_zero
    refine (degree_mul_le _ _).trans_eq ?_
    rwa [isUnit_iff_degree_eq_zero.1 hq, add_zero]

/-- An irreducible real polynomial has natural degree at most two. -/
lemma Irreducible.nat_degree_le_two {p : ℝ[X]} (hp : Irreducible p) : natDegree p ≤ 2 :=
  natDegree_le_iff_degree_le.2 hp.degree_le_two
