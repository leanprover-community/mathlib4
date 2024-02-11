/-
Copyright (c) 2019 Chris Hughes All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
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
-/

open Polynomial Bornology

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

#check nsmul_eq_mul

/-- If `z` is a non-real complex root of a real polynomial,
then `p` is divisible by a quadratic polynomial. -/
lemma Polynomial.quadratic_dvd_of_aeval_eq_zero (p : ℝ[X]) {z : ℂ} (h0 : aeval z p = 0)
    (hz : z.im ≠ 0) : X ^ 2 - 2 * z.re • X + C (‖z‖ ^ 2) ∣ p := by
  suffices (X ^ 2 - (2 * z.re) • X + C (‖z‖ ^ 2 : ℂ) : ℂ[X]) ∣ map (algebraMap ℝ ℂ) p by
    simpa [← map_dvd_map' (algebraMap ℝ ℂ), mul_smul] using this
  suffices (X - C (conj z)) * (X - C z) ∣ map (algebraMap ℝ ℂ) p by
    rw [sub_mul, mul_sub, mul_sub] at this
  -- { rwa [sub_mul, mul_sub, ← sq, mul_comm X, mul_sub, ← sub_add, sub_sub, ← add_mul, ← map_add,
  --     ← map_mul, ← norm_sq_eq_conj_mul_self, add_conj, of_real_mul, of_real_bit0, of_real_one]
  --     at this },
  refine (is_coprime_X_sub_C_of_is_unit_sub $ is_unit.mk0 _ $ sub_ne_zero.2 $
    mt eq_conj_iff_im.1 hz).mul_dvd (dvd_iff_is_root.2 _) (dvd_iff_is_root.2 _),
  { rwa [is_root, eval_map, ← aeval_def, aeval_conj, _root_.map_eq_zero] },
  { rwa [is_root, eval_map, ← aeval_def] }
end

/-- An irreducible real polynomial has degree at most two. -/
lemma irreducible.degree_le_two {p : ℝ[X]} (hp : irreducible p) : degree p ≤ 2 :=
begin
  obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z p = 0,
    from is_alg_closed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne',
  cases eq_or_ne z.im 0 with hz0 hz0,
  { lift z to ℝ using hz0,
    rw [← complex.coe_algebra_map, aeval_algebra_map_apply_eq_algebra_map_eval, _root_.map_eq_zero]
      at hz,
    exact (degree_eq_one_of_irreducible_of_root hp hz).trans_le one_le_two },
  { obtain ⟨q, rfl⟩ := p.quadratic_dvd_of_complex_root hz hz0,
    have hd : degree (X ^ 2 - C (2 * z.re) * X + C (norm_sq z)) = 2,
    { rw [← one_mul (X ^ 2), ← map_one C, sub_eq_add_neg, ← neg_mul, ← map_neg],
      exact degree_quadratic one_ne_zero },
    have hq : is_unit q,
    { refine (of_irreducible_mul hp).resolve_left (mt is_unit_iff_degree_eq_zero.1 _),
      simpa only [← with_bot.coe_one, ← with_bot.coe_bit0, with_bot.coe_eq_zero, hd]
        using two_ne_zero },
    refine (degree_mul_le _ _).trans_eq _,
    rw [is_unit_iff_degree_eq_zero.1 hq, hd, add_zero] }
end

/-- An irreducible real polynomial has natural degree at most two. -/
lemma irreducible.nat_degree_le_two {p : ℝ[X]} (hp : irreducible p) : nat_degree p ≤ 2 :=
nat_degree_le_iff_degree_le.2 hp.degree_le_two
