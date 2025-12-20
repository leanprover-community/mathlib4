/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.Algebra.Polynomial.Expand

/-!
## Expand power series

Given a power series `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some nonzero natural number `n`.
This operation is called `PowerSeries.expand` and it is an algebra homomorphism.

### Main declaration

* `PowerSeries.expand`: expand a power series by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

@[expose] public section

namespace PowerSeries

variable {τ R S : Type*} [CommRing R] [CommRing S] (p : ℕ) (hp : p ≠ 0)

/-- Expand the power series by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `PowerSeries.expand`. -/
noncomputable def expand : PowerSeries R →ₐ[R] PowerSeries R :=
  MvPowerSeries.expand p hp

theorem expand_apply (f : PowerSeries R) : expand p hp f = subst (X ^ p) f := by
  simp only [expand, MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]
  rfl

theorem expand_C (r : R) : expand p hp (C r : PowerSeries R) = C r := by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

theorem expand_mul_eq_comp (q : ℕ) (hq : q ≠ 0) :
    expand (p * q) (p.mul_ne_zero hp hq) = (expand p hp (R := R)).comp (expand q hq) := by
  ext1 i
  simp_rw [expand, MvPowerSeries.expand_mul_eq_comp p hp q hq]

theorem expand_mul (q : ℕ) (hq : q ≠ 0) (φ : PowerSeries R) :
    φ.expand (p * q) (p.mul_ne_zero hp hq) = (φ.expand q hq).expand p hp :=
  DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ

@[simp]
theorem expand_X : expand p hp (X (R := R)) = X ^ p :=
  substAlgHom_X (HasSubst.X_pow hp)

@[simp]
theorem expand_monomial (d : ℕ) (r : R) :
    expand p hp (monomial d r) = monomial (p * d) r := by
  simp_rw [expand, monomial, MvPowerSeries.expand_monomial, Finsupp.smul_single, smul_eq_mul]

@[simp]
theorem expand_one : expand 1 one_ne_zero = AlgHom.id R (PowerSeries R) := by
  simp [expand]

theorem expand_one_apply (f : PowerSeries R) : expand 1 one_ne_zero f = f := by simp

@[simp]
theorem map_expand (f : R →+* S) (φ : PowerSeries R) :
    map f (expand p hp φ) = expand p hp (map f φ) := by
  simp_rw [expand_apply, map, map_subst (HasSubst.X_pow hp), map_pow, X, MvPowerSeries.map_X, map]

/- TODO : In the original file of multi variate polynomial, there are two theorem about rename
here, but we don't have rename for multi variate power series. And for `eval₂Hom`, `eval₂`
and `aevel`, the expression does't look good. -/

variable (q : ℕ) (hq : 0 < q)

@[simp]
theorem coeff_expand_mul (φ : PowerSeries R) (m : ℕ) :
    (expand p hp φ).coeff (p * m) = φ.coeff m := by
  classical
  rw [coeff, ← smul_eq_mul, (Finsupp.smul_single p () m).symm, expand,
    MvPowerSeries.coeff_expand_smul]
  rfl

theorem coeff_expand_of_not_dvd (φ : PowerSeries R) {m : ℕ} (h : ¬ p ∣ m) :
    (expand p hp φ).coeff m = 0 := by
  classical
  rw [coeff, expand, MvPowerSeries.coeff_expand_of_not_dvd p hp φ (i := ())]
  simpa

theorem support_expand_subset (φ : PowerSeries R) :
    (expand p hp φ).support ⊆ φ.support.image (p • ·) := by
  rw [expand, MvPowerSeries.support_expand]

theorem support_expand (φ : PowerSeries R) :
    (expand p hp φ).support = φ.support.image (p • ·) := by
  classical
  rw [expand, MvPowerSeries.support_expand]

section Polynomial

@[simp]
theorem expand_eq_expand {φ : Polynomial R} :
    (φ.expand p (R := R)) = expand p hp φ.toPowerSeries := by
  ext n
  simp only [Polynomial.coeff_coe]
  by_cases! h : p ∣ n
  · obtain ⟨m, hm⟩ := h
    rw [hm, coeff_expand_mul p hp _ _, mul_comm p, φ.coeff_expand_mul
      (p.ne_zero_iff_zero_lt.mp hp), φ.coeff_coe]
  · rw [coeff_expand_of_not_dvd p hp _ h, Polynomial.coeff_expand (p.ne_zero_iff_zero_lt.mp hp),
      if_neg h]

end Polynomial

section ExpChar

variable [ExpChar R p]

theorem expand_char {f : PowerSeries R} :
    (f.expand p hp).map (frobenius R p) = f ^ p := by
  rw [expand, map, MvPowerSeries.expand_char]

theorem map_expand_pow_char (f : PowerSeries R) (n : ℕ) :
    map (frobenius R p ^ n) (expand (p ^ n) (pow_ne_zero n hp) f) = f ^ p ^ n := by
  rw [expand, map, MvPowerSeries.map_expand_pow_char p hp]

end ExpChar

end PowerSeries
