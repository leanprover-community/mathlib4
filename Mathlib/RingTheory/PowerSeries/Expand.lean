/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Expand

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
  simp [expand, MvPowerSeries.expand, subst, X]

theorem expand_C (r : R) : expand p hp (C r : PowerSeries R) = C r := by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

theorem expand_mul_eq_comp (q : ℕ) (hq : q ≠ 0) :
    expand (p * q) (p.mul_ne_zero hp hq) = (expand p hp (R := R)).comp (expand q hq) := by
  ext1 i
  simp [expand, MvPowerSeries.expand_mul_eq_comp p hp q hq]

theorem expand_mul (q : ℕ) (hq : q ≠ 0) (φ : PowerSeries R) :
    φ.expand (p * q) (p.mul_ne_zero hp hq) = (φ.expand q hq).expand p hp :=
  DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ

@[simp]
theorem expand_X : expand p hp (X (R := R)) = X ^ p :=
  substAlgHom_X (HasSubst.X_pow hp)

@[simp]
theorem expand_monomial (d : ℕ) (r : R) :
    expand p hp (monomial d r) = monomial (p * d) r := by
  simp [expand, monomial, MvPowerSeries.expand_monomial]

@[simp]
theorem expand_one : expand 1 one_ne_zero = AlgHom.id R (PowerSeries R) := by
  simp [expand]

theorem expand_one_apply (f : PowerSeries R) : expand 1 one_ne_zero f = f := by simp

@[simp]
theorem map_expand (f : R →+* S) (φ : PowerSeries R) :
    map f (expand p hp φ) = expand p hp (map f φ) := by
  simp [map, expand, MvPowerSeries.map_expand]

/- TODO : In the original file of multi variate polynomial, there are two theorem about rename
here, but we don't have rename for multi variate power series. And for `eval₂Hom`, `eval₂`
and `aevel`, the expression does't look good. -/

variable (q : ℕ) (hq : 0 < q)

@[simp]
theorem coeff_expand_mul (φ : PowerSeries R) (m : ℕ) :
    (expand p hp φ).coeff (p * m) = φ.coeff m := by
  rw [coeff, coeff, expand, ← smul_eq_mul, ← Finsupp.smul_single, MvPowerSeries.coeff_expand_smul]

theorem coeff_expand_of_not_dvd (φ : PowerSeries R) {m : ℕ} (h : ¬ p ∣ m) :
    (expand p hp φ).coeff m = 0 := by
  rw [coeff, expand, MvPowerSeries.coeff_expand_of_not_dvd (i := ())]
  simpa

theorem support_expand_subset (φ : PowerSeries R) :
    (expand p hp φ).support ⊆ φ.support.image (p • ·) := by
  rw [expand, MvPowerSeries.support_expand]

theorem support_expand (φ : PowerSeries R) :
    (expand p hp φ).support = φ.support.image (p • ·) := by
  rw [expand, MvPowerSeries.support_expand]

end PowerSeries
