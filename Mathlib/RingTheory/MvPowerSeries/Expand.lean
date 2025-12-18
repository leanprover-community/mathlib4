/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
## Expand multivariate power series

Given a multivariate power series `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some nonzero natural number `n`.
This operation is called `MvPowerSeries.expand` and it is an algebra homomorphism.

### Main declaration

* `MvPowerSeries.expand`: expand a multi variate power series by a factor of p, so `∑ aₙ xⁿ`
becomes `∑ aₙ xⁿᵖ`.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ τ R S : Type*} [Finite σ] [Finite τ] [CommRing R] [CommRing S] (p : ℕ) (hp : p ≠ 0)

/-- Expand the power series by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `PowerSeries.expand`. -/
noncomputable def expand : MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R :=
  substAlgHom (HasSubst.X_pow hp)

theorem expand_C (r : R) : expand p hp (C r : MvPowerSeries σ R) = C r := by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

@[simp]
theorem expand_X (i : σ) : expand p hp (X i : MvPowerSeries σ R) = X i ^ p :=
  substAlgHom_X (HasSubst.X_pow hp) i

@[simp]
theorem expand_monomial (d : σ →₀ ℕ) (r : R) :
    expand p hp (monomial d r) = monomial (p • d) r := by
  rw [expand, substAlgHom_monomial (HasSubst.X_pow hp), monomial_eq', Finsupp.prod,
    Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul, algebraMap_apply, Algebra.algebraMap_self]
  · simp

@[simp]
theorem expand_one : expand 1 one_ne_zero = AlgHom.id R (MvPowerSeries σ R) := by
  ext1 i
  simp [expand, subst_self]

theorem expand_one_apply (f : MvPowerSeries σ R) : expand 1 one_ne_zero f = f := by simp

@[simp]
theorem map_expand (f : R →+* S) (φ : MvPowerSeries σ R) :
    map f (expand p hp φ) = expand p hp (map f φ) := by
  simp [expand, map_subst (HasSubst.X_pow hp)]

section

omit [Finite σ]
theorem HasSubst.expand {f : σ → MvPowerSeries τ S} (hf : HasSubst f) :
    HasSubst fun i ↦ expand p hp (f i) := comp hf (HasSubst.X_pow hp)

theorem expand_comp_substAlgHom {f : σ → MvPowerSeries τ S} (hf : HasSubst f) :
    (expand p hp).comp (substAlgHom hf) = substAlgHom (HasSubst.expand p hp hf) := by
  ext1 i
  simp [expand, subst_comp_subst_apply hf (HasSubst.X_pow hp)]

theorem expand_substAlgHom {f : σ → MvPowerSeries τ S} (hf : HasSubst f) {φ : MvPowerSeries σ S} :
    expand p hp (substAlgHom hf φ) = substAlgHom (HasSubst.expand p hp hf) φ := by
  rw [← AlgHom.comp_apply, expand_comp_substAlgHom]

end

/- TODO : In the original file of multi variate polynomial, there are two theorem about rename
here, but we don't have rename for multi variate power series. And for `eval₂Hom`, `eval₂`
and `aevel`, the expression does't look good. -/

variable (q : ℕ) (hq : q ≠ 0)

theorem expand_mul_eq_comp :
    expand (σ := σ) (R := R) (p * q) (p.mul_ne_zero hp hq) = (expand p hp).comp (expand q hq) := by
  ext1 i
  simp [expand, pow_mul, subst_comp_subst_apply (HasSubst.X_pow hq) (HasSubst.X_pow hp),
    subst_pow (HasSubst.X_pow hp), subst_X (HasSubst.X_pow hp)]

theorem expand_mul (φ : MvPowerSeries σ R) : φ.expand (p * q) (p.mul_ne_zero hp hq) =
    (φ.expand q hq).expand p hp :=
  DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ

@[simp]
theorem coeff_expand_smul (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    (expand p hp φ).coeff (p • m) = φ.coeff m := by
  classical
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp), smul_eq_mul]
  have {d : σ →₀ ℕ} : (d.prod fun s e ↦ (X s (R := R) ^ p) ^ e) = monomial (p • d) 1 := by
    simp [monomial_smul_eq]
  rw [finsum_eq_single _ m]
  · rw [this, coeff_monomial, if_pos rfl, mul_one]
  · intro d hd
    rw [this, coeff_monomial, if_neg _, mul_zero]
    simp [nsmul_right_inj hp, hd.symm]

theorem coeff_expand_of_not_dvd (φ : MvPowerSeries σ R) {m : σ →₀ ℕ} {i : σ} (h : ¬ p ∣ m i) :
    (expand p hp φ).coeff m = 0 := by
  classical
  contrapose! h
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp)] at h
  have : ∃ (d : σ →₀ ℕ), (coeff m) (d.prod fun s e ↦ ((X s (R := R)) ^ p) ^ e) ≠ 0 := by
    by_contra! hc
    rw [finsum_eq_zero_of_forall_eq_zero fun d => by simp [hc d]] at h
    contradiction
  obtain ⟨d, hd⟩ := this
  have : (d.prod fun s e ↦ ((X s (R := R)) ^ p) ^ e) = monomial (p • d) 1 := by
    simp [monomial_smul_eq]
  rw [this, coeff_monomial] at hd
  have meq : m = p • d := by
    by_contra hc
    rw [if_neg hc] at hd
    contradiction
  simp [meq]

theorem support_expand_subset (φ : MvPowerSeries σ R) :
    (expand p hp φ).support ⊆ φ.support.image (p • ·) := by
  intro d hd
  have : ∀ i, p ∣ d i := fun _ => by_contra fun hc => hd (coeff_expand_of_not_dvd p hp φ hc)
  letI m := d.mapRange (fun n => n / p) (Nat.zero_div p)
  have eq_aux : p • m = d := (Finsupp.ext fun a => Nat.eq_mul_of_div_eq_right (this a) rfl).symm
  rw [Function.mem_support, ← eq_aux, ← coeff_apply (expand p hp φ), coeff_expand_smul,
    coeff_apply] at hd
  exact ⟨m, hd, eq_aux⟩

theorem support_expand (φ : MvPowerSeries σ R) :
    (expand p hp φ).support = φ.support.image (p • ·) := by
  classical
  refine (support_expand_subset p hp φ).antisymm ?_
  intro d hd
  obtain ⟨n, hn₁, hn₂⟩ := hd
  simp only [← hn₂, Function.mem_support]
  by_contra hc
  rw [Function.mem_support, ← coeff_apply φ, ← coeff_expand_smul p hp, coeff_apply, hc] at hn₁
  contradiction

end MvPowerSeries
