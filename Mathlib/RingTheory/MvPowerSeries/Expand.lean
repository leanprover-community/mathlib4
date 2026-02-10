/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.Expand

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

theorem expand_subst {f : σ → MvPowerSeries τ R} (hf : HasSubst f) {φ : MvPowerSeries σ R} :
    expand p hp (subst f φ) = subst (fun i ↦ (f i).expand p hp) φ := by
  rw [← substAlgHom_apply hf, expand_substAlgHom, substAlgHom_apply]

end

/- TODO : In the original file of `MvPolynomial`, there are two theorems about `rename`
here, but we don't have `rename` for `MvPowerSeries`. And for `eval₂Hom`, `eval₂`
and `aeval`, the expression doesn't look good. -/

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

@[simp]
theorem constantCoeff_expand (φ : MvPowerSeries σ R) :
    (φ.expand p hp).constantCoeff = φ.constantCoeff := by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← smul_zero p, coeff_expand_smul]
  simp

theorem coeff_expand_of_not_dvd (φ : MvPowerSeries σ R) {m : σ →₀ ℕ} {i : σ} (h : ¬ p ∣ m i) :
    (expand p hp φ).coeff m = 0 := by
  classical
  contrapose! h
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp)] at h
  obtain ⟨d, hd⟩ : ∃ (d : σ →₀ ℕ), (coeff m) (d.prod fun s e ↦ ((X s (R := R)) ^ p) ^ e) ≠ 0 := by
    by_contra! hc
    rw [finsum_eq_zero_of_forall_eq_zero fun d => by simp [hc d]] at h
    contradiction
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

@[simp]
theorem order_expand (φ : MvPowerSeries σ R) :
    (φ.expand p hp).order = p • φ.order := by
  by_cases! hφ : φ = 0
  · simpa [hφ] using (ENat.mul_top (by norm_cast)).symm
  · apply eq_of_le_of_ge
    · obtain ⟨d, hd₁, hd₂⟩ := exists_coeff_ne_zero_and_order (ne_zero_iff_order_finite.mp hφ)
      have : p • φ.order = (p • d).degree := by simp [← hd₂]
      rw [this]
      exact order_le <| (coeff_expand_smul p hp φ _) ▸ hd₁
    · refine MvPowerSeries.le_order fun d hd => ?_
      by_cases! h : ∀ i, p ∣ d i
      · obtain ⟨m, hm⟩ : ∃ m, d = p • m := ⟨Finsupp.equivFunOnFinite.symm fun i => d i / p,
          by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
        rw [hm, coeff_expand_smul, coeff_of_lt_order]
        simp only [hm, map_nsmul, smul_eq_mul, Nat.cast_mul, nsmul_eq_mul] at hd
        exact lt_of_mul_lt_mul_left' hd
      · obtain ⟨i, hi⟩ := h
        exact coeff_expand_of_not_dvd p hp φ hi

section MvPolynomial

/-- For any multivariate polynomial `φ`, then `MvPolynomial.expand p φ` and
`MvPowerSeries.expand p hp ↑φ` coincide. -/
@[simp]
theorem expand_eq_expand {φ : MvPolynomial σ R} :
    expand p hp (↑φ) = (φ.expand p : MvPowerSeries σ R) := by
  ext n
  simp only [MvPolynomial.coeff_coe]
  by_cases! h : ∀ i, p ∣ n i
  · obtain ⟨m, hm⟩ : ∃ m, n = p • m :=
      ⟨Finsupp.equivFunOnFinite.symm fun i => n i / p, by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [hm, coeff_expand_smul p hp _ _, φ.coeff_expand_smul _ hp, φ.coeff_coe]
  · obtain ⟨i, hi⟩ := h
    rw [coeff_expand_of_not_dvd p hp _ hi, MvPolynomial.coeff_expand_of_not_dvd _ hi]

theorem trunc'_expand [DecidableEq σ] {n : σ →₀ ℕ} (φ : MvPowerSeries σ R) :
    trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p := by
  ext d
  by_cases! h : ∀ i, p ∣ d i
  · obtain ⟨m, hm⟩ : ∃ m, d = p • m := ⟨Finsupp.equivFunOnFinite.symm fun i => d i / p,
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    by_cases! h_le : m ≤ n
    · rw [hm, coeff_trunc', if_pos (nsmul_le_nsmul_right h_le p), coeff_expand_smul,
        MvPolynomial.coeff_expand_smul _ hp, coeff_trunc', if_pos h_le]
    · have not_le : ¬ p • m ≤ p • n := by
        obtain ⟨i, hi⟩ : ∃ i, m i > n i := by
          by_contra! hc
          exact h_le (Finsupp.coe_le_coe.mp hc)
        have : ¬ p • m i ≤ p • n i := by
          simp [Nat.mul_lt_mul_of_pos_left hi (p.ne_zero_iff_zero_lt.mp hp)]
        exact Not.intro fun a ↦ this (a i)
      rw [coeff_trunc', hm, if_neg not_le, MvPolynomial.coeff_expand_smul _ hp, coeff_trunc',
        if_neg h_le]
  · obtain ⟨i, hi⟩ := h
    rw [MvPolynomial.coeff_expand_of_not_dvd _ hi]
    by_cases! hd : d ≤ p • n
    · rw [coeff_trunc', if_pos hd, coeff_expand_of_not_dvd _ hp _ hi]
    rw [coeff_trunc', if_neg hd]

include hp in
theorem trunc'_expand_trunc' {n m : σ →₀ ℕ} (h : n ≤ m) [DecidableEq σ] (f : MvPowerSeries σ R) :
    (MvPolynomial.expand p) (trunc' R n f) = (trunc' R (p • n))
    ↑((MvPolynomial.expand p) (trunc' R m f)) := by
  rw [← expand_eq_expand p hp, trunc'_expand, ← trunc'_trunc' h]

end MvPolynomial

section ExpChar

variable [ExpChar R p]

theorem map_frobenius_expand {f : MvPowerSeries σ R} :
    (f.expand p hp).map (frobenius R p) = f ^ p := by
  classical
  rw [eq_iff_frequently_trunc'_eq, Filter.frequently_atTop]
  intro n
  use (p • n)
  refine ⟨le_self_nsmul (zero_le n) hp, ?_⟩
  · have : (((trunc' R (p • n) f).expand p).map (frobenius R p)).toMvPowerSeries =
      MvPowerSeries.map (frobenius R p) ((trunc' R (p • n) f).expand p) := by
      simp only [MvPolynomial.map_expand, ← expand_eq_expand p hp, map_expand]
      congr
      ext m
      simp only [MvPolynomial.coeff_coe, MvPolynomial.coeff_map, coeff_map]
    rw [trunc'_map, trunc'_expand, ← trunc'_trunc'_pow (Nat.one_le_iff_ne_zero.mpr
      (expChar_ne_zero R p)), ← MvPolynomial.coe_pow p, ← MvPolynomial.map_frobenius_expand, this,
        trunc'_map, trunc'_expand_trunc' p hp (le_self_nsmul (zero_le n) hp)]

theorem map_iterateFrobenius_expand (f : MvPowerSeries σ R) (n : ℕ) :
    map (iterateFrobenius R p n) (expand (p ^ n) (pow_ne_zero n hp) f) = f ^ p ^ n := by
  induction n with
  | zero => simp [map_id]
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p hp, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

end ExpChar

end MvPowerSeries
