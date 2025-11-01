/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-!
# Irreducibility of quadratic polynomials

* `MvPolynomial.sum_X_mul_Y n R` is the polynomial
$\sum_{i=1}^n X_i Y_i$ of $R[X_1\dots,X_n,Y_1,\dots,Y_n]$.
It is constructed as an object of `MvPolynomial (n ⊕ n) R`,
where `n` is a finite type,
the first component of `n ⊕ n` represents the `X` indeterminates,
and the second component represents the `Y` indeterminates.

* `MvPolynomial.irreducible_sum_X_mul_Y` : if `n` is nontrivial and `R` is a domain,
then `MVPolynomial.quadratic n R` is irreducible.

-/

-- TODO: exists? move elsewhere.
/-- The equivalence between a type and the `Option` type
of the type deprived of one given element. -/
noncomputable def equiv_option {n : Type*} [DecidableEq n] (i : n) :
    n ≃ Option {x : n // x ≠ i} where
  toFun x := if hx : x = i then none else some ⟨x, hx⟩
  invFun y := Option.elim y i (fun x ↦ ↑x)
  left_inv x := by
    by_cases hx : x = i <;> simp [hx]
  right_inv y :=  by
    cases y with
    | none => simp
    | some x => simp [x.prop]

namespace MvPolynomial

open scoped Polynomial

section
/-! ## Divisibility properties -/

variable {σ R : Type*} [CommRing R] [IsCancelMulZero R]

theorem dvd_C_iff_exists
    {σ : Type*} {a : R} (ha : a ≠ 0) {p : MvPolynomial σ R} :
    p ∣ MvPolynomial.C a ↔ ∃ b, b ∣ a ∧ p = MvPolynomial.C b := by
  constructor
  · intro hp
    use MvPolynomial.coeff 0 p
    suffices p.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      refine ⟨?_, this⟩
      rw [this, MvPolynomial.C_dvd_iff_dvd_coeff] at hp
      convert hp 0
      simp
    apply Nat.eq_zero_of_le_zero
    convert totalDegree_le_of_dvd_of_isDomain hp (by simp [ha])
    simp
  · rintro ⟨b, hab, rfl⟩
    exact _root_.map_dvd MvPolynomial.C hab

theorem dvd_X_iff_exists [Nontrivial R]
    {σ : Type*} {i : σ} {p : MvPolynomial σ R} :
    p ∣ X i ↔ ∃ r, IsUnit r ∧ (p = C r ∨ p = r • (X i)) := by
  constructor
  · rintro ⟨q, hq⟩
    have : totalDegree p + totalDegree q = 1 := by
      rw [← totalDegree_mul_of_isDomain, ← hq]
      · simp only [totalDegree_X]
      · intro h; simp [h] at hq
      · intro h; simp [h] at hq
    rw [Nat.add_eq_one_iff] at this
    rcases this with h01 | h10
    · rw [totalDegree_eq_zero_iff_eq_C] at h01
      refine ⟨coeff 0 p, ?_, Or.inl h01.1⟩
      rw [h01.1] at hq
      replace hq := congr_arg (fun f ↦ coeff (Finsupp.single i 1) f) hq
      simp only [coeff_X, coeff_C_mul] at hq
      exact isUnit_of_mul_eq_one _ _ hq.symm
    · rw [totalDegree_eq_zero_iff_eq_C] at h10
      have : IsUnit (coeff 0 q) := by
        replace hq := congr_arg (fun f ↦ coeff (Finsupp.single i 1) f) hq
        simp only at hq
        rw [h10.2, mul_comm] at hq
        simp only [coeff_X, coeff_C_mul] at hq
        exact isUnit_of_mul_eq_one _ _ hq.symm
      set u := this.unit
      have h : q = C (u : R) := by rw [h10.2]; simp [u]
      refine ⟨(u⁻¹ : Rˣ), Units.isUnit _, ?_⟩
      right
      rw [smul_eq_C_mul, hq, mul_comm p q, h, ← mul_assoc,
        ← map_mul]
      simp
  · rintro ⟨r, hr, hp⟩
    rcases hp with hp | hp
    · rw [hp, ← (hr.map _).unit_spec]
      exact Units.coe_dvd
    · rw [hp, smul_eq_C_mul, ← (hr.map _).unit_spec, Units.mul_left_dvd]

-- TODO: generalize to monomials

end

section
/-! ## The quadratic polynomia $$\sum_{i=1}^n X_i Y_i$$. -/

open Polynomial

variable (n : Type*) [Fintype n] (R : Type*) [CommRing R] [IsDomain R]

/-- The quadratic polynomial $$\sum_{i=1}^n X_i Y_i$$. -/
noncomputable def sum_X_mul_Y : MvPolynomial (n ⊕ n) R :=
  ∑ i : n, MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr i)

theorem irreducible_sum_X_mul_Y (h : Nontrivial n) :
    Irreducible (sum_X_mul_Y n R) := by
  classical
  let p := ∑ x : n,
    MvPolynomial.X (R := MvPolynomial n R) x * MvPolynomial.C ( (MvPolynomial.X (R := R) x))
  let e := sumRingEquiv R n n
  have : e (sum_X_mul_Y n R) = p := by simp [e, p, sum_X_mul_Y, sumRingEquiv]
  rw [← MulEquiv.irreducible_iff e, this]
  obtain ⟨i, j, hij⟩ := h
  set S := MvPolynomial { x // x ≠ i } (MvPolynomial n R)
  let f : MvPolynomial n (MvPolynomial n R) ≃ₐ[R] S[X] :=
    ((renameEquiv (MvPolynomial n R) (equiv_option i)).trans
      (MvPolynomial.optionEquivLeft _ _)).restrictScalars R
  have hfXi : f (MvPolynomial.X i) = Polynomial.X := by
    simp only [f]
    rw [AlgEquiv.restrictScalars_apply]
    simp [equiv_option, optionEquivLeft_apply]
  have hfX (x : {x : n // x ≠ i}) : f (MvPolynomial.X x) =
      Polynomial.C (MvPolynomial.X x) := by
    simp only [f]
    rw [AlgEquiv.restrictScalars_apply]
    simp [equiv_option, optionEquivLeft_apply, dif_neg x.prop]
  have hfCX (x : n) : f (MvPolynomial.C (MvPolynomial.X x)) =
      Polynomial.C (MvPolynomial.C (MvPolynomial.X x)) := by
    simp only [f]
    rw [AlgEquiv.restrictScalars_apply]
    simp [equiv_option, optionEquivLeft_apply]
  rw [← MulEquiv.irreducible_iff f]
  let a : S := C (MvPolynomial.X (R := R) i)
  let b : S := ∑ x : { x : n // x ≠ i},
    (MvPolynomial.X (R := R) (x : n)) • X (R := MvPolynomial n R) x
  suffices f p = a • Polynomial.X + Polynomial.C b  by
    rw [this]
    apply irreducible_smul_X_add_C
    · intro ha
      simp only [ne_eq, a] at ha
      rw [MvPolynomial.C_eq_zero] at ha
      exact MvPolynomial.X_ne_zero i ha
    · intro c hca hcb
      simp only [a] at hca
      rw [dvd_C_iff_exists (MvPolynomial.X_ne_zero i)] at hca
      obtain ⟨c, hc, rfl⟩ := hca
      apply IsUnit.map
      rw [MvPolynomial.dvd_X_iff_exists] at hc
      obtain ⟨r, hr, hc | hc⟩ := hc <;>
        have hr' : IsUnit (MvPolynomial.C (σ := n) r) :=
            IsUnit.map MvPolynomial.C hr
      · simpa [hc] using hr'
      · exfalso
        apply hij
        rw [← MvPolynomial.X_dvd_X (σ := n) (R := R)]
        apply dvd_of_mul_left_dvd (a := MvPolynomial.C r)
        rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hcb
        specialize hcb (Finsupp.single ⟨j, Ne.symm hij⟩ 1)
        rw [hc, MvPolynomial.smul_eq_C_mul] at hcb
        simp only [b] at hcb
        rw [MvPolynomial.coeff_sum] at hcb
        simpa using hcb
  simp only [p]
  rw [map_sum, Fintype.sum_eq_add_sum_subtype_ne _ i]
  rw [map_sum]
  apply congr_arg₂
  · simp only [ne_eq, map_mul, a]
    rw [mul_comm, hfXi, hfCX, ← Polynomial.smul_eq_C_mul]
  · apply Fintype.sum_congr
    intro x
    simp [hfCX, hfX]
    rw [MvPolynomial.smul_eq_C_mul, map_mul, mul_comm]

end

end MvPolynomial
