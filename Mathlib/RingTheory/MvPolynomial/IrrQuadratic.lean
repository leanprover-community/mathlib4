/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.Algebra.MvPolynomial.Nilpotent

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

## TODO

* Prove, over a field, that a polynomial of degree at most 2 whose quadratic
  part has rank at least 3 is irreducible.

* Cases of ranks 1 and 2 can be treated as well, but the answer depends
  on the terms of degree 0 and 1.
  Eg, $X^2-Y$ is irreducible, but $X^2$, $X^2-1$, $X^2-Y^2$, $X^2-Y$ are not.
  And $X^2+Y^2$ is irreducible over the reals but not over the complex numbers.

-/

@[expose] public section

namespace MvPolynomial

open scoped Polynomial

section
/-! ## The quadratic polynomial $$\sum_{i=1}^n X_i Y_i$$. -/

open Polynomial

variable (n : Type*) (R : Type*) [CommRing R]

/-- The quadratic polynomial $$\sum_{i=1}^n X_i Y_i$$. -/
noncomputable def sum_X_mul_Y : MvPolynomial (n ⊕ n) R :=
  ∑ᶠ i, X (.inl i) * X (.inr i)

lemma sum_X_mul_Y_eq_sum [Fintype n] :
    sum_X_mul_Y n R = ∑ i, X (.inl i) * X (.inr i) := by
  rw [sum_X_mul_Y, finsum_eq_sum_of_fintype]

theorem irreducible_sum_X_mul_Y [Finite n] [Nontrivial n] [IsDomain R] :
    Irreducible (sum_X_mul_Y n R) := by
  have : DecidableEq n := Classical.typeDecidableEq n
  have : Fintype n := Fintype.ofFinite n
  let p := ∑ x : n, X (R := MvPolynomial n R) x * C ( (X (R := R) x))
  suffices Irreducible p by
    rw [← MulEquiv.irreducible_iff (sumRingEquiv R n n)]
    simpa [sum_X_mul_Y_eq_sum, sumRingEquiv]
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  set S := MvPolynomial { x // x ≠ i } (MvPolynomial n R)
  set f : MvPolynomial n (MvPolynomial n R) ≃ₐ[R] S[X] :=
    ((renameEquiv (MvPolynomial n R) (Equiv.optionSubtypeNe i).symm).trans
      (MvPolynomial.optionEquivLeft _ _)).restrictScalars R with hf
  have hfXi : f (MvPolynomial.X i) = Polynomial.X := by
    rw [hf, AlgEquiv.restrictScalars_apply]
    simp [optionEquivLeft_apply]
  have hfX (x : {x : n // x ≠ i}) : f (MvPolynomial.X x) =
      Polynomial.C (MvPolynomial.X x) := by
    rw [hf, AlgEquiv.restrictScalars_apply]
    simp [optionEquivLeft_apply, dif_neg x.prop]
  have hfCX (x : n) : f (C (X x)) = Polynomial.C (C (X x)) := by
    rw [hf, AlgEquiv.restrictScalars_apply]
    simp [optionEquivLeft_apply]
  rw [← MulEquiv.irreducible_iff f]
  let a : S := C (X (R := R) i)
  let b : S := ∑ x : { x : n // x ≠ i},
    (X (R := R) (x : n)) • X (R := MvPolynomial n R) x
  suffices f p = a • Polynomial.X + Polynomial.C b  by
    rw [this]
    apply irreducible_smul_X_add_C
    · intro ha
      simp only [ne_eq, a] at ha
      rw [C_eq_zero] at ha
      exact X_ne_zero i ha
    · intro c hca hcb
      simp only [a] at hca
      rw [dvd_C_iff_exists (X_ne_zero i)] at hca
      obtain ⟨c, hc, rfl⟩ := hca
      apply IsUnit.map
      rw [dvd_X_iff_exists] at hc
      obtain ⟨r, hr, hc | hc⟩ := hc <;>
        have hr' : IsUnit (C (σ := n) r) := IsUnit.map C hr
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
    simp only [ne_eq, map_mul, hfX, hfCX]
    rw [smul_eq_C_mul, map_mul, mul_comm]

variable {n R}

/-- The quadratic polynomial $$\sum_{i=1}^n c_i X_i Y_i$$. -/
noncomputable def sum_smul_X_mul_Y (c : n → R) :
    MvPolynomial (n ⊕ n) R :=
  ∑ᶠ i, c i • X (.inl i) * X (.inr i)

variable (c : n → R)

lemma sum_smul_X_mul_Y_eq_sum [Fintype n] :
    sum_smul_X_mul_Y c = ∑ i, c i • X (.inl i) * X (.inr i) := by
  rw [sum_smul_X_mul_Y, finsum_eq_sum_of_fintype]

theorem irreducible_sum_smul_X_mul_Y [Finite n] [Nontrivial n] [IsDomain R]
    (hc : ∀ i, c i ≠ 0) :
    Irreducible (sum_smul_X_mul_Y c) := by
  have : DecidableEq n := Classical.typeDecidableEq n
  have : Fintype n := Fintype.ofFinite n
  let p := ∑ x : n, X x * C ( c x • X (R := R) x)
  suffices Irreducible p by
    rw [← MulEquiv.irreducible_iff (sumRingEquiv R n n)]
    convert this
    simp only [sumRingEquiv, sum_smul_X_mul_Y_eq_sum, smul_eq_C_mul, map_sum,
      mvPolynomialEquivMvPolynomial_apply, map_mul, sumToIter_C, sumToIter_Xl, sumToIter_Xr,
      p]
    congr
    ext1 i
    ring
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  set S := MvPolynomial { x // x ≠ i } (MvPolynomial n R)
  set f : MvPolynomial n (MvPolynomial n R) ≃ₐ[R] S[X] :=
    ((renameEquiv (MvPolynomial n R) (Equiv.optionSubtypeNe i).symm).trans
      (MvPolynomial.optionEquivLeft _ _)).restrictScalars R with hf
  have hfXi : f (MvPolynomial.X i) = Polynomial.X := by
    rw [hf, AlgEquiv.restrictScalars_apply]
    simp [optionEquivLeft_apply]
  have hfX (x : {x : n // x ≠ i}) : f (MvPolynomial.X x) =
      Polynomial.C (MvPolynomial.X x) := by
    rw [hf, AlgEquiv.restrictScalars_apply]
    simp [optionEquivLeft_apply, dif_neg x.prop]
  have hfCX (x : n) : f (MvPolynomial.C (MvPolynomial.X x)) =
      Polynomial.C (MvPolynomial.C (MvPolynomial.X x)) := by
    rw [hf, AlgEquiv.restrictScalars_apply]
    simp [optionEquivLeft_apply]
  rw [← MulEquiv.irreducible_iff f]
  let a : S := C (c i • MvPolynomial.X (R := R) i)
  let b : S := ∑ x : { x : n // x ≠ i},
    (c x • MvPolynomial.X (R := R) (x : n)) • X (R := MvPolynomial n R) x
  suffices f p = a • Polynomial.X + Polynomial.C b  by
    rw [this]
    apply irreducible_smul_X_add_C
    · intro ha
      apply hc i
      simp only [ne_eq, a] at ha
      rw [MvPolynomial.C_eq_zero] at ha
      simpa only [smul_eq_zero, X_ne_zero, or_false] using ha
    · intro s hsa hsb
      simp only [a] at hsa
      rw [dvd_C_iff_exists ?_] at hsa
      obtain ⟨t, ht, rfl⟩ := hsa
      apply IsUnit.map
      rw [MvPolynomial.dvd_smul_X_iff_exists ?_] at ht
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
    simp only [ne_eq, map_mul, hfX, hfCX]
    rw [MvPolynomial.smul_eq_C_mul, map_mul, mul_comm]


end

end MvPolynomial
