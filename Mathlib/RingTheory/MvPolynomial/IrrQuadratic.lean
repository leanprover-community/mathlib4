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
# Irreducibility of linear and quadratic polynomials

* For `c : n →₀ R`, `MvPolynomial.sum_smul_X c` is the linear polynomial
  $\sum_i c_i X_i$ of $R[X_1\dots,X_n]$.

* `MvPolynomial.irreducible_sum_smul_X` : if the support of `c` is nontrivial,
  if `R` is a domain,
  and if the only common divisors to all `c i` are units,
  then `MvPolynomial.sum_smul_X c` is irreducible.

* For `c : n →₀ R`, `MvPolynomial.sum_X_mul_Y c` is the quadratic polynomial
  $\sum_i c_i X_i Y_i$ of $R[X_1\dots,X_n,Y_1,\dots,Y_n]$.
  It is constructed as an object of `MvPolynomial (n ⊕ n) R`,
  the first component of `n ⊕ n` represents the `X` indeterminates,
  and the second component represents the `Y` indeterminates.

* `MvPolynomial.irreducible_sum_smul_X_mul_Y` :
  if the support of `c` is nontrivial,
  the ring `R` is a domain,
  and the only divisors common to all `c i` are units,
  then `MvPolynomial.sum_smul_X_mul_Y c` is irreducible.

## TODO

* Treat the case of diagonal quadratic polynomials,
  $ \sum c_i X_i ^ 2$. For irreducibility, one will need that
  there are at least 3 nonzero values of `c`,
  and that the only common divisors to all `c i` are units.

* Addition of quadratic polynomial of both kinds are relevant too.

* Prove, over a field, that a polynomial of degree at most 2 whose quadratic
  part has rank at least 3 is irreducible.

* Cases of ranks 1 and 2 can be treated as well, but the answer depends
  on the terms of degree 0 and 1.
  Eg, $X^2-Y$ is irreducible, but $X^2$, $X^2-1$, $X^2-Y^2$, $X^2-Y$ are not.
  And $X^2+Y^2$ is irreducible over the reals but not over the complex numbers.

-/

@[expose] public section

theorem Function.nontrivial_of_nontrivial (α β : Type*) [Nontrivial (α → β)] :
    Nontrivial β := by
  obtain ⟨x, y, h⟩ := exists_pair_ne (α → β)
  rw [ne_eq, funext_iff, not_forall] at h
  obtain ⟨a, h⟩ := h
  exact nontrivial_of_ne _ _ h

theorem Finsupp.nontrivial_of_nontrivial (α β : Type*) [Zero β] [Nontrivial (α →₀ β)] :
    Nontrivial β := by
  obtain ⟨x, y, h⟩ := exists_pair_ne (α →₀ β)
  rw [ne_eq, Finsupp.ext_iff, not_forall] at h
  obtain ⟨a, h⟩ := h
  exact nontrivial_of_ne _ _ h

namespace MvPolynomial

open scoped Polynomial

section
/-! ## The quadratic polynomial $$\sum_{i=1}^n X_i Y_i$$. -/

open Polynomial

variable {n : Type*} {R : Type*} [CommRing R]

/-- The linear polynomial $$\sum_i c_i X_i$$. -/
noncomputable def sum_smul_X :
    (n →₀ R) →ₗ[R] MvPolynomial n R :=
  Finsupp.linearCombination R X

variable (c : n →₀ R)

theorem sum_smul_X_eq :
    sum_smul_X c = c.sum (fun i r ↦ r • X i) := by
  rw [sum_smul_X, Finsupp.linearCombination_apply]

@[simp] theorem coeff_zero_sum_smul_X (c : n →₀ R) :
    coeff 0 (sum_smul_X c) = 0 := by
  classical
  rw [sum_smul_X_eq, ← lcoeff_apply, map_finsuppSum]
  aesop

@[simp]
theorem coeff_single_sum_smul_X (i : n) :
    coeff (Finsupp.single i 1) (sum_smul_X c) = c i := by
  classical
  rw [sum_smul_X, Finsupp.linearCombination_apply, ← lcoeff_apply,
    map_finsuppSum, Finsupp.sum_eq_single i]
  · simp [map_smul, lcoeff_apply]
  · intro j _ hj
    rw [map_smul, lcoeff_apply, coeff_X', if_neg, smul_zero]
    contrapose hj
    apply Finsupp.single_left_injective one_ne_zero hj
  · simp

theorem totalDegree_sum_smul_X (hc_ne_zero : c ≠ 0) :
    (sum_smul_X c).totalDegree = 1 := by
  classical
  have : Nontrivial (n →₀ R) := nontrivial_of_ne c 0 hc_ne_zero
  have : Nontrivial R := Finsupp.nontrivial_of_nontrivial n R
  apply le_antisymm
  · rw [sum_smul_X_eq, Finsupp.sum]
    apply totalDegree_finsetSum_le
    simp [le_trans (totalDegree_smul_le _ _)]
  · rw [Nat.one_le_iff_ne_zero, ne_eq, totalDegree_eq_zero_iff_eq_C,
      coeff_zero_sum_smul_X, map_zero]
    intro h
    apply hc_ne_zero
    ext i
    rw [← coeff_single_sum_smul_X]
    simp [h]

variable (R) in
/-- The isomorphism from multivariate polynomials in `n` indeterminates to
polynomials with coefficients in `n - 1` indeterminates. -/
private noncomputable
def φ [DecidableEq n] (i : n) :
    MvPolynomial n R ≃ₐ[R] (MvPolynomial {x // x ≠ i} R)[X] :=
  (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft R {x // x ≠ i})

private
theorem φ_X_self (i : n) [DecidableEq n] :
    φ R i (X i) = Polynomial.X := by
  simp only [φ, ne_eq, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    Equiv.optionSubtypeNe_symm_apply, ↓reduceDIte]
  apply optionEquivLeft_X_none

private
theorem φ_X_of_ne [DecidableEq n] {i j : n} (hj : j ≠ i) :
    φ R i (X j) = Polynomial.C (X ⟨j, hj⟩) := by
  simp only [φ, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_X, Equiv.optionSubtypeNe_symm_apply]
  rw [dif_neg hj, optionEquivLeft_X_some]

private
theorem φ_sum_smul_X_eq [DecidableEq n] (i : n) :
    φ R i (sum_smul_X c) = c i • Polynomial.X +
      Polynomial.C (sum_smul_X (c.subtypeDomain (fun x ↦ x ≠ i))) := by
  simp only [sum_smul_X_eq, Finsupp.sum]
  rw [Finset.sum_subset (s₂ := insert i c.support)
    (Finset.subset_insert i c.support) (fun x _ hx' ↦ by aesop)]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_insert_self i c.support),
    map_add, map_smul, φ_X_self, add_right_inj]
  rw [map_sum]
  rw [Finset.sum_bij'
    (f := fun x ↦ φ R i (c x • X x))
    (g := fun y : {x : n // x ≠ i} ↦ Polynomial.C (c (y : n) • X (R := R) y))
    (i := fun x hx ↦ (⟨x, And.right (by simpa using hx)⟩ : {x // x ≠ i}))
    (j := fun y hy ↦ y)]
  pick_goal 6
  · intro j hj
    simp only [ne_eq, map_smul]
    rw [φ_X_of_ne (And.right (by simpa using hj)),
      MvPolynomial.smul_eq_C_mul, map_mul]
    simp [Algebra.smul_def]
  all_goals aesop

theorem X_dvd_sum_smul_X_iff (i : n) :
    X i ∣ sum_smul_X c ↔ c.support ⊆ {i} := by
  refine ⟨fun h_dvd ↦ ?_, fun hci ↦ ?_⟩
  · by_contra hci
    classical
    have : ∃ j, c j ≠ 0 ∧ j ≠ i := by
      simpa [Finset.subset_iff] using hci
    obtain ⟨j, hj, hji⟩ := this
    apply hj
    have : φ R i (X i) ∣ φ R i (sum_smul_X c) := by
      simpa using (φ R i).toRingHom.map_dvd h_dvd
    rw [φ_sum_smul_X_eq c, φ_X_self] at this
    rw [← algebraMap_smul (MvPolynomial {x // x ≠ i} R) (c i), Polynomial.smul_eq_C_mul,
        dvd_add_right (dvd_mul_left ..), Polynomial.X_dvd_iff, Polynomial.coeff_C_zero] at this
    simpa using congr(coeff (Finsupp.single ⟨j, hji⟩ 1) $this)
  · rw [sum_smul_X_eq, Finsupp.sum_eq_single i]
    · rw [smul_eq_C_mul]
      exact dvd_mul_left (X i) (C (c i))
    · intro j hj hji
      suffices c j = 0 by simp [this]
      rw [← Finsupp.notMem_support_iff]
      contrapose hji
      simpa using hci hji
    · simp

theorem irreducible_sum_smul_X [IsDomain R]
    (hc_nontrivial : c.support.Nontrivial)
    (hc_gcd : ∀ r, (∀ i, r ∣ c i) → IsUnit r) :
    Irreducible (sum_smul_X c) where
  not_isUnit h := by
    apply not_isUnit_zero (M₀ := R)
    simp [MvPolynomial.isUnit_iff_totalDegree_of_isReduced] at h
  isUnit_or_isUnit p q hpq := by
    wlog hp : p.totalDegree ≤ q.totalDegree generalizing p q hpq
    · rw [mul_comm] at hpq
      rw [or_comm]
      exact this q p hpq (Nat.le_of_not_le hp)
    have hpq' := congr(MvPolynomial.totalDegree $hpq)
    rw [totalDegree_sum_smul_X c ?_, eq_comm, totalDegree_mul_of_isDomain,
      Nat.add_eq_one_iff] at hpq'
    · rcases hpq' with (h | h)
      · left
        rw [totalDegree_eq_zero_iff_eq_C] at h
        rw [h.1]
        apply IsUnit.map
        apply hc_gcd (coeff 0 p)
        intro i
        rw [← coeff_single_sum_smul_X c i, hpq]
        nth_rewrite 2 [h.1]
        simp
      · exfalso
        simp [h.1, h.2] at hp
    all_goals aesop

/-- The quadratic polynomial $$\sum_i c_i X_i Y_i$$. -/
noncomputable def sum_smul_X_mul_Y :
    (n →₀ R) →ₗ[R] MvPolynomial (n ⊕ n) R :=
  Finsupp.linearCombination R (fun i ↦ X (.inl i) * X (.inr i))

variable (c : n →₀ R)

lemma sum_smul_X_mul_Y_eq :
    sum_smul_X_mul_Y c = c.sum fun i a ↦ a • X (.inl i) * X (.inr i) := by
  simp [sum_smul_X_mul_Y, Finsupp.linearCombination_apply]

theorem irreducible_sum_smul_X_mul_Y [IsDomain R]
    (hc : c.support.Nontrivial)
    (h_dvd : ∀ r, (∀ i, r ∣ c i) → IsUnit r) :
    Irreducible (sum_smul_X_mul_Y c) := by
  classical
  let d : n →₀ MvPolynomial n R :=
  { toFun i := c i • X i
    support := c.support
    mem_support_toFun i := by aesop }
  let h := sumRingEquiv R n n
  suffices h (sum_smul_X_mul_Y c) = sum_smul_X d by
    rw [← MulEquiv.irreducible_iff (sumRingEquiv R n n)]
    rw [this]
    refine irreducible_sum_smul_X d hc ?_
    intro r hr
    simp only [Finsupp.coe_mk, d] at hr
    suffices r.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      rw [this]
      apply IsUnit.map C
      apply h_dvd
      intro i
      obtain ⟨p, hp⟩ := hr i
      replace hp := congr(coeff (Finsupp.single i 1) $hp)
      rw [this] at hp
      exact ⟨coeff (Finsupp.single i 1) p, by simpa using hp⟩
    suffices ∃ i ∈ c.support, r ∣ C (c i) by
      obtain ⟨i, hi, hri⟩ := this
      rw [← Nat.le_zero]
      convert totalDegree_le_of_dvd_of_isDomain hri ?_
      · simp
      · simpa using hi
    by_contra! hr'
    obtain ⟨i, hi : i ∈ c.support, j, hj : j ∈ c.support, hij⟩ := hc
    have hri := hr i
    simp only [smul_eq_C_mul, mul_comm, dvd_X_mul_iff] at hri
    obtain ⟨⟨s, hrs⟩, hrs'⟩ := Or.resolve_left hri (hr' i hi)
    have hrj := hr j
    simp only [smul_eq_C_mul, mul_comm, hrs] at hrj
    obtain ⟨t, ht⟩ := hrj
    rw [mul_assoc, mul_comm s, mul_assoc] at ht
    have : X i ∣ X j * (C (c j)) :=
      dvd_of_mul_right_eq (t * s) ht.symm
    rw [dvd_X_mul_iff] at this
    rcases this with (this | this)
    · obtain ⟨u, hu⟩ := this
      have : X i ∣ C (c j) := dvd_of_mul_right_eq u hu.symm
      rw [Finsupp.mem_support_iff] at hj
      rw [dvd_C_iff_exists hj] at this
      obtain ⟨u, ⟨v, huv⟩, this⟩ := this
      apply hj
      rw [huv]
      convert zero_mul _
      simpa using congr(coeff 0 $this.symm)
    · apply hij
      exact (X_dvd_X.mp this.1).symm
  simp only [sum_smul_X_mul_Y_eq, sum_smul_X_eq, map_finsuppSum]
  rw [Finsupp.sum, Finsupp.sum]
  rw [Finset.sum_congr rfl]
  intro i _
  simp [h, d, sumRingEquiv, Algebra.smul_def, mul_assoc,
    mul_comm (X i) (C _)]

end

end MvPolynomial
