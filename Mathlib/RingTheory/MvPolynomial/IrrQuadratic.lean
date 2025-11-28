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
/-! ## Divisibility properties -/

variable {σ R : Type*} [CommRing R] {p q : MvPolynomial σ R}

theorem dvd_C_iff_exists [IsCancelMulZero R] {a : R} (ha : a ≠ 0) :
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

theorem monomial_mul_eq_monomial_mul_iff
    {σ : Type*} {m : σ →₀ ℕ} {p q : MvPolynomial σ R} :
    monomial m 1 * p = monomial m 1 * q ↔ p = q := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  ext d
  simpa using congr_arg (coeff (m + d)) h

theorem X_mul_eq_X_mul_iff
    {σ : Type*} {i : σ} {p q : MvPolynomial σ R} :
    X i * p = X i * q ↔ p = q :=
  monomial_mul_eq_monomial_mul_iff (m := Finsupp.single i 1)

theorem eq_divMonomial_single
    {σ : Type*} {i : σ} {p q r : MvPolynomial σ R}
    (h : X i * q + r = p) (hr : ∀ n ∈ r.support, n i = 0) :
    q = p.divMonomial (Finsupp.single i 1) := by
  ext n
  rw [coeff_divMonomial, ← h, coeff_add, coeff_X_mul, left_eq_add, ← notMem_support_iff]
  intro hn
  simpa using hr _ hn

theorem eq_modMonomial_single
    {σ : Type*} {i : σ} {p q r : MvPolynomial σ R}
    (h : X i * q + r = p) (hr : ∀ n ∈ r.support, n i = 0) :
    r = p.modMonomial (Finsupp.single i 1) := by
  have h' := id h
  rwa [← p.divMonomial_add_modMonomial_single i,
    eq_divMonomial_single h hr, add_right_inj] at h'

theorem eq_modMonomial_single_iff
    {σ : Type*} {i : σ} {p r : MvPolynomial σ R} (h : X i ∣ p - r) :
    r = p.modMonomial (Finsupp.single i 1) ↔
      ∀ n ∈ r.support, n i = 0 := by
  refine ⟨fun h n ↦ ?_, fun hr ↦ ?_⟩
  · contrapose!
    intro hn
    rw [h, notMem_support_iff]
    apply coeff_modMonomial_of_le
    simpa [Nat.one_le_iff_ne_zero]
  · obtain ⟨q, hq⟩ := h
    apply eq_modMonomial_single (q := q) _ hr
    rw [← eq_sub_iff_add_eq, hq]

theorem X_dvd_mul_iff [IsCancelMulZero R] {i : σ} :
    X i ∣ p * q ↔ X i ∣ p ∨ X i ∣ q := by
  nontriviality R
  have _ : NoZeroDivisors (MvPolynomial σ R) :=
    IsLeftCancelMulZero.to_noZeroDivisors (MvPolynomial σ R)
  constructor
  · intro h
    suffices (p.modMonomial (Finsupp.single i 1)) * (q.modMonomial (Finsupp.single i 1)) =
          (p * q).modMonomial (Finsupp.single i 1) by
      simp only [X_dvd_iff_modMonomial_eq_zero] at h ⊢
      rwa [h, mul_eq_zero] at this
    have hp := p.modMonomial_add_divMonomial_single i
    have hq := q.modMonomial_add_divMonomial_single i
    rw [eq_modMonomial_single_iff]
    · intro n
      contrapose
      intro hn
      classical
      rw [notMem_support_iff, coeff_mul]
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_antidiagonal] at hx
      simp only [← hx, Finsupp.coe_add, Pi.add_apply, Nat.add_eq_zero_iff, not_and_or] at hn
      rcases hn with hn | hn
      · rw [coeff_modMonomial_of_le, zero_mul]
        simpa [← Nat.one_le_iff_ne_zero] using hn
      · rw [mul_comm, coeff_modMonomial_of_le, zero_mul]
        simpa [← Nat.one_le_iff_ne_zero] using hn
    · nth_rewrite 1 [← hp]
      nth_rewrite 1 [← hq]
      simp  only [add_mul, mul_add, add_assoc, add_sub_cancel_left]
      simp only [← mul_assoc, mul_comm _ (X i)]
      simp only [mul_assoc, ← mul_add (X i)]
      apply dvd_mul_right
  · intro h
    rcases h with h | h
    · exact dvd_mul_of_dvd_left h q
    · exact dvd_mul_of_dvd_right h p

theorem dvd_X_mul_iff [IsCancelMulZero R] {i : σ} :
    p ∣ X i * q ↔ p ∣ q ∨ (X i ∣ p ∧ p.divMonomial (Finsupp.single i 1) ∣ q) := by
  constructor
  · intro hp
    obtain ⟨r, hp⟩ := hp
    have := p.modMonomial_add_divMonomial_single i
    have : X i ∣ p ∨ X i ∣ r := by simp [← X_dvd_mul_iff, ← hp]
    rcases this with hip | hir
    · right
      refine ⟨hip, ?_⟩
      rw [X_dvd_iff_modMonomial_eq_zero] at hip
      rw [hip, zero_add] at this
      rw [← this, mul_assoc, X_mul_eq_X_mul_iff] at hp
      use r
    · obtain ⟨r, rfl⟩ := hir
      replace hp : q = p * r := by
        rwa [← mul_assoc, mul_comm p, mul_assoc, X_mul_eq_X_mul_iff] at hp
      left
      rw [hp]
      exact dvd_mul_right p r
  · rintro hp
    rcases hp with hp | ⟨hi, hq⟩
    · exact dvd_mul_of_dvd_right hp (X i)
    · suffices p = X i * p.divMonomial (Finsupp.single i 1) by
        rw [this]
        exact mul_dvd_mul_left (X i) hq
      conv_lhs => rw [← p.modMonomial_add_divMonomial (Finsupp.single i 1)]
      simpa only [← C_mul_X_eq_monomial, C_1, one_mul, add_eq_right,
        ← X_dvd_iff_modMonomial_eq_zero]

theorem dvd_monomial_mul_iff_exists [IsCancelMulZero R] {n : σ →₀ ℕ} :
    p ∣ monomial n 1 * q ↔ ∃ m r, m ≤ n ∧ r ∣ q ∧ p = monomial m 1 * r := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton (MvPolynomial σ R) := by
      exact Unique.instSubsingleton
    simp only [this.allEq _ p, dvd_refl, and_self, and_true, exists_const, true_iff]
    refine ⟨n, le_refl n⟩
  suffices ∀ (d) (n : σ →₀ ℕ) (hd : n.degree = d) (p q : MvPolynomial σ R),
    p ∣ monomial n 1 * q ↔ ∃ m r, m ≤ n ∧ r ∣ q ∧ p = monomial m 1 * r by
    apply this n.degree n rfl
  classical
  intro d
  induction d with
  | zero =>
    intro n hn p
    rw [Finsupp.degree_eq_zero_iff] at hn
    simp only [hn, monomial_zero', C_1, one_mul, nonpos_iff_eq_zero, exists_and_left,
      exists_eq_left, exists_eq_right', implies_true]
  | succ d hd =>
    intro n hn p q
    refine ⟨fun hp ↦ ?_, fun ⟨m, r, hmn, hrq, hp⟩ ↦ ?_⟩
    · have : n.support.Nonempty := by
        rw [Finsupp.support_nonempty_iff]
        intro hn'
        simp [hn'] at hn
      obtain ⟨i, hi⟩ := this
      let n' := n - Finsupp.single i 1
      have hn' : n' + Finsupp.single i 1 = n := by
        apply Finsupp.sub_add_single_one_cancel
        rwa [← Finsupp.mem_support_iff]
      have hnn' : n' ≤ n := by simp [← hn']
      have hd' : n'.degree = d := by
        rw [← add_left_inj, ← hn, ← hn']
        simp
      rw [← hn', monomial_add_single, pow_one, mul_comm _ (X i), mul_assoc, dvd_X_mul_iff] at hp
      rcases hp with hp | hp
      · obtain ⟨m, r, hm, hr, hp⟩ := (hd n' hd' p q).mp hp
        exact ⟨m, r, le_trans hm hnn', hr, hp⟩
      · obtain ⟨p', hp'⟩ := hp.1
        obtain ⟨m, r, hm, hr, hp⟩ := (hd n' hd' _ _).mp hp.2
        use m + Finsupp.single i 1, r, ?_, hr
        · simp [monomial_add_single, pow_one, mul_comm _ (X i), mul_assoc, ← hp,
          hp']
        · simpa [← hn'] using hm

    · rw [hp, ← add_tsub_cancel_of_le hmn, ← mul_one 1, ← monomial_mul, mul_one, mul_assoc]
      apply mul_dvd_mul dvd_rfl
      apply dvd_mul_of_dvd_right hrq

theorem dvd_monomial_iff_exists [IsCancelMulZero R] {n : σ →₀ ℕ} {a : R} (ha : a ≠ 0) :
    p ∣ monomial n a ↔ ∃ m b, m ≤ n ∧ b ∣ a ∧ p = monomial m b := by
  rw [show monomial n a = monomial n 1 * C a from by
    rw [mul_comm, C_mul_monomial, mul_one]]
  rw [dvd_monomial_mul_iff_exists]
  apply exists_congr
  intro m
  constructor
  · rintro ⟨r, hmn, hr, h⟩
    rw [dvd_C_iff_exists ha] at hr
    obtain ⟨b, hb, hr⟩ := hr
    use b, hmn, hb
    rw [h, mul_comm, hr, C_mul_monomial, mul_one]
  · rintro ⟨b, hmn, hb, h⟩
    use C b, hmn, map_dvd C hb
    rwa [mul_comm, C_mul_monomial, mul_one]

theorem dvd_monomial_one_iff_exists [IsCancelMulZero R] {n : σ →₀ ℕ} :
    p ∣ monomial n 1 ↔ ∃ m u, m ≤ n ∧ IsUnit u ∧ p = monomial m u := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [Subsingleton.allEq _ p, dvd_refl, isUnit_iff_eq_one, and_true, exists_eq_right,
    true_iff]
    use n
  rw [dvd_monomial_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro m
  simp_rw [isUnit_iff_dvd_one]

theorem dvd_X_iff_exists [IsCancelMulZero R] {i : σ} :
    p ∣ X i ↔ ∃ r, IsUnit r ∧ (p = C r ∨ p = r • X i) := by
  rw [show (X i : MvPolynomial σ R) = monomial (Finsupp.single i 1) 1 from
    by rfl]
  rw [dvd_monomial_one_iff_exists]
  rw [exists_comm]
  apply exists_congr
  intro b
  constructor
  · rintro ⟨m, hmn, hb, hp⟩
    simp only [hb, true_and]
    suffices m = 0 ∨ m = Finsupp.single i 1 by
      rcases this with hm | hm
      · left; simp [hp, hm]
      · right; rw [hp, hm, smul_monomial, smul_eq_mul, mul_one]
    by_cases hm : m i = 0
    · left
      ext j
      simp only [Finsupp.coe_zero, Pi.zero_apply, ← Nat.le_zero]
      by_cases hj : j = i
      · rw [← hm, hj]
      · rw [← ne_eq] at hj; convert hmn j; rw [Finsupp.single_eq_of_ne hj]
    · right
      ext j
      apply le_antisymm (hmn j)
      by_cases hj : j = i
      · simpa [hj, Nat.one_le_iff_ne_zero]
      · rw [← ne_eq] at hj; simp [Finsupp.single_eq_of_ne hj]
  · rintro ⟨hb, hp | hp⟩
    · use 0; simp [hb, hp]
    · use Finsupp.single i 1, le_refl _, hb, by simp [hp, smul_monomial]

section
/-! ## The quadratic polynomia $$\sum_{i=1}^n X_i Y_i$$. -/

open Polynomial

variable (n : Type*) [Finite n] (R : Type*) [CommRing R] [IsDomain R]

/-- The quadratic polynomial $$\sum_{i=1}^n X_i Y_i$$. -/
noncomputable def sum_X_mul_Y : MvPolynomial (n ⊕ n) R :=
  ∑ᶠ i, MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr i)

theorem irreducible_sum_X_mul_Y [Nontrivial n] :
    Irreducible (sum_X_mul_Y n R) := by
  have : DecidableEq n := Classical.typeDecidableEq n
  have : Fintype n := Fintype.ofFinite n
  let p := ∑ x : n,
    MvPolynomial.X (R := MvPolynomial n R) x * MvPolynomial.C ( (MvPolynomial.X (R := R) x))
  let e := sumRingEquiv R n n
  have : e (sum_X_mul_Y n R) = p := by
    simp [finsum_eq_sum_of_fintype, e, p, sum_X_mul_Y, sumRingEquiv]
  rw [← MulEquiv.irreducible_iff e, this]
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
