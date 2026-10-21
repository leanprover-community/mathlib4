/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, Heather Macbeth, Ansar Azhdarov
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Order.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.DFinsupp.Notation
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring.Compare

/-!
# The Motzkin polynomial

The Motzkin polynomial is a well-known counterexample: it is nonnegative everywhere, but not
expressible as a polynomial sum of squares.
-/

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

local notation "⟪" n ", " m "⟫"  => Finsupp.single (0 : Fin 2) n + Finsupp.single (1 : Fin 2) m

open MvPolynomial in
public noncomputable def motzkin_polynomial : MvPolynomial (Fin 2) K :=
  monomial ⟪4, 2⟫ 1 + monomial ⟪2, 4⟫ 1 - monomial ⟪2, 2⟫ 3 + monomial 0 1

private lemma motzkin_polynomial_nonneg_aux (x y : K) :
    0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h : 0 < (x ^ 2 + y ^ 2) ^ 2 := by positivity
  refine nonneg_of_mul_nonneg_left ?_ h
  have H : 0 ≤ (x ^ 3 * y + x * y ^ 3 - 2 * x * y) ^ 2 * (1 + x ^ 2 + y ^ 2)
    + (x ^ 2 - y ^ 2) ^ 2 := by positivity
  linear_combination H

/-- The **Motzkin polynomial** is nonnegative. -/
theorem motzkin_polynomial_nonneg (r : Fin 2 → K) : 0 ≤ motzkin_polynomial.eval r := by
  simp [motzkin_polynomial, MvPolynomial.eval, ← mul_assoc, motzkin_polynomial_nonneg_aux]

/-- If the Motzkin polynomial is expressible as a polynomial sum of squares ∑ gᵢ², then the degree
  of each gᵢ is at most three. -/
private lemma motzkin_polynomial_ne_sos_aux₁ {ι : Type*} {s : Finset ι} {g : ι → MvPolynomial (Fin 2) K}
    (h : motzkin_polynomial = ∑ i ∈ s, g i ^ 2) : ∀ i ∈ s, (g i).totalDegree ≤ 3 := by
  intro i hi
  -- Let d be the maximum degree among gᵢ's. Assume d > 3.
  set d := s.sup fun i ↦ (g i).totalDegree with hd
  suffices d ≤ 3 from le_trans (s.le_sup (f := fun i ↦ (g i).totalDegree) hi) this
  by_contra! hcontra
  -- Take the homogeneous component of degree 2 * d on both sides of h.
  have h1 := congr($h |>.homogeneousComponent (2 * d))
  -- lhs = 0.
  have : motzkin_polynomial (K := K).homogeneousComponent (2 * d) = 0 := by
    apply MvPolynomial.homogeneousComponent_eq_zero
    refine lt_of_le_of_lt (b := 6) ?_ (by linarith)
    rw [motzkin_polynomial]
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    case refine_2 => simp
    refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
    case refine_2 => simp [Finsupp.sum_single_add_single]
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    <;> simp [Finsupp.sum_single_add_single]
  rw [this] at h1
  -- Rewrite rhs as sos of homogeneous components of gᵢ's of degree d.
  have : ∀ i ∈ s, (g i ^ 2).homogeneousComponent (2 * d) = (g i).homogeneousComponent d ^ 2 := by
    intro i hi
    refine MvPolynomial.homogeneousComponent_pow_eq_of_totalDegree_le ?_ 2
    exact Finset.le_sup (f := fun i ↦ (g i).totalDegree) hi
  rw [map_sum, Finset.sum_congr rfl this] at h1
  -- For any choice of variables, rhs evaluates to zero. Hence, each homogeneous component in sos
  -- evaluates to zero. Hence, each homogeneous component in sos is zero.
  simp only [MvPolynomial.funext_iff, map_zero, map_sum, map_pow] at h1
  have h2 : ∀ i ∈ s, (g i).homogeneousComponent d = 0 := by
    intro i hi
    simp only [MvPolynomial.funext_iff, map_zero]
    intro r
    specialize h1 r
    rw [eq_comm, Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _] at h1
    exact sq_eq_zero_iff.mp (h1 i hi)
  -- This contradicts the choice of d.
  have : s.Nonempty := by
    by_contra! rfl
    simpa [motzkin_polynomial] using congr($h |>.coeff 0)
  obtain ⟨i, hi1, hi2⟩ := s.exists_mem_eq_sup this (fun i ↦ (g i).totalDegree)
  specialize h2 i hi1
  rw [hd, hi2] at h2
  replace h2 := congr($h2 |>.totalDegree)
  simp only [MvPolynomial.totalDegree_homogeneousComponent_totalDegree,
    MvPolynomial.totalDegree_zero] at h2
  linarith

/-- Sets the first variable in a bivariate polynomial to zero. -/
private noncomputable def x_zero {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R) :
    Polynomial R := f.aeval (fun₀ | (0 : Fin 2) => 0 | 1 => Polynomial.X)

/-- Sets the second variable in a bivariate polynomial to zero. -/
private noncomputable def y_zero {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R) :
    Polynomial R := f.aeval (fun₀ | (0 : Fin 2) => Polynomial.X | 1 => 0)

private lemma x_zero_sum {R ι : Type*} [CommSemiring R] (f : ι → MvPolynomial (Fin 2) R)
    (s : Finset ι) : x_zero (∑ i ∈ s, f i) = ∑ i ∈ s, x_zero (f i) := by simp [x_zero]

private lemma y_zero_sum {R ι : Type*} [CommSemiring R] (f : ι → MvPolynomial (Fin 2) R)
    (s : Finset ι) : y_zero (∑ i ∈ s, f i) = ∑ i ∈ s, y_zero (f i) := by simp [y_zero]

private lemma x_zero_sq {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R) :
    x_zero (f ^ 2) = x_zero f ^ 2 := by simp [x_zero]

private lemma y_zero_sq {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R) :
    y_zero (f ^ 2) = y_zero f ^ 2 := by simp [y_zero]

private lemma x_zero_monomial {R : Type*} [CommSemiring R] (m : Fin 2 →₀ ℕ) (c : R) :
    x_zero (MvPolynomial.monomial m c) = if m 0 = 0 then Polynomial.monomial (m 1) c else 0 := by
  by_cases! hm : m 0 = 0
  <;> simp [hm, x_zero, MvPolynomial.aeval_monomial, Polynomial.C_mul_X_pow_eq_monomial]

private lemma y_zero_monomial {R : Type*} [CommSemiring R] (m : Fin 2 →₀ ℕ) (c : R) :
    y_zero (MvPolynomial.monomial m c) = if m 1 = 0 then Polynomial.monomial (m 0) c else 0 := by
  by_cases! hm : m 1 = 0
  <;> simp [hm, y_zero, MvPolynomial.aeval_monomial, Polynomial.C_mul_X_pow_eq_monomial]

private lemma mem_support_x_zero {R : Type*} [CommSemiring R] {f : MvPolynomial (Fin 2) R}
    {m : Fin 2 →₀ ℕ} (hm1 : m ∈ f.support) (hm2 : 0 ∉ m.support) : m 1 ∈ (x_zero f).support := by
  rw [Finsupp.mem_support_iff, not_not] at hm2
  rw [Polynomial.mem_support_iff, f.as_sum, x_zero_sum, Polynomial.finsetSum_coeff]
  simp only [x_zero_monomial, apply_ite (Polynomial.coeff · (m 1)), Polynomial.coeff_monomial,
    Polynomial.coeff_zero, ← ite_and, ← hm2]
  have : ∀ d, d = m ↔ d 0 = m 0 ∧ d 1 = m 1 := by simp [Finsupp.ext_iff]
  simp only [← this, Finset.sum_ite_eq', hm1, ite_true, ← MvPolynomial.mem_support_iff]

private lemma mem_support_y_zero {R : Type*} [CommSemiring R] {f : MvPolynomial (Fin 2) R}
    {m : Fin 2 →₀ ℕ} (hm1 : m ∈ f.support) (hm2 : 1 ∉ m.support) : m 0 ∈ (y_zero f).support := by
  rw [Finsupp.mem_support_iff, not_not] at hm2
  rw [Polynomial.mem_support_iff, f.as_sum, y_zero_sum, Polynomial.finsetSum_coeff]
  simp only [y_zero_monomial, apply_ite (Polynomial.coeff · (m 0)), Polynomial.coeff_monomial,
    Polynomial.coeff_zero, ← ite_and, ← hm2, and_comm]
  have : ∀ d, d = m ↔ d 0 = m 0 ∧ d 1 = m 1 := by simp [Finsupp.ext_iff]
  simp only [← this, Finset.sum_ite_eq', hm1, ite_true, ← MvPolynomial.mem_support_iff]

/-- If the Motzkin polynomial is expressible as a polynomial sum of squares ∑ gᵢ², then for every i,
  each non-constant monomial in gᵢ contains both x and y. -/
private lemma motzkin_polynomial_ne_sos_aux₂ {ι : Type*} {s : Finset ι}
    {g : ι → MvPolynomial (Fin 2) K} (h : motzkin_polynomial = ∑ i ∈ s, g i ^ 2) :
    ∀ i ∈ s, ∀ m ∈ (g i).support, 0 ∈ m.support ↔ 1 ∈ m.support := by
  -- Assume that some gₖ contains a monomial m of the form cxⁿ or cyⁿ.
  intro k hk m hm
  by_contra! ⟨hm0, hm1⟩ | ⟨hm0, hm1⟩
  · -- In the first case, set y to zero on both sides of h.
    have h1 := congr(y_zero $h)
    simp only [y_zero_sum, y_zero_sq] at h1
    -- lhs = 1.
    have : y_zero (motzkin_polynomial (K := K)) = 1 := by
      simp [motzkin_polynomial, y_zero, MvPolynomial.aeval]
    rw [this] at h1
    -- The degree of rhs is zero. Hence, the degree of every gᵢ, after setting y to zero, is zero.
    replace h1 := congr($h1 |>.natDegree)
    rw [Polynomial.natDegree_one] at h1
    have h2 : ∀ i ∈ s, (y_zero (g i)).natDegree = 0 := by
      rw [Polynomial.natDegree_sum_pow_eq_of_even _ even_two, eq_comm] at h1
      simpa using h1
    -- This contradicts the assumption on gₖ.
    specialize h2 k hk
    order [Polynomial.le_natDegree_of_mem_supp _ (mem_support_y_zero hm hm1),
      Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hm0)]
  · -- The second case is analogous.
    have h1 := congr(x_zero $h)
    simp only [x_zero_sum, x_zero_sq] at h1
    have : x_zero (motzkin_polynomial (K := K)) = 1 := by
      simp [motzkin_polynomial, x_zero, MvPolynomial.aeval]
    rw [this] at h1
    replace h1 := congr($h1 |>.natDegree)
    rw [Polynomial.natDegree_one] at h1
    have h2 : ∀ i ∈ s, (x_zero (g i)).natDegree = 0 := by
      rw [Polynomial.natDegree_sum_pow_eq_of_even _ even_two, eq_comm] at h1
      simpa using h1
    specialize h2 k hk
    order [Polynomial.le_natDegree_of_mem_supp _ (mem_support_x_zero hm hm0),
      Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hm1)]

private noncomputable def t : Finset (Fin 2 →₀ ℕ) := {⟪2, 1⟫, ⟪1, 2⟫, ⟪1, 1⟫, 0}

/-- If the Motzkin polynomial polynomial is expressible as a polynomial sum of squares ∑ gᵢ², then
  each gᵢ has the form ax²y + bxy² + cxy + d. -/
private lemma motzkin_polynomial_ne_sos_aux₃ {ι : Type*} {s : Finset ι}
    {g : ι → MvPolynomial (Fin 2) K} (h : motzkin_polynomial = ∑ i ∈ s, g i ^ 2) :
    ∀ i ∈ s, (g i).support ⊆ t := by
  intro i hi m hm
  have h1 : m.degree ≤ 3 := le_trans (MvPolynomial.le_totalDegree hm)
    (motzkin_polynomial_ne_sos_aux₁ h i hi)
  simp only [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h1
  have h2 : 0 ∈ m.support ↔ 1 ∈ m.support := motzkin_polynomial_ne_sos_aux₂ h i hi m hm
  simp only [Finsupp.mem_support_iff] at h2
  simp [t, Finsupp.ext_iff]
  lia

private lemma auxₜ : {x ∈ t ×ˢ t | x.1 + x.2 = ⟪2, 2⟫} = {(⟪1, 1⟫, ⟪1, 1⟫)} := by
  ext ⟨x, y⟩
  simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk_inj]
  constructor
  · rintro ⟨⟨(rfl | rfl | rfl | rfl), (rfl | rfl | rfl | rfl)⟩, hxy⟩
    <;> simp_all [Finsupp.ext_iff]
  · intro ⟨hx, hy⟩
    exact ⟨⟨by simp [hx], by simp [hy]⟩, by simp [hx, hy, Finsupp.ext_iff]⟩

/-- The **Motzkin polynomial** is not expressible as a polynomial sum of squares. -/
theorem motzkin_polynomial_ne_sos {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial (Fin 2) K) :
    motzkin_polynomial ≠ ∑ i ∈ s, g i ^ 2 := by
  -- Assume the contrary. Take the coefficient of x²y² on both sides of the equation.
  by_contra hcontra
  have h := congr($hcontra |>.coeff ⟪2, 2⟫)
  -- The coefficient in the Motzkin polynomial is negative.
  have : motzkin_polynomial (K := K).coeff ⟪2, 2⟫ < 0 := by
    simp [motzkin_polynomial, Finsupp.ext_iff, MvPolynomial.coeff_one]
  -- From auxiliary lemmas, the coefficient in sos is sos of coefficients of xy.
  have : ∀ i ∈ s, (g i ^ 2).coeff ⟪2, 2⟫ = (g i).coeff ⟪1, 1⟫ ^ 2 := by
    intro i hi
    conv => left; rw [sq, (g i).as_sum, Finset.sum_mul_sum]
    have hit : (g i).support ⊆ t := motzkin_polynomial_ne_sos_aux₃ hcontra i hi
    rw [Finset.sum_subset hit (fun _ _ hm ↦ by simp [MvPolynomial.notMem_support_iff.mp hm])]
    conv =>
      left; left; right; right; intro m
      rw [Finset.sum_subset hit (fun _ _ hm ↦ by simp [MvPolynomial.notMem_support_iff.mp hm])]
    simp [← Finset.sum_product', MvPolynomial.coeff_monomial, ← Finset.sum_filter, auxₜ, sq]
  rw [MvPolynomial.coeff_sum, Finset.sum_congr rfl this] at h
  -- Hence, it is nonnegative. Contradiction.
  have : 0 ≤ ∑ i ∈ s, (g i).coeff ⟪1, 1⟫ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  order
