import Mathlib




section UnexploredExercise_3106
/-
  If $R$ is a UFD and $f(x) = a_n x^n + a_{n-1} x^{n-1} + \dots + a_1 x + a_0$ is a polynomial in
 $R[x]$ with a rational root of the form $\frac{p}{q}$ (where $p, q \in R$ have no common divisors
  other than units), then :
  1. $p$ must divide $a_0$, the constant term of $f(x)$.
  2. $q$ must divide $a_n$, the leading coefficient of $f(x)$.
-/
variable {R : Type* } {K : Type u_2} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
 [Field K] [Algebra R K] [IsFractionRing R K] {f : Polynomial R} {r : K}
--Both two theorem are well-known.

lemma part_1 (hr : (Polynomial.aeval r) f = 0) : IsFractionRing.num R r ∣ f.coeff 0 :=
  num_dvd_of_is_root hr
lemma part_2 (hr : (Polynomial.aeval r) f = 0) : ↑(IsFractionRing.den R r) ∣ f.leadingCoeff :=
  den_dvd_of_is_root hr

end UnexploredExercise_3106




section UnexploredExercise_3109
/-
Use the Rational Root Theorem 5.6 (applied to $x^3−2$ ) to argue that $\sqrt[3]{2}$ is irrational.
1. First, according to the definition of cube roots, $\sqrt[3]{2}$ is the roots of $x^3-2$
2. Then according to well-known theorem : If $x^n, n > 0$, is integer and is not the $n$-th power
  of an integer, then $x$ is irrational.
3. Sufficient to check $\sqrt[3]{2}$ is not a integeral, actually it $> 1$ and $< 2$, of course it is
 not a integral.
-/
lemma Int.cast_eq {x y: ℤ} (h : (x : ℝ) = (y : ℝ)) : x = y := by
  linarith [Int.cast_le.mp (le_of_eq h), Int.cast_le.mp (ge_of_eq h)]

lemma main : Irrational (2 ^ ((1 : ℝ) / 3)) := by
  set x : ℝ := (2 ^ ((1 : ℝ) / 3))
  --1. First, according to the definition of cube roots, $\sqrt[3]{2}$ is the roots of $x^3-2$
  have eq : x ^ 3 = 2 := by
    rw [← Real.rpow_natCast (2 ^ (1 / 3)) 3]
    simp only [one_div, Nat.cast_ofNat, Nat.ofNat_nonneg, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, Real.rpow_inv_rpow]
  /- 2. Then according to well-known theorem : If $x^n, n > 0$, is integer and is not the $n$-th power
  of an integer, then $x$ is irrational. -/
  apply irrational_nrt_of_notint_nrt (3 : ℕ) (2 : ℕ)
  · simp only [eq, Nat.cast_ofNat, Int.cast_ofNat]
  · /- 3. Sufficient to check $\sqrt[3]{2}$ is not a integeral, actually it $> 1$ and $< 2$, of course it is
  not a integral. -/
    intro ⟨y, hy⟩
    have hy : y ^ 3 = 2 := by
      apply Int.cast_eq
      simp only [Int.cast_pow, Int.cast_ofNat, ← hy, eq]
    by_cases nh : y ≥ 2
    · linarith [hy, (pow_le_pow_left (by linarith) nh 3)]
    · have : 0 ≥ y ^ 3 :=
        Odd.pow_nonpos (Nat.odd_iff.mpr rfl) <| Int.lt_add_one_iff.mp <| lt_of_le_of_ne
         (Int.not_lt.mp nh) fun h ↦ (by rw [h] at hy; norm_num at hy)
      linarith
  · norm_num

end UnexploredExercise_3109




section UnexploredExercise_3108

/-
Use the Rational Root Theorem 5.6 to argue that $x^{3}+x+7$ is irreducible over $\mathbb{Q}[x]$.
 Use elementary calculus to argue that this polynomial does have exactly one real root.

Given the polynomial : $f(x) = x^3 + x + 7$
All this lemmas are some trivial things in mathmetics, but not easy in lean
1.$\operatorname{deg}P = 3$   2. $P \neq 0$ 	3.$P$ is not unit

The Rational Root Theorem states that if a polynomial with integer coefficients has a rational root
$ \frac{p}{q} $ (in lowest terms), then $ p $ divides the constant term and $q$ divides
the leading coefficient.

The leading coefficient is $1$, so the possible values for $q $ are $ \pm 1 $.

Thus, the only possible rational roots are $\pm1$ and $\pm7$, they are all integrals.

Now we can check each of these values to see if they are roots of $ f(x) $:

1. When $x\ge0$, $f(x)\ge0^3+0+7=7>0$, they are not roots
2. When $x\le-2$, $f(x)\le(-2)^3+(-2)+7=-3<0$, they are not roots
3. Hence the only posible root is $x = -1$
4. $ f(1) = 1^3 + 1 + 7 = 9 \neq 0 $
5. Since none of these values yield zero, $ f(x) $ has no rational roots.
Therefore, by the Rational Root Theorem, the polynomial $ f(x) = x^3 + x + 7 $ is irreducible over
$ \mathbb{Q} $.
-/

open Polynomial
open IsFractionRing

--Given the polynomial : $f(x) = x^3 + x + 7$
noncomputable def P : Polynomial ℤ := C 1 * X ^ 3 + C 1 * X + C 7
--All this lemmas are some trivial things in mathmetics, but not easy in lean

lemma coeffs : (∀ n > 3, P.coeff n = 0) ∧ P.coeff 3 = 1 ∧
    P.coeff 2 = 0 ∧ P.coeff 1 = 1 ∧ P.coeff 0 = 7 := by
  simp only [P, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num
  intro n hn
  repeat' rw [if_neg]
  any_goals linarith only [hn]
--1.$\operatorname{deg}P = 3$
lemma P_natDeg : P.natDegree = 3 :=
  have : P.degree = 3 := by
    unfold P; compute_degree
    simp only [ne_eq, one_ne_zero, not_false_eq_true]
    repeat exact Nat.le_of_ble_eq_true rfl
  natDegree_eq_of_degree_eq_some this

lemma P_inQ_natDeg : (Polynomial.map (algebraMap ℤ ℚ) P).natDegree = 3 := by
  have : (Polynomial.map (algebraMap ℤ ℚ) P).coeff 3 = (algebraMap ℤ ℚ) (P.coeff 3) :=
    coeff_map (algebraMap ℤ ℚ) 3
  simp only [coeffs.2.1, algebraMap_int_eq, eq_intCast, Int.cast_one] at this
  have : (Polynomial.map (algebraMap ℤ ℚ) P).natDegree ≥ 3 :=
    le_natDegree_of_ne_zero <| ne_zero_of_eq_one this
  linarith[natDegree_map_le (algebraMap ℤ ℚ) P, P_natDeg]

example : Irreducible (Polynomial.map (algebraMap ℤ ℚ) P) := by
  --2. $P \neq 0$
  have P_inQ_notzero : Polynomial.map (algebraMap ℤ ℚ) P ≠ 0 :=
    zero_le_degree_iff.mp <| le_of_lt <| natDegree_pos_iff_degree_pos.mp
    <| by rw [P_inQ_natDeg]; norm_num
  --3.$P$ is not unit
  have P_inQ_notUnit : ¬IsUnit (Polynomial.map (algebraMap ℤ ℚ) P) := by
    apply not_isUnit_of_natDegree_pos
    rw[P_inQ_natDeg]; norm_num

  /-The Rational Root Theorem states that if a polynomial with integer coefficients has a rational root
    $ \frac{p}{q} $ (in lowest terms), then $ p $ divides the constant term and $q$ divides
    the leading coefficient. -/
  apply (irreducible_iff_degree_lt (Polynomial.map (algebraMap ℤ ℚ) P) P_inQ_notzero
    P_inQ_notUnit).mpr

  intro q qdeg dvd
  simp only [P_inQ_natDeg, Nat.reduceDiv, Nat.cast_one] at qdeg

  have qneq0: q ≠ 0 := fun nq ↦ (by simp only [nq, zero_dvd_iff] at dvd; contradiction)

  by_cases choice : q.natDegree = 1
  · have choice : q.degree = 1 := by rw[degree_eq_natDegree qneq0, choice, Nat.cast_one]

    obtain ⟨x, hx⟩ : ∃ x, q.IsRoot x := exists_root_of_degree_eq_one choice

    have x_P_root : (aeval x) P = 0 := by
      rw[← (aeval_map_algebraMap ℚ x P)]
      exact aeval_eq_zero_of_dvd_aeval_eq_zero dvd hx
    --The leading coefficient is $1$, so the possible values for $q $ are $ \pm 1 $.
    have den_dvd : (den ℤ x : ℤ) ∣ P.leadingCoeff := den_dvd_of_is_root x_P_root
    rw[← coeff_natDegree, P_natDeg, coeffs.2.1] at den_dvd

    have den_dvd : (den ℤ x : ℤ) = 1 ∨ (den ℤ x : ℤ) = -1 :=
      Int.natAbs_eq_natAbs_iff.mp <| Nat.eq_one_of_dvd_one <| Int.ofNat_dvd_right.mp den_dvd

    have dvd : IsLocalization.mk' ℚ (num ℤ x) (den ℤ x) = x := mk'_num_den ℤ x
    simp only [mk'_eq_div, algebraMap_int_eq, eq_intCast] at dvd
    --Thus, the only possible rational roots are $\pm1$ and $\pm7$, they are all integrals.
    obtain ⟨x₀, hx⟩ : ∃ x₀ : ℤ , (x₀ : ℚ) = x := by
      rcases den_dvd with h | h
      · simp only [h, Int.cast_one, div_one] at dvd
        use (num ℤ x : ℤ)
      · simp only [h, Int.reduceNeg, Int.cast_neg, Int.cast_one] at dvd
        use (-num ℤ x : ℤ)
        nth_rw 2[← dvd]
        rw[div_neg (num ℤ x : ℚ), div_one (num ℤ x : ℚ), Int.cast_neg]
    --Now we can check each of these values to see if they are roots of $ f(x) $:
    simp only [P] at x_P_root
    rw [map_add, map_add, aeval_C] at x_P_root
    simp only [eq_intCast, Int.cast_one, one_mul, map_pow, aeval_X, algebraMap_int_eq,
      Int.cast_ofNat] at x_P_root
    --1. When $x\ge0$, $f(x)\ge0^3+0+7=7>0$, they are not roots
    have t1 : x < 0 := by by_contra nh; push_neg at nh; linarith[pow_nonneg nh 3]
    --2. When $x\le-2$, $f(x)\le(-2)^3+(-2)+7=-3<0$, they are not roots
    have t2 : -2 < x := by
      by_contra nh; push_neg at nh
      have : x ^ 3 ≤ (-2) ^ 3 := by
        have : 2 ^ 3 ≤ (-x) ^ 3 := by
          apply pow_le_pow_left
          repeat linarith
        have : - (-x) ^ 3 ≤ - 2 ^ 3 := by linarith
        rw [Odd.neg_pow (Nat.odd_iff.mpr rfl)] at this
        linarith
      linarith

    rw[← hx] at t1 t2 x_P_root
    simp only [Int.cast_lt_zero] at t1
    have : -1 ≤ x₀ := Int.cast_lt.mp t2
    --3. Hence the only posible root is $x = -1$
    have : x₀ = -1 := by linarith [Int.le_sub_one_of_lt t1]
    simp only [this, Int.reduceNeg, Int.cast_neg, Int.cast_one] at x_P_root
    --4. $ f(1) = 1^3 + 1 + 7 = 9 \neq 0 $
    norm_num at x_P_root

  · /-5. Since none of these values yield zero, $ f(x) $ has no rational roots.
    Therefore, by the Rational Root Theorem, the polynomial $ f(x) = x^3 + x + 7 $ is irreducible over
    $ \mathbb{Q} $.-/
    have qdeg : q.natDegree < 1 := Nat.lt_of_le_of_ne (natDegree_le_iff_degree_le.mpr qdeg) choice
    have := degree_eq_natDegree qneq0
    rw [Nat.lt_one_iff.mp qdeg, CharP.cast_eq_zero] at this
    exact isUnit_iff_degree_eq_zero.mpr this

end UnexploredExercise_3108
