/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

#align_import ring_theory.polynomial.cyclotomic.expand from "leanprover-community/mathlib"@"0723536a0522d24fc2f159a096fb3304bef77472"

/-!
# Cyclotomic polynomials and `expand`.

We gather results relating cyclotomic polynomials and `expand`.

## Main results

* `Polynomial.cyclotomic_expand_eq_cyclotomic_mul` : If `p` is a prime such that `¬ p ∣ n`, then
  `expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`.
* `Polynomial.cyclotomic_expand_eq_cyclotomic` : If `p` is a prime such that `p ∣ n`, then
  `expand R p (cyclotomic n R) = cyclotomic (p * n) R`.
* `Polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd` : If `R` is of characteristic `p` and
  `¬p ∣ n`, then `cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1)`.
* `Polynomial.cyclotomic_mul_prime_dvd_eq_pow` : If `R` is of characteristic `p` and `p ∣ n`, then
  `cyclotomic (n * p) R = (cyclotomic n R) ^ p`.
* `Polynomial.cyclotomic_mul_prime_pow_eq` : If `R` is of characteristic `p` and `¬p ∣ m`, then
  `cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`.
-/


namespace Polynomial

/-- If `p` is a prime such that `¬ p ∣ n`, then
`expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`. -/
@[simp]
theorem cyclotomic_expand_eq_cyclotomic_mul {p n : ℕ} (hp : Nat.Prime p) (hdiv : ¬p ∣ n)
    (R : Type*) [CommRing R] :
    expand R p (cyclotomic n R) = cyclotomic (n * p) R * cyclotomic n R := by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  -- ⊢ ↑(expand R p) (cyclotomic 0 R) = cyclotomic (0 * p) R * cyclotomic 0 R
  · simp
    -- 🎉 no goals
  haveI := NeZero.of_pos hnpos
  -- ⊢ ↑(expand R p) (cyclotomic n R) = cyclotomic (n * p) R * cyclotomic n R
  suffices expand ℤ p (cyclotomic n ℤ) = cyclotomic (n * p) ℤ * cyclotomic n ℤ by
    rw [← map_cyclotomic_int, ← map_expand, this, Polynomial.map_mul, map_cyclotomic_int,
      map_cyclotomic]
  refine' eq_of_monic_of_dvd_of_natDegree_le ((cyclotomic.monic _ ℤ).mul (cyclotomic.monic _ _))
    ((cyclotomic.monic n ℤ).expand hp.pos) _ _
  · refine' (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _
      (IsPrimitive.mul (cyclotomic.isPrimitive (n * p) ℤ) (cyclotomic.isPrimitive n ℤ))
      ((cyclotomic.monic n ℤ).expand hp.pos).isPrimitive).2 _
    rw [Polynomial.map_mul, map_cyclotomic_int, map_cyclotomic_int, map_expand, map_cyclotomic_int]
    -- ⊢ cyclotomic (n * p) ℚ * cyclotomic n ℚ ∣ ↑(expand ℚ p) (cyclotomic n ℚ)
    refine' IsCoprime.mul_dvd (cyclotomic.isCoprime_rat fun h => _) _ _
    · replace h : n * p = n * 1 := by simp [h]
      -- ⊢ False
      exact Nat.Prime.ne_one hp (mul_left_cancel₀ hnpos.ne' h)
      -- 🎉 no goals
    · have hpos : 0 < n * p := mul_pos hnpos hp.pos
      -- ⊢ cyclotomic (n * p) ℚ ∣ ↑(expand ℚ p) (cyclotomic n ℚ)
      have hprim := Complex.isPrimitiveRoot_exp _ hpos.ne'
      -- ⊢ cyclotomic (n * p) ℚ ∣ ↑(expand ℚ p) (cyclotomic n ℚ)
      rw [cyclotomic_eq_minpoly_rat hprim hpos]
      -- ⊢ minpoly ℚ (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(n * p))) ∣ ↑(expand ℚ p …
      refine' @minpoly.dvd ℚ ℂ _ _ algebraRat _ _ _
      -- ⊢ ↑(aeval (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(n * p)))) (↑(expand ℚ p)  …
      rw [aeval_def, ← eval_map, map_expand, map_cyclotomic, expand_eval, ← IsRoot.def,
        @isRoot_cyclotomic_iff]
      convert IsPrimitiveRoot.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n)
      -- ⊢ n = n * p / p
      rw [Nat.mul_div_cancel _ (Nat.Prime.pos hp)]
      -- 🎉 no goals
    · have hprim := Complex.isPrimitiveRoot_exp _ hnpos.ne.symm
      -- ⊢ cyclotomic n ℚ ∣ ↑(expand ℚ p) (cyclotomic n ℚ)
      rw [cyclotomic_eq_minpoly_rat hprim hnpos]
      -- ⊢ minpoly ℚ (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) ∣ ↑(expand ℚ p) (min …
      refine' @minpoly.dvd ℚ ℂ _ _ algebraRat _ _ _
      -- ⊢ ↑(aeval (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n))) (↑(expand ℚ p) (minpo …
      rw [aeval_def, ← eval_map, map_expand, expand_eval, ← IsRoot.def, ←
        cyclotomic_eq_minpoly_rat hprim hnpos, map_cyclotomic, @isRoot_cyclotomic_iff]
      exact IsPrimitiveRoot.pow_of_prime hprim hp hdiv
      -- 🎉 no goals
  · rw [natDegree_expand, natDegree_cyclotomic,
      natDegree_mul (cyclotomic_ne_zero _ ℤ) (cyclotomic_ne_zero _ ℤ), natDegree_cyclotomic,
      natDegree_cyclotomic, mul_comm n,
      Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hp).2 hdiv), Nat.totient_prime hp,
      mul_comm (p - 1), ← Nat.mul_succ, Nat.sub_one, Nat.succ_pred_eq_of_pos hp.pos]
#align polynomial.cyclotomic_expand_eq_cyclotomic_mul Polynomial.cyclotomic_expand_eq_cyclotomic_mul

/-- If `p` is a prime such that `p ∣ n`, then
`expand R p (cyclotomic n R) = cyclotomic (p * n) R`. -/
@[simp]
theorem cyclotomic_expand_eq_cyclotomic {p n : ℕ} (hp : Nat.Prime p) (hdiv : p ∣ n) (R : Type*)
    [CommRing R] : expand R p (cyclotomic n R) = cyclotomic (n * p) R := by
  rcases n.eq_zero_or_pos with (rfl | hzero)
  -- ⊢ ↑(expand R p) (cyclotomic 0 R) = cyclotomic (0 * p) R
  · simp
    -- 🎉 no goals
  haveI := NeZero.of_pos hzero
  -- ⊢ ↑(expand R p) (cyclotomic n R) = cyclotomic (n * p) R
  suffices expand ℤ p (cyclotomic n ℤ) = cyclotomic (n * p) ℤ by
    rw [← map_cyclotomic_int, ← map_expand, this, map_cyclotomic_int, map_cyclotomic]
  refine' eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic _ _)
    ((cyclotomic.monic n ℤ).expand hp.pos) _ _
  · have hpos := Nat.mul_pos hzero hp.pos
    -- ⊢ cyclotomic (n * p) ℤ ∣ ↑(expand ℤ p) (cyclotomic n ℤ)
    have hprim := Complex.isPrimitiveRoot_exp _ hpos.ne.symm
    -- ⊢ cyclotomic (n * p) ℤ ∣ ↑(expand ℤ p) (cyclotomic n ℤ)
    rw [cyclotomic_eq_minpoly hprim hpos]
    -- ⊢ minpoly ℤ (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(n * p))) ∣ ↑(expand ℤ p …
    refine' minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hpos) _
    -- ⊢ ↑(aeval (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(n * p)))) (↑(expand ℤ p)  …
    rw [aeval_def, ← eval_map, map_expand, map_cyclotomic, expand_eval, ← IsRoot.def,
      @isRoot_cyclotomic_iff]
    · convert IsPrimitiveRoot.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n)
      -- ⊢ n = n * p / p
      rw [Nat.mul_div_cancel _ hp.pos]
      -- 🎉 no goals
  · rw [natDegree_expand, natDegree_cyclotomic, natDegree_cyclotomic, mul_comm n,
      Nat.totient_mul_of_prime_of_dvd hp hdiv, mul_comm]
#align polynomial.cyclotomic_expand_eq_cyclotomic Polynomial.cyclotomic_expand_eq_cyclotomic

/-- If the `p ^ n`th cyclotomic polynomial is irreducible, so is the `p ^ m`th, for `m ≤ n`. -/
theorem cyclotomic_irreducible_pow_of_irreducible_pow {p : ℕ} (hp : Nat.Prime p) {R} [CommRing R]
    [IsDomain R] {n m : ℕ} (hmn : m ≤ n) (h : Irreducible (cyclotomic (p ^ n) R)) :
    Irreducible (cyclotomic (p ^ m) R) := by
  rcases m.eq_zero_or_pos with (rfl | hm)
  -- ⊢ Irreducible (cyclotomic (p ^ 0) R)
  · simpa using irreducible_X_sub_C (1 : R)
    -- 🎉 no goals
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  -- ⊢ Irreducible (cyclotomic (p ^ m) R)
  induction' k with k hk
  -- ⊢ Irreducible (cyclotomic (p ^ m) R)
  · simpa using h
    -- 🎉 no goals
  have : m + k ≠ 0 := (add_pos_of_pos_of_nonneg hm k.zero_le).ne'
  -- ⊢ Irreducible (cyclotomic (p ^ m) R)
  rw [Nat.add_succ, pow_succ', ← cyclotomic_expand_eq_cyclotomic hp <| dvd_pow_self p this] at h
  -- ⊢ Irreducible (cyclotomic (p ^ m) R)
  exact hk (by linarith) (of_irreducible_expand hp.ne_zero h)
  -- 🎉 no goals
#align polynomial.cyclotomic_irreducible_pow_of_irreducible_pow Polynomial.cyclotomic_irreducible_pow_of_irreducible_pow

/-- If `Irreducible (cyclotomic (p ^ n) R)` then `Irreducible (cyclotomic p R).` -/
theorem cyclotomic_irreducible_of_irreducible_pow {p : ℕ} (hp : Nat.Prime p) {R} [CommRing R]
    [IsDomain R] {n : ℕ} (hn : n ≠ 0) (h : Irreducible (cyclotomic (p ^ n) R)) :
    Irreducible (cyclotomic p R) :=
  pow_one p ▸ cyclotomic_irreducible_pow_of_irreducible_pow hp hn.bot_lt h
#align polynomial.cyclotomic_irreducible_of_irreducible_pow Polynomial.cyclotomic_irreducible_of_irreducible_pow

section CharP

/-- If `R` is of characteristic `p` and `¬p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1)`. -/
theorem cyclotomic_mul_prime_eq_pow_of_not_dvd (R : Type*) {p n : ℕ} [hp : Fact (Nat.Prime p)]
    [Ring R] [CharP R p] (hn : ¬p ∣ n) : cyclotomic (n * p) R = cyclotomic n R ^ (p - 1) := by
  letI : Algebra (ZMod p) R := ZMod.algebra _ _
  -- ⊢ cyclotomic (n * p) R = cyclotomic n R ^ (p - 1)
  suffices cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p) ^ (p - 1) by
    rw [← map_cyclotomic _ (algebraMap (ZMod p) R), ← map_cyclotomic _ (algebraMap (ZMod p) R),
      this, Polynomial.map_pow]
  apply mul_right_injective₀ (cyclotomic_ne_zero n <| ZMod p); dsimp
  -- ⊢ (fun x x_1 => x * x_1) (cyclotomic n (ZMod p)) (cyclotomic (n * p) (ZMod p)) …
                                                               -- ⊢ cyclotomic n (ZMod p) * cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p)  …
  rw [← pow_succ, tsub_add_cancel_of_le hp.out.one_lt.le, mul_comm, ← ZMod.expand_card]
  -- ⊢ cyclotomic (n * p) (ZMod p) * cyclotomic n (ZMod p) = ↑(expand (ZMod p) p) ( …
  conv_rhs => rw [← map_cyclotomic_int]
  -- ⊢ cyclotomic (n * p) (ZMod p) * cyclotomic n (ZMod p) = ↑(expand (ZMod p) p) ( …
  rw [← map_expand, cyclotomic_expand_eq_cyclotomic_mul hp.out hn, Polynomial.map_mul,
    map_cyclotomic, map_cyclotomic]
#align polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd Polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd

/-- If `R` is of characteristic `p` and `p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ p`. -/
theorem cyclotomic_mul_prime_dvd_eq_pow (R : Type*) {p n : ℕ} [hp : Fact (Nat.Prime p)] [Ring R]
    [CharP R p] (hn : p ∣ n) : cyclotomic (n * p) R = cyclotomic n R ^ p := by
  letI : Algebra (ZMod p) R := ZMod.algebra _ _
  -- ⊢ cyclotomic (n * p) R = cyclotomic n R ^ p
  suffices cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p) ^ p by
    rw [← map_cyclotomic _ (algebraMap (ZMod p) R), ← map_cyclotomic _ (algebraMap (ZMod p) R),
      this, Polynomial.map_pow]
  rw [← ZMod.expand_card, ← map_cyclotomic_int n, ← map_expand,
    cyclotomic_expand_eq_cyclotomic hp.out hn, map_cyclotomic, mul_comm]
#align polynomial.cyclotomic_mul_prime_dvd_eq_pow Polynomial.cyclotomic_mul_prime_dvd_eq_pow

/-- If `R` is of characteristic `p` and `¬p ∣ m`, then
`cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`. -/
theorem cyclotomic_mul_prime_pow_eq (R : Type*) {p m : ℕ} [Fact (Nat.Prime p)] [Ring R] [CharP R p]
    (hm : ¬p ∣ m) : ∀ {k}, 0 < k → cyclotomic (p ^ k * m) R = cyclotomic m R ^ (p ^ k - p ^ (k - 1))
  | 1, _ => by
    rw [pow_one, Nat.sub_self, pow_zero, mul_comm, cyclotomic_mul_prime_eq_pow_of_not_dvd R hm]
    -- 🎉 no goals
  | a + 2, _ => by
    have hdiv : p ∣ p ^ a.succ * m := ⟨p ^ a * m, by rw [← mul_assoc, pow_succ]⟩
    -- ⊢ cyclotomic (p ^ (a + 2) * m) R = cyclotomic m R ^ (p ^ (a + 2) - p ^ (a + 2  …
    rw [pow_succ, mul_assoc, mul_comm, cyclotomic_mul_prime_dvd_eq_pow R hdiv,
      cyclotomic_mul_prime_pow_eq _ _ a.succ_pos, ← pow_mul]
    congr 1
    -- ⊢ (p ^ Nat.succ a - p ^ (Nat.succ a - 1)) * p = p * p ^ (a + 1) - p ^ (a + 2 - …
    simp only [tsub_zero, Nat.succ_sub_succ_eq_sub]
    -- ⊢ (p ^ Nat.succ a - p ^ a) * p = p * p ^ (a + 1) - p ^ (a + 1)
    rwa [Nat.mul_sub_right_distrib, mul_comm, pow_succ']
    -- 🎉 no goals
#align polynomial.cyclotomic_mul_prime_pow_eq Polynomial.cyclotomic_mul_prime_pow_eq

/-- If `R` is of characteristic `p` and `¬p ∣ m`, then `ζ` is a root of `cyclotomic (p ^ k * m) R`
 if and only if it is a primitive `m`-th root of unity. -/
theorem isRoot_cyclotomic_prime_pow_mul_iff_of_charP {m k p : ℕ} {R : Type*} [CommRing R]
    [IsDomain R] [hp : Fact (Nat.Prime p)] [hchar : CharP R p] {μ : R} [NeZero (m : R)] :
    (Polynomial.cyclotomic (p ^ k * m) R).IsRoot μ ↔ IsPrimitiveRoot μ m := by
  rcases k.eq_zero_or_pos with (rfl | hk)
  -- ⊢ IsRoot (cyclotomic (p ^ 0 * m) R) μ ↔ IsPrimitiveRoot μ m
  · rw [pow_zero, one_mul, isRoot_cyclotomic_iff]
    -- 🎉 no goals
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ IsPrimitiveRoot μ m
  · rw [IsRoot.def, cyclotomic_mul_prime_pow_eq R (NeZero.not_char_dvd R p m) hk, eval_pow] at h
    -- ⊢ IsPrimitiveRoot μ m
    replace h := pow_eq_zero h
    -- ⊢ IsPrimitiveRoot μ m
    rwa [← IsRoot.def, isRoot_cyclotomic_iff] at h
    -- 🎉 no goals
  · rw [← isRoot_cyclotomic_iff, IsRoot.def] at h
    -- ⊢ IsRoot (cyclotomic (p ^ k * m) R) μ
    rw [cyclotomic_mul_prime_pow_eq R (NeZero.not_char_dvd R p m) hk, IsRoot.def, eval_pow, h,
      zero_pow]
    simp only [tsub_pos_iff_lt]
    -- ⊢ p ^ (k - 1) < p ^ k
    apply pow_strictMono_right hp.out.one_lt (Nat.pred_lt hk.ne')
    -- 🎉 no goals
#align polynomial.is_root_cyclotomic_prime_pow_mul_iff_of_char_p Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP

end CharP

end Polynomial
