/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.RingTheory.DividedPowers.Basic

/-! # Examples of divided power structures

In this file we show that, for certain choices of a commutative (semi)ring `A` and an ideal `I` of
`A`, the family of maps `ℕ → A → A` given by `fun n x ↦ x^n/n!` is a divided power structure on `I`.

## Main Definitions

* `DividedPowers.OfInvertibleFactorial.dpow` : the family of functions `ℕ → A → A` given by
  `x^n/n!`.
* `DividedPowers.OfInvertibleFactorial.dividedPowers` : the divided power structure on `I` given by
  `fun x n ↦ x^n/n!`, assuming that there exists a natural number `n` such that `f (n-1)!` is
  invertible in `A` and `I^n = 0`.
* `DividedPowers.OfSquareZero.dividedPowers` : given an ideal `I` such that `I^2 =0`, this is
  the divided power structure on `I` given by `fun x n ↦ x^n/n!`.
* `DividedPowers.CharP.dividedPowers` : if `A` is a commutative ring of prime characteristic `p`
  and `I` is an ideal such that `I^p = 0`, , this is the divided power structure on `I` given by
  `fun x n ↦ x^n/n!`.
* `DividedPowers.RatAlgebra.dividedPowers` : if `I` is any ideal in a `ℚ`-algebra, this is the
  divided power structure on `I` given by `fun x n ↦ x^n/n!`.

## Main Results

* `DividedPowers.RatAlgebra.dividedPowers_unique`: there are no other divided power structures on an
  ideal of a `ℚ`-algebra.

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

-/

open Nat Ring

namespace DividedPowers

namespace OfInvertibleFactorial

variable {A : Type*} [CommSemiring A] (I : Ideal A) [DecidablePred (fun x ↦ x ∈ I)]

/-- The family of functions `ℕ → A → A` given by `x^n/n!`. -/
noncomputable def dpow : ℕ → A → A := fun m x => if x ∈ I then inverse (m ! : A) * x ^ m else 0

variable {I}

theorem dpow_eq_of_mem {m : ℕ} {x : A} (hx : x ∈ I) : dpow I m x = inverse (m ! : A) * x ^ m := by
  simp [dpow, hx]

theorem dpow_eq_of_not_mem {m : ℕ} {x : A} (hx : x ∉ I) : dpow I m x = 0 := by simp [dpow, hx]

theorem dpow_null {m : ℕ} {x : A} (hx : x ∉ I) : dpow I m x = 0 := by simp [dpow, hx]

theorem dpow_zero {x : A} (hx : x ∈ I) : dpow I 0 x = 1 := by simp [dpow, hx]

theorem dpow_one {x : A} (hx : x ∈ I) : dpow I 1 x = x := by simp [dpow_eq_of_mem hx]

theorem dpow_mem {m : ℕ} (hm : m ≠ 0) {x : A} (hx : x ∈ I) : dpow I m x ∈ I := by
  rw [dpow_eq_of_mem hx]
  exact Ideal.mul_mem_left I _ (Ideal.pow_mem_of_mem I hx _ (Nat.pos_of_ne_zero hm))

theorem dpow_add_of_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m : ℕ} (hmn : m < n)
    {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    dpow I m (x + y) = (Finset.antidiagonal m).sum (fun k ↦ dpow I k.1 x * dpow I k.2 y) := by
  rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
  simp only [dpow]
  rw [inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hmn),
    Finset.mul_sum, Commute.add_pow' (Commute.all _ _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos hx, if_pos hy]
  ring_nf
  simp only [mul_assoc]; congr; rw [← mul_assoc]
  exact castChoose_eq (hn_fac.natCast_factorial_of_lt hmn) hk

theorem dpow_add {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) (hnI : I ^ n = 0) {m : ℕ} {x : A}
    (hx : x ∈ I) {y : A} (hy : y ∈ I) :
    dpow I m (x + y) = (Finset.antidiagonal m).sum fun k ↦ dpow I k.1 x * dpow I k.2 y := by
  by_cases hmn : m < n
  · exact dpow_add_of_lt hn_fac hmn hx hy
  · have h_sub : I ^ m ≤ I ^ n := Ideal.pow_le_pow_right (not_lt.mp hmn)
    rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
    simp only [dpow]
    have hxy : (x + y) ^ m = 0 := by
      rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hnI]
      exact Set.mem_of_subset_of_mem h_sub (Ideal.pow_mem_pow (Ideal.add_mem I hx hy) m)
    rw [hxy, mul_zero, eq_comm]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_pos hx, if_pos hy, mul_assoc, mul_comm (x ^ k.1), mul_assoc, ← mul_assoc]
    apply mul_eq_zero_of_right
    rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hnI]
    apply Set.mem_of_subset_of_mem h_sub
    rw [← Finset.mem_antidiagonal.mp hk, add_comm, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hy _) (Ideal.pow_mem_pow hx _)

theorem dpow_mul {m : ℕ} {a x : A} (hx : x ∈ I) : dpow I m (a * x) = a ^ m * dpow I m x := by
  rw [dpow_eq_of_mem (Ideal.mul_mem_left I _ hx), dpow_eq_of_mem hx,
    mul_pow, ← mul_assoc, mul_comm _ (a ^ m), mul_assoc]

theorem dpow_mul_of_add_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m k : ℕ}
    (hkm : m + k < n) {x : A} (hx : x ∈ I) :
    dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x := by
  have hm : m < n := lt_of_le_of_lt le_self_add hkm
  have hk : k < n := lt_of_le_of_lt le_add_self hkm
  rw [dpow_eq_of_mem hx, dpow_eq_of_mem hx, dpow_eq_of_mem hx,
    mul_assoc, ← mul_assoc (x ^ m), mul_comm (x ^ m), mul_assoc _ (x ^ m),
    ← pow_add, ← mul_assoc, ← mul_assoc]
  apply congr_arg₂ _ _ rfl
  rw [eq_mul_inverse_iff_mul_eq _ _ _ (hn_fac.natCast_factorial_of_lt hkm),
      mul_assoc,
      inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hm),
      inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hk)]
  norm_cast; apply congr_arg
  rw [← Nat.add_choose_mul_factorial_mul_factorial, mul_comm, mul_comm _ (m !), Nat.choose_symm_add]

theorem mul_dpow {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m k : ℕ} {x : A} (hx : x ∈ I) :
    dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x := by
  by_cases hkm : m + k < n
  · exact dpow_mul_of_add_lt hn_fac hkm hx
  · have hxmk : x ^ (m + k) = 0 := Ideal.pow_eq_zero_of_mem hnI (not_lt.mp hkm) hx
    rw [dpow_eq_of_mem hx, dpow_eq_of_mem hx, dpow_eq_of_mem hx,
      mul_assoc, ← mul_assoc (x ^ m), mul_comm (x ^ m), mul_assoc _ (x ^ m), ← pow_add, hxmk,
      mul_zero, mul_zero, mul_zero, mul_zero]

theorem dpow_comp_of_mul_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m k : ℕ} (hk : k ≠ 0)
    (hkm : m * k < n) {x : A} (hx : x ∈ I) :
    dpow I m (dpow I k x) = ↑(uniformBell m k) * dpow I (m * k) x := by
  have hmn : m < n := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk)) hkm
  rw [dpow_eq_of_mem (m := m * k) hx, dpow_eq_of_mem (dpow_mem hk hx)]
  by_cases hm0 : m = 0
  · simp only [hm0, zero_mul, _root_.pow_zero, mul_one, uniformBell_zero_left, cast_one, one_mul]
  · have hkn : k < n := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm0)) hkm
    rw [dpow_eq_of_mem hx, mul_pow, ← pow_mul, mul_comm k, ← mul_assoc, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [eq_mul_inverse_iff_mul_eq _ _ _ (hn_fac.natCast_factorial_of_lt hkm),
      mul_assoc, inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hmn),
      inverse_pow_mul_eq_iff_eq_mul _ _ (hn_fac.natCast_factorial_of_lt hkn),
      ← uniformBell_mul_eq _ hk]
    simp only [Nat.cast_mul, Nat.cast_pow]
    ring_nf

theorem dpow_comp {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m k : ℕ} (hk : k ≠ 0) {x : A} (hx : x ∈ I) :
    dpow I m (dpow I k x) = ↑(uniformBell m k) * dpow I (m * k) x := by
  by_cases hmk : m * k < n
  · exact dpow_comp_of_mul_lt hn_fac hk hmk hx
  · have hxmk : x ^ (m * k) = 0 := Ideal.pow_eq_zero_of_mem hnI (not_lt.mp hmk) hx
    rw [dpow_eq_of_mem (dpow_mem hk hx), dpow_eq_of_mem hx, dpow_eq_of_mem hx,
      mul_pow, ← pow_mul, ← mul_assoc, mul_comm k, hxmk, mul_zero, mul_zero, mul_zero]

/-- If `(n-1)!` is invertible in `A` and `I^n = 0`, then `I` admits a divided power structure.
  Proposition 1.2.7 of [B74], part (ii). -/
noncomputable def dividedPowers {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A))
    (hnI : I ^ n = 0) : DividedPowers I where
  dpow            := dpow I
  dpow_null hx    := dpow_null hx
  dpow_zero hx    := dpow_zero hx
  dpow_one hx     := dpow_one hx
  dpow_mem hn hx  := dpow_mem hn hx
  dpow_add hx hy  := dpow_add hn_fac hnI hx hy
  dpow_mul        := dpow_mul
  mul_dpow hx     := mul_dpow hn_fac hnI hx
  dpow_comp hk hx := dpow_comp hn_fac hnI hk hx

lemma dpow_apply {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m : ℕ} {x : A} :
  (dividedPowers (hn_fac) (hnI)).dpow m x =
    if x ∈ I then inverse (m.factorial : A) * x ^ m else 0 := rfl

end OfInvertibleFactorial

namespace OfSquareZero

variable {A : Type*} [CommSemiring A] {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)]
  (hI2 : I ^ 2 = 0)

/-- If `I^2 = 0`, then `I` admits a divided power structure. -/
noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (by norm_num) hI2

theorem dpow_of_two_le {n : ℕ} (hn : 2 ≤ n) (a : A) :
    (dividedPowers hI2) n a = 0 := by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hI2 hn ha, mul_zero]

end OfSquareZero

namespace IsNilpotent

variable {A : Type*} [CommRing A] {p : ℕ} [Fact (Nat.Prime p)] (hp : IsNilpotent (p : A))
  {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)] (hIp : I ^ p = 0)

/-- If `A` is a commutative ring of prime characteristic `p` and `I` is an ideal such that
  `I^p = 0`, then `I` admits a divided power structure. -/
noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (n := p)
    (IsUnit.natCast_factorial_of_isNilpotent hp (Nat.sub_one_lt (NeZero.ne' p).symm)) hIp

theorem dpow_of_prime_le {n : ℕ} (hn : p ≤ n) (a : A) : (dividedPowers hp hIp) n a = 0 := by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hIp hn ha, mul_zero]

end IsNilpotent

namespace CharP

variable (A : Type*) [CommRing A] (p : ℕ) [CharP A p] [Fact (Nat.Prime p)]
  {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)] (hIp : I ^ p = 0)

/-- If `A` is a commutative ring of prime characteristic `p` and `I` is an ideal such that
  `I^p = 0`, then `I` admits a divided power structure. -/
noncomputable def dividedPowers : DividedPowers I :=
  IsNilpotent.dividedPowers ((CharP.cast_eq_zero A p) ▸ IsNilpotent.zero) hIp

theorem dpow_of_prime_le {n : ℕ} (hn : p ≤ n) (a : A) : (dividedPowers A p hIp) n a = 0 := by
  simp only [dividedPowers, IsNilpotent.dividedPowers, OfInvertibleFactorial.dpow_apply,
    ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hIp hn ha, mul_zero]

end CharP

-- We formalize example 2 from [BO], Section 3.
namespace RatAlgebra

variable {R : Type*} [CommSemiring R] (I : Ideal R) [DecidablePred (fun x ↦ x ∈ I)]

/-- The family `ℕ → R → R` given by `dpow n x = x ^ n / n!`. -/
noncomputable def dpow : ℕ → R → R := OfInvertibleFactorial.dpow I

variable {I}

theorem dpow_eq_of_mem (n : ℕ) {x : R} (hx : x ∈ I) :
    dpow I n x = (inverse n.factorial : R) * x ^ n := by
  rw [dpow, OfInvertibleFactorial.dpow_eq_of_mem hx]

variable [Algebra ℚ R]

variable (I)

/-- If `I` is an ideal in a `ℚ`-algebra `A`, then `I` admits a unique divided power structure,
  given by `dpow n x = x ^ n / n!`. -/
noncomputable def dividedPowers : DividedPowers I where
  dpow           := dpow I
  dpow_null hx   := OfInvertibleFactorial.dpow_null hx
  dpow_zero hx   := OfInvertibleFactorial.dpow_zero hx
  dpow_one hx    := OfInvertibleFactorial.dpow_one hx
  dpow_mem hn hx := OfInvertibleFactorial.dpow_mem hn hx
  dpow_add {n} _ _ hx hy := OfInvertibleFactorial.dpow_add_of_lt
    (IsUnit.natCast_factorial_of_algebra ℚ _) (n.lt_succ_self) hx hy
  dpow_mul hx := OfInvertibleFactorial.dpow_mul hx
  mul_dpow {m} k _ hx := OfInvertibleFactorial.dpow_mul_of_add_lt
    (IsUnit.natCast_factorial_of_algebra ℚ _) (m + k).lt_succ_self hx
  dpow_comp hk hx := OfInvertibleFactorial.dpow_comp_of_mul_lt
    (IsUnit.natCast_factorial_of_algebra ℚ _) hk (lt_add_one _) hx

@[simp]
lemma dpow_apply {n : ℕ} {x : R} :
    (dividedPowers I).dpow n x = if x ∈ I then inverse (n.factorial : R) * x ^ n else 0 := rfl

omit [DecidablePred fun x ↦ x ∈ I] in
/-- If `I` is an ideal in a `ℚ`-algebra `A`, then the divided power structure on `I` given by
  `dpow n x = x ^ n / n!` is the only possible one. -/
theorem dpow_eq_inv_fact_smul (hI : DividedPowers I) {n : ℕ} {x : R} (hx : x ∈ I) :
    hI.dpow n x = (inverse (n.factorial : ℚ)) • x ^ n := by
  rw [inverse_eq_inv', ← factorial_mul_dpow_eq_pow hI hx, ← smul_eq_mul, ← smul_assoc]
  nth_rewrite 1 [← one_smul R (hI.dpow n x)]
  congr
  have aux : ((n !) : R) = (n ! : ℚ) • (1 : R) := by
    rw [cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
  rw [aux, ← mul_smul]
  suffices (n ! : ℚ)⁻¹ * (n !) = 1 by
    rw [this, one_smul]
  apply Rat.inv_mul_cancel
  rw [← cast_zero, ne_eq]
  simp [factorial_ne_zero]

variable {I}

/-- There are no other divided power structures on an ideal of a  `ℚ`-algebra. -/
theorem dividedPowers_unique (hI : DividedPowers I) : hI = dividedPowers I :=
  hI.ext _ (fun n x hx ↦ by rw [dpow_apply, if_pos hx, eq_comm, inverse_mul_eq_iff_eq_mul _ _ _
      (IsUnit.natCast_factorial_of_algebra ℚ n), factorial_mul_dpow_eq_pow _ hx])

end RatAlgebra

end DividedPowers
