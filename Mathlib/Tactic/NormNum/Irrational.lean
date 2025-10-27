/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Rify

/-! # `norm_num` extension for `Irrational`

This module defines a `norm_num` extension for `Irrational x ^ y` for rational `x` and `y`. It also
supports `Irrational √x` expressions.

## Implementation details
To prove that `(a / b) ^ (p / q)` is irrational, we reduce the problem to showing that `(a / b) ^ p`
is not a `q`-th power of any rational number. This, in turn, reduces to proving that either `a` or
`b` is not a `q`-th power of a natural number, assuming `p` and `q` are coprime.
To show that a given `n : ℕ` is not a `q`-th power, we find a natural number `k`
such that `k ^ q < n < (k + 1) ^ q`, using binary search.

## TODO
Disprove `Irrational x` for rational `x`.

-/

namespace Tactic

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

section lemmas

-- TODO: fix non-terminal simp (acting on three goals, with different simp sets)
set_option linter.flexible false in
private theorem irrational_rpow_rat_of_not_power {q : ℚ} {a b : ℕ}
    (h : ∀ p : ℚ, q ^ a ≠ p ^ b) (hb : 0 < b) (hq : 0 ≤ q) :
    Irrational (Real.rpow q (a / b : ℚ)) := by
  simp only [Irrational, Rat.cast_div, Rat.cast_natCast, Real.rpow_eq_pow, Set.mem_range,
    not_exists]
  intro x hx
  absurd h x
  rify
  rw [hx, ← Real.rpow_mul_natCast, div_mul_cancel₀] <;> simp
  · cutsat
  · assumption

private theorem not_power_nat_pow {n p q : ℕ}
    (h_coprime : p.Coprime q)
    (hq : 0 < q)
    (h : ∀ m, n ≠ m ^ q) (m : ℕ) :
    n ^ p ≠ m ^ q := by
  by_cases hn : n = 0
  · specialize h 0
    simp [hn, zero_pow hq.ne.symm] at h
  contrapose! h
  apply_fun Nat.factorization at h
  simp only [Nat.factorization_pow] at h
  suffices ∃ f : ℕ →₀ ℕ, n.factorization = q • f by
    obtain ⟨f, hf⟩ := this
    have : f = (f.prod fun x1 x2 => x1 ^ x2).factorization := by
      rw [Nat.prod_pow_factorization_eq_self]
      intro z hz
      apply_fun Finsupp.support at hf
      rw [Finsupp.support_smul_eq (by cutsat)] at hf
      rw [← hf] at hz
      exact Nat.prime_of_mem_primeFactors hz
    have hf0 : f 0 = 0 := by
      apply_fun (· 0) at hf
      simp only [Nat.factorization_zero_right, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        zero_eq_mul] at hf
      cases hf
      · cutsat
      · assumption
    rw [this, ← Nat.factorization_pow] at hf
    apply Nat.factorization_inj at hf
    · use f.prod (· ^ ·)
    · exact hn
    · simp only [ne_eq, Set.mem_setOf_eq, pow_eq_zero_iff', Finsupp.prod_eq_zero_iff,
        Finsupp.mem_support_iff, existsAndEq, true_and, and_self, not_and, Decidable.not_not]
      tauto
  use n.factorization.mapRange (fun e ↦ e / q) (by simp)
  ext z
  apply_fun (· z) at h
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.mapRange_apply] at h ⊢
  rw [Nat.mul_div_cancel']
  apply Nat.Coprime.dvd_of_dvd_mul_left _ ⟨_, h⟩
  rwa [Nat.coprime_comm]

private theorem not_power_nat_of_bounds {n k d : ℕ}
    (h_left : k ^ d < n) (h_right : n < (k + 1) ^ d) {m : ℕ} :
    n ≠ m ^ d := by
  intro h
  rw [h] at h_left h_right
  have : k < m := lt_of_pow_lt_pow_left' d h_left
  have : m < k + 1 := lt_of_pow_lt_pow_left' d h_right
  cutsat

private theorem not_power_nat_pow_of_bounds {n k p q : ℕ}
    (hq : 0 < q) (h_coprime : p.Coprime q) (h_left : k ^ q < n) (h_right : n < (k + 1) ^ q)
    (m : ℕ) :
    n ^ p ≠ m ^ q := by
  apply not_power_nat_pow h_coprime hq
  intro m
  apply not_power_nat_of_bounds h_left h_right

private lemma eq_of_mul_eq_mul_of_coprime_aux {a b x y : ℕ} (hab : a.Coprime b)
    (h : a * x = b * y) : a ∣ y := Nat.Coprime.dvd_of_dvd_mul_left hab (Dvd.intro x h)

private lemma eq_of_mul_eq_mul_of_coprime {a b x y : ℕ} (hab : a.Coprime b) (hxy : x.Coprime y)
    (h : a * x = b * y) : a = y := by
  apply Nat.dvd_antisymm
  · exact eq_of_mul_eq_mul_of_coprime_aux hab h
  · exact eq_of_mul_eq_mul_of_coprime_aux (x := b) hxy.symm (by rw [mul_comm, ← h, mul_comm])

/-- Weaker version of `not_power_rat_of_num` with extra `q ≥ 0` assumption. -/
private theorem not_power_rat_of_num_aux {a b d : ℕ}
    (h_coprime : a.Coprime b) (ha : ∀ x, a ≠ x ^ d) {q : ℚ} (hq : 0 ≤ q) :
    (a / b : ℚ) ≠ q ^ d := by
  by_cases hb_zero : b = 0
  · subst hb_zero
    contrapose! ha
    simp only [Nat.coprime_zero_right] at h_coprime
    subst h_coprime
    use 1
    simp
  by_contra! h
  rw [← Rat.num_div_den q] at h
  set x' := q.num
  set y := q.den
  obtain ⟨x, hx'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x' by rwa [Rat.num_nonneg])
  rw [hx'] at h
  specialize ha x
  simp only [Int.cast_natCast, div_pow] at h
  rw [div_eq_div_iff] at h
  rotate_left
  · simpa
  · simp [y]
  replace h : a * y ^ d = x ^ d * b := by
    qify
    assumption
  apply ha
  conv at h => rhs; rw [mul_comm]
  apply eq_of_mul_eq_mul_of_coprime h_coprime _ h
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  simpa [hx'] using (show x'.natAbs.Coprime y from Rat.reduced q)

private theorem not_power_rat_of_num {a b d : ℕ}
    (h_coprime : a.Coprime b) (ha : ∀ x, a ≠ x ^ d) (q : ℚ) :
    (a / b : ℚ) ≠ q ^ d := by
  by_cases hq : 0 ≤ q
  · apply not_power_rat_of_num_aux h_coprime ha hq
  rcases d.even_or_odd with (h_even | h_odd)
  · have := not_power_rat_of_num_aux h_coprime (q := -q) ha (by linarith)
    rwa [h_even.neg_pow] at this
  · contrapose! hq
    rw [← h_odd.pow_nonneg_iff, ← hq]
    positivity

private theorem irrational_rpow_rat_rat_of_num {x y : ℝ} {x_num x_den y_num y_den k_num : ℕ}
    (hx_isNNRat : IsNNRat x x_num x_den)
    (hy_isNNRat : IsNNRat y y_num y_den)
    (hx_coprime : Nat.Coprime x_num x_den)
    (hy_coprime : Nat.Coprime y_num y_den)
    (hn1 : k_num ^ y_den < x_num)
    (hn2 : x_num < (k_num + 1) ^ y_den) :
    Irrational (x ^ y) := by
  have hy_den_pos : 0 < y_den := by
    by_contra! h
    simp only [nonpos_iff_eq_zero] at h
    simp only [h, pow_zero, Nat.lt_one_iff] at hn1 hn2
    omega
  rcases hx_isNNRat with ⟨hx_inv, hx_eq⟩
  rcases hy_isNNRat with ⟨hy_inv, hy_eq⟩
  rw [hy_eq, hx_eq]
  have h1 : (y_num * ⅟(y_den : ℝ) : ℝ) = ((y_num / y_den : ℚ) : ℝ) := by
    simp
    rfl
  have h2 : (x_num * ⅟(x_den : ℝ) : ℝ) = ((x_num / x_den : ℚ) : ℝ) := by
    simp
    rfl
  rw [h1, h2]
  refine irrational_rpow_rat_of_not_power ?_ hy_den_pos ?_
  · simp only [div_pow, ← Nat.cast_pow]
    apply not_power_rat_of_num
    · apply Nat.Coprime.pow _ _ hx_coprime
    · apply not_power_nat_pow_of_bounds hy_den_pos hy_coprime hn1 hn2
  · positivity

private theorem irrational_rpow_rat_rat_of_den {x y : ℝ} {x_num x_den y_num y_den k_den : ℕ}
    (hx_isNNRat : IsNNRat x x_num x_den)
    (hy_isNNRat : IsNNRat y y_num y_den)
    (hx_coprime : Nat.Coprime x_num x_den)
    (hy_coprime : Nat.Coprime y_num y_den)
    (hd1 : k_den ^ y_den < x_den)
    (hd2 : x_den < (k_den + 1) ^ y_den) :
    Irrational (x ^ y) := by
  rcases hx_isNNRat with ⟨hx_inv, hx_eq⟩
  apply Irrational.of_inv
  rw [← Real.inv_rpow (by simpa [hx_eq] using by positivity)]
  apply irrational_rpow_rat_rat_of_num (x_num := x_den) (x_den := x_num) _ hy_isNNRat
    (Nat.coprime_comm.mp hx_coprime) hy_coprime hd1 hd2
  refine ⟨invertibleOfNonzero (fun _ ↦ ?_), by simp [hx_eq]⟩
  simp_all

private theorem irrational_rpow_nat_rat {x y : ℝ} {x_num y_num y_den k : ℕ}
    (hx_isNat : IsNat x x_num)
    (hy_isNNRat : IsNNRat y y_num y_den)
    (hy_coprime : Nat.Coprime y_num y_den)
    (hn1 : k ^ y_den < x_num)
    (hn2 : x_num < (k + 1) ^ y_den) :
    Irrational (x ^ y) :=
  irrational_rpow_rat_rat_of_num hx_isNat.to_isNNRat hy_isNNRat (by simp) hy_coprime hn1 hn2

private theorem irrational_sqrt_rat_of_num {x : ℝ} {num den num_k : ℕ}
    (hx_isNNRat : IsNNRat x num den)
    (hx_coprime : Nat.Coprime num den)
    (hn1 : num_k ^ 2 < num)
    (hn2 : num < (num_k + 1) ^ 2) :
    Irrational (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_num hx_isNNRat (y_num := 1) (y_den := 2) _ hx_coprime (by simp)
    hn1 hn2
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

private theorem irrational_sqrt_rat_of_den {x : ℝ} {num den den_k : ℕ}
    (hx_isNNRat : IsNNRat x num den)
    (hx_coprime : Nat.Coprime num den)
    (hd1 : den_k ^ 2 < den)
    (hd2 : den < (den_k + 1) ^ 2) :
    Irrational (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_den hx_isNNRat (y_num := 1) (y_den := 2) _ hx_coprime (by simp)
    hd1 hd2
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

private theorem irrational_sqrt_nat {x : ℝ} {n k : ℕ}
    (hx_isNat : IsNat x n)
    (hn1 : k ^ 2 < n)
    (hn2 : n < (k + 1) ^ 2) :
    Irrational (Real.sqrt x) :=
  irrational_sqrt_rat_of_num hx_isNat.to_isNNRat (by simp) hn1 hn2

end lemmas

/-- To prove that `m` is not `n`-power (and thus `m ^ (1/n)` is irrational), we find `k` such that
`k ^ n < m < (k + 1) ^ n`. -/
structure NotPowerCertificate (m n : Q(ℕ)) where
  /-- Natural `k` such that `k ^ n < m < (k + 1) ^ n`. -/
  k : Q(ℕ)
  /-- Proof of `k ^ n < m`. -/
  pf_left : Q($k ^ $n < $m)
  /-- Proof of `m < (k + 1) ^ n`. -/
  pf_right : Q($m < ($k + 1) ^ $n)

/-- Finds `k` such that `k ^ n < m < (k + 1) ^ n` using bisection method. It assumes `n > 0`. -/
def findNotPowerCertificateCore (m n : ℕ) : Option ℕ := Id.run do
  let mut left := 0
  let mut right := m + 1
  while right - left > 1 do
    let middle := (left + right) / 2
    if middle ^ n ≤ m then
      left := middle
    else
      right := middle
  if left ^ n < m then
    return some left
  return none

/-- Finds `NotPowerCertificate` showing that `m` is not `n`-power. -/
def findNotPowerCertificate (m n : Q(ℕ)) : MetaM (NotPowerCertificate m n) := do
  let .isNat (_ : Q(AddMonoidWithOne ℕ)) m _ := ← derive m | failure
  let .isNat (_ : Q(AddMonoidWithOne ℕ)) n _ := ← derive n | failure
  let mVal := m.natLit!
  let nVal := n.natLit!
  let some k := findNotPowerCertificateCore mVal nVal | failure
  let .isBool true pf_left ← derive q($k ^ $n < $m) | failure
  let .isBool true pf_right ← derive q($m < ($k + 1) ^ $n) | failure
  return ⟨q($k), pf_left, pf_right⟩

/-- `norm_num` extension that proves `Irrational x ^ y` for rational `y`. `x` may be
natural or rational. -/
@[norm_num Irrational (_ ^ (_ : ℝ))]
def evalIrrationalRpow : NormNumExt where eval {u α} e := do
  let 0 := u | failure
  let ~q(Prop) := α | failure
  let ~q(Irrational (($x : ℝ) ^ ($y : ℝ))) := e | failure
  let .isNNRat sℝ _ y_num y_den y_isNNRat ← derive y | failure
  let ⟨gy, hy_coprime⟩ := proveNatGCD y_num y_den
  if gy.natLit! != 1 then failure
  let _ : $gy =Q 1 := ⟨⟩
  match ← derive x with
  | .isNat sℝ ex x_isNat =>
    let cert ← findNotPowerCertificate q($ex) y_den
    assumeInstancesCommute
    return .isTrue q(irrational_rpow_nat_rat $x_isNat $y_isNNRat $hy_coprime
      $cert.pf_left $cert.pf_right)
  | .isNNRat sℝ _ x_num x_den x_isNNRat =>
    let ⟨gx, hx_coprime⟩ := proveNatGCD x_num x_den
    if gx.natLit! != 1 then failure
    let _ : $gx =Q 1 := ⟨⟩
    let hx_isNNRat' : Q(IsNNRat $x $x_num $x_den) := x_isNNRat
    let hy_isNNRat' : Q(IsNNRat $y $y_num $y_den) := y_isNNRat
    try
      let numCert ← findNotPowerCertificate q($x_num) y_den
      assumeInstancesCommute
      return Result.isTrue q(irrational_rpow_rat_rat_of_num $hx_isNNRat' $hy_isNNRat'
        $hx_coprime $hy_coprime $numCert.pf_left $numCert.pf_right)
    catch _ =>
      let denCert ← findNotPowerCertificate q($x_den) y_den
      assumeInstancesCommute
      return Result.isTrue q(irrational_rpow_rat_rat_of_den $hx_isNNRat' $hy_isNNRat'
        $hx_coprime $hy_coprime $denCert.pf_left $denCert.pf_right)
  | _ => failure

/-- `norm_num` extension that proves `Irrational √x` for rational `x`. -/
@[norm_num Irrational (Real.sqrt _)]
def evalIrrationalSqrt : NormNumExt where eval {u α} e := do
  let 0 := u | failure
  let ~q(Prop) := α | failure
  let ~q(Irrational (√$x)) := e | failure
  match ← derive x with
  | .isNat sℝ ex pf =>
    let cert ← findNotPowerCertificate ex q(nat_lit 2)
    assumeInstancesCommute
    return .isTrue q(irrational_sqrt_nat $pf $cert.pf_left $cert.pf_right)
  | .isNNRat sℝ eq en ed pf =>
    let ⟨g, pf_coprime⟩ := proveNatGCD en ed
    if g.natLit! != 1 then failure
    let _ : $g =Q 1 := ⟨⟩
    try
      let numCert ← findNotPowerCertificate en q(nat_lit 2)
      assumeInstancesCommute
      return Result.isTrue
        q(irrational_sqrt_rat_of_num $pf $pf_coprime $numCert.pf_left $numCert.pf_right)
    catch _ =>
      let denCert ← findNotPowerCertificate ed q(nat_lit 2)
      assumeInstancesCommute
      return Result.isTrue
        q(irrational_sqrt_rat_of_den $pf $pf_coprime $denCert.pf_left $denCert.pf_right)
  | _ => failure

end NormNum

end Tactic
