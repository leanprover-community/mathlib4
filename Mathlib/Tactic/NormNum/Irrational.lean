/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Rify
import Mathlib.Tactic.TautoSet

/-! # `norm_num` extension for `Irrational`

This module defines a `norm_num` extension for `Irrational x^y` for rational `x` and `y`. It also
supports `Irrational √x` expressions.

## Implementation details
To prove that `(a / b)^(p / q)` is irrational, we reduce the problem to showing that `(a / b)^p` is
not a `q`-th power of any rational number. This, in turn, reduces to proving that either `a^p` or
`b^p` is not a `q`-th power of a natural number. To show that a given `n : ℕ` is not a `q`-th power,
we find a natural number `k` such that `k^q < n < (k + 1)^q`, using binary search.

## TODO
Disprove `Irrational x` for rational `x`.

-/

namespace Tactic

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

section lemmas

private theorem irrational_rpow_rat_of_not_power {q : ℚ} {a b : ℕ}
    (h : ¬ ∃ p : ℚ, q^a = p^b) (hb : 0 < b) (hq : 0 ≤ q) :
    Irrational (Real.rpow q (a / b : ℚ)) := by
  simp only [not_exists] at h
  simp only [Irrational, Rat.cast_div, Rat.cast_natCast, Real.rpow_eq_pow, Set.mem_range,
    not_exists]
  intro x hx
  absurd h x
  rify
  rw [hx, ← Real.rpow_mul_natCast, div_mul_cancel₀] <;> simp
  · omega
  · assumption

private theorem not_power_nat_of_bounds {n k d : ℕ}
    (h_left : k^d < n)
    (h_right : n < (k + 1)^d) :
    ¬ ∃ m, n = m^d := by
  intro ⟨m, h⟩
  rw [h] at h_left h_right
  have : k < m := lt_of_pow_lt_pow_left' d h_left
  have : m < k + 1 := lt_of_pow_lt_pow_left' d h_right
  omega

/-- Weaker version of `not_power_rat_of_num_aux` with extra `q ≥ 0` assumption. -/
private theorem not_power_rat_of_num_aux {a b d : ℕ}
    (h_coprime : a.Coprime b)
    (ha : ¬ ∃ x, a = x^d) :
    ¬ ∃ q ≥ 0, (a / b : ℚ) = q^d := by
  by_cases hb_zero : b = 0
  · subst hb_zero
    simp at h_coprime
    subst h_coprime
    absurd ha
    use 1
    simp
  intro ⟨q, hq, h⟩
  rw [← Rat.num_div_den q] at h
  set x' := q.num
  set y := q.den
  obtain ⟨x, hx'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x' by rwa [Rat.num_nonneg])
  rw [hx'] at h
  simp at ha
  specialize ha x
  simp [div_pow] at h
  rw [div_eq_div_iff] at h
  rotate_left
  · simpa
  · apply pow_ne_zero
    simp [y]
  replace h : a * y ^ d = x ^ d * b := by
    qify
    assumption
  have hy_zero : y ≠ 0 := by simp [y]
  by_cases ha_zero : a = 0
  · subst ha_zero
    simp [hb_zero] at h
    simp [h.left, h.right] at ha
  by_cases hd_zero : d = 0
  · subst hd_zero
    simp at h ha
    simp [h] at h_coprime
    omega
  by_cases hx_zero : x = 0
  · subst hx_zero
    simp [zero_pow hd_zero] at h ha
    simp [ha, y] at h
  suffices a.factorization = (x ^ d).factorization by
    have := Nat.factorization_inj ha_zero (pow_ne_zero d hx_zero) this
    exact ha this
  apply_fun Nat.factorization at h
  obtain ⟨hax, hby, hay⟩ : a.primeFactors = x.primeFactors ∧ b.primeFactors = y.primeFactors ∧
      Disjoint a.primeFactors y.primeFactors := by
    apply_fun Finsupp.support at h
    simp [Nat.primeFactors_mul ha_zero (pow_ne_zero d hy_zero),
      Nat.primeFactors_mul (pow_ne_zero d hx_zero) hb_zero, Nat.primeFactors_pow _ hd_zero] at h
    have hab : a.primeFactors ∩ b.primeFactors = ∅ := by
      rwa [← Finset.disjoint_iff_inter_eq_empty, Nat.disjoint_primeFactors ha_zero hb_zero]
    have hxy : x.primeFactors ∩ y.primeFactors = ∅ := by
      rw [← Finset.disjoint_iff_inter_eq_empty, Nat.disjoint_primeFactors hx_zero hy_zero]
      have : x'.natAbs.Coprime y := Rat.reduced q
      simpa [hx'] using this
    apply_fun Finset.toSet at h hab hxy
    simp at h hab hxy
    constructorm* _ ∧ _
    · apply_fun Finset.toSet
      · tauto_set
      · exact Finset.coe_injective
    · apply_fun Finset.toSet
      · tauto_set
      · exact Finset.coe_injective
    · rw [← Finset.disjoint_coe]
      tauto_set
  rw [Finsupp.ext_iff']
  constructor
  · simpa [Finsupp.support_smul_eq hd_zero]
  intro p hp
  replace h : (a * y ^ d).factorization p = (x ^ d * b).factorization p := by
    rw [h]
  rw [Nat.factorization_mul ha_zero (pow_ne_zero d hy_zero)] at h
  rw [Nat.factorization_mul (pow_ne_zero d hx_zero) hb_zero] at h
  simp at h ⊢
  have hy0 : y.factorization p = 0 := by
    rw [← Finsupp.not_mem_support_iff]
    exact Disjoint.not_mem_of_mem_left_finset hay hp
  have hb0 : b.factorization p = 0 := by
    rw [← Finsupp.not_mem_support_iff, Nat.support_factorization]
    exact Disjoint.not_mem_of_mem_left_finset (Nat.Coprime.disjoint_primeFactors h_coprime) hp
  simpa [hy0, hb0] using h

private theorem not_power_rat_of_num {a b d : ℕ}
    (h_coprime : a.Coprime b)
    (ha : ¬ ∃ x, a = x^d) :
    ¬ ∃ q : ℚ, (a / b : ℚ) = q^d := by
  intro ⟨q, h_eq⟩
  by_cases hq : 0 ≤ q
  · have := not_power_rat_of_num_aux h_coprime ha
    push_neg at this
    specialize this q hq
    contradiction
  rcases d.even_or_odd with (h_even | h_odd)
  · have := not_power_rat_of_num_aux h_coprime ha
    push_neg at this
    specialize this (-q) (by linarith)
    rw [h_even.neg_pow] at this
    contradiction
  · have : 0 ≤ q ^ d := by
      rw [← h_eq]
      positivity
    rw [h_odd.pow_nonneg_iff] at this
    contradiction

private theorem irrational_rpow_rat_rat_of_num {x y : ℝ} {x_num x_den y_num y_den k_num : ℕ}
    (hx_isRat : IsRat x (Int.ofNat x_num) x_den)
    (hy_isRat : IsRat y (Int.ofNat y_num) y_den)
    (hx_coprime : Nat.Coprime x_num x_den)
    (hn1 : k_num^y_den < x_num^y_num)
    (hn2 : x_num^y_num < (k_num + 1)^y_den) :
    Irrational (x^y) := by
  rcases hx_isRat with ⟨hx_inv, hx_eq⟩
  rcases hy_isRat with ⟨hy_inv, hy_eq⟩
  rw [hy_eq, hx_eq]
  have h1 : ((Int.ofNat y_num) * ⅟(y_den : ℝ) : ℝ) = ((y_num / y_den : ℚ) : ℝ) := by
    simp
    rfl
  have h2 : ((Int.ofNat x_num) * ⅟(x_den : ℝ) : ℝ) = ((x_num / x_den : ℚ) : ℝ) := by
    simp
    rfl
  rw [h1, h2]
  apply irrational_rpow_rat_of_not_power
  · simp only [div_pow, ← Nat.cast_npow]
    apply not_power_rat_of_num
    · apply Nat.Coprime.pow _ _ hx_coprime
    · apply not_power_nat_of_bounds hn1 hn2
  · by_contra hy_den
    replace hy_den : y_den = 0 := by omega
    have : (y_den : ℝ) ≠ 0 := by apply hy_inv.ne_zero
    simp at this
    contradiction
  · positivity

private theorem irrational_rpow_rat_rat_of_den {x y : ℝ} {x_num x_den y_num y_den k_den : ℕ}
    (hx_isRat : IsRat x (Int.ofNat x_num) x_den)
    (hy_isRat : IsRat y (Int.ofNat y_num) y_den)
    (hx_coprime : Nat.Coprime x_num x_den)
    (hd1 : k_den^y_den < x_den^y_num)
    (hd2 : x_den^y_num < (k_den + 1)^y_den) :
    Irrational (x^y) := by
  rcases hx_isRat with ⟨hx_inv, hx_eq⟩
  apply Irrational.of_inv
  rw [← Real.inv_rpow (by simp [hx_eq]; positivity)]
  apply irrational_rpow_rat_rat_of_num (x_num := x_den) (x_den := x_num) _ hy_isRat
    (Nat.coprime_comm.mp hx_coprime) hd1 hd2
  refine ⟨invertibleOfNonzero (fun _ ↦ ?_), by simp [hx_eq]⟩
  simp_all

private theorem irrational_rpow_nat_rat {x y : ℝ} {x_num y_num y_den k : ℕ}
    (hx_isNat : IsNat x x_num)
    (hy_isRat : IsRat y (Int.ofNat y_num) y_den)
    (hn1 : k^y_den < x_num^y_num)
    (hn2 : x_num^y_num < (k + 1)^y_den) :
    Irrational (x^y) :=
  irrational_rpow_rat_rat_of_num hx_isNat.to_isRat hy_isRat (by simp) hn1 hn2

private theorem irrational_sqrt_rat_of_num {x : ℝ} {num den num_k : ℕ}
    (hx_isRat : IsRat x (Int.ofNat num) den)
    (hx_coprime : Nat.Coprime num den)
    (hn1 : num_k^2 < num)
    (hn2 : num < (num_k + 1)^2) :
    Irrational (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_num hx_isRat (y_num := 1) (y_den := 2) <;> try simpa
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

private theorem irrational_sqrt_rat_of_den {x : ℝ} {num den den_k : ℕ}
    (hx_isRat : IsRat x (Int.ofNat num) den)
    (hx_coprime : Nat.Coprime num den)
    (hd1 : den_k^2 < den)
    (hd2 : den < (den_k + 1)^2) :
    Irrational (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_den hx_isRat (y_num := 1) (y_den := 2) <;> try simpa
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

private theorem irrational_sqrt_nat {x : ℝ} {n k : ℕ}
    (hx_isNat : IsNat x n)
    (hn1 : k^2 < n)
    (hn2 : n < (k + 1)^2) :
    Irrational (Real.sqrt x) :=
  irrational_sqrt_rat_of_num hx_isNat.to_isRat (by simp) hn1 hn2

end lemmas

/-- To prove that `m` is not `n`-power (and thus `m^(1/n)` is irrational), we find `k` such that
`k^n < m < (k + 1)^n`. -/
structure NotPowerCertificate (m n : Q(ℕ)) where
  /-- Natural `k` such that `k^n < m < (k + 1)^n`. -/
  k : Q(ℕ)
  /-- Proof of `k^n < m`. -/
  pf_left : Q($k^$n < $m)
  /-- Proof of `m < (k + 1)^n`. -/
  pf_right : Q($m < ($k + 1)^$n)

/-- Finds `k` such that `k^n < m < (k + 1)^n` using bisection method. -/
def findNotPowerCertificateCore (m n : ℕ) : Option ℕ := Id.run do
  let mut left := 0
  let mut right := m + 1
  while right - left > 1 do
    let middle := (left + right) / 2
    if middle^n ≤ m then
      left := middle
    else
      right := middle
  if left^n < m then
    return .some left
  return .none

/-- Finds `NotPowerCertificate` showing that `m` is not `n`-power. -/
def findNotPowerCertificate (m n : Q(ℕ)) : MetaM (NotPowerCertificate m n) := do
  let .isNat (_ : Q(AddMonoidWithOne ℕ)) m _ := ← derive m | failure
  let .isNat (_ : Q(AddMonoidWithOne ℕ)) n _ := ← derive n | failure
  let mVal := m.natLit!
  let nVal := n.natLit!
  let .some k := findNotPowerCertificateCore mVal nVal | failure
  let .isBool true pf_left ← derive q($k^$n < $m) | failure
  let .isBool true pf_right ← derive q($m < ($k + 1)^$n) | failure
  return ⟨q($k), pf_left, pf_right⟩

/-- `norm_num` extension that proves `Irrational x^y` for rational `x` and `y`. -/
@[norm_num Irrational (_ ^ (_ : ℝ))]
def evalIrrationalRpow : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (($x : ℝ) ^ ($y : ℝ))) =>
    match ← derive y with
    | .isRat sℝ _ y_num y_den y_isRat =>
      match y_num with
      | ~q(Int.ofNat $y_num') =>
        match ← derive x with
        | .isNat sℝ ex x_isNat =>
          let cert ← findNotPowerCertificate q($ex^$y_num') y_den
          assumeInstancesCommute
          return .isTrue q(irrational_rpow_nat_rat $x_isNat $y_isRat $cert.pf_left $cert.pf_right)
        | .isRat sℝ _ x_num x_den x_isRat =>
          match x_num with
          | ~q(Int.ofNat $x_num') =>
            let ⟨g, pf_coprime⟩ := proveNatGCD x_num' x_den
            if g.natLit! != 1 then failure
            let _ : $g =Q 1 := ⟨⟩
            let x_isRat' : Q(IsRat $x (Int.ofNat $x_num') $x_den) := x_isRat
            let y_isRat' : Q(IsRat $y (Int.ofNat $y_num') $y_den) := y_isRat
            try
              let numCert ← findNotPowerCertificate q($x_num'^$y_num') y_den
              assumeInstancesCommute
              return .isTrue q(irrational_rpow_rat_rat_of_num $x_isRat' $y_isRat' $pf_coprime
                $numCert.pf_left $numCert.pf_right)
            catch _ =>
              let denCert ← findNotPowerCertificate q($x_den^$y_num') y_den
              assumeInstancesCommute
              return .isTrue q(irrational_rpow_rat_rat_of_den $x_isRat' $y_isRat' $pf_coprime
                $denCert.pf_left $denCert.pf_right)
          | _ => failure
        | _ => failure
    | _ => failure
  | _ => failure

/-- `norm_num` extension that proves `Irrational √x` for rational `x`. -/
@[norm_num Irrational (Real.sqrt _)]
def evalIrrationalSqrt : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (Real.sqrt $x)) =>
    match ← derive x with
    | .isNat sℝ ex pf =>
      let cert ← findNotPowerCertificate ex q(nat_lit 2)
      assumeInstancesCommute
      return .isTrue q(irrational_sqrt_nat $pf $cert.pf_left $cert.pf_right)
    | .isRat sℝ eq en ed pf =>
      match en with
      | ~q(Int.ofNat $n') =>
        let ⟨g, pf_coprime⟩ := proveNatGCD n' ed
        if g.natLit! != 1 then failure
        let _ : $g =Q 1 := ⟨⟩
        try
          let numCert ← findNotPowerCertificate n' q(nat_lit 2)
          assumeInstancesCommute
          return .isTrue q(irrational_sqrt_rat_of_num $pf $pf_coprime $numCert.pf_left
            $numCert.pf_right)
        catch _ =>
          let denCert ← findNotPowerCertificate ed q(nat_lit 2)
          assumeInstancesCommute
          return .isTrue q(irrational_sqrt_rat_of_den $pf $pf_coprime $denCert.pf_left
            $denCert.pf_right)
      | _ => failure
    | _ => failure
  | _ => failure

end NormNum

end Tactic
