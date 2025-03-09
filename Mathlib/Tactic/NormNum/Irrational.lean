/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.Rify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum.GCD


/-! # `norm_num` extension for `Nat.sqrt`

This module defines a `norm_num` extension for `Nat.sqrt`.
-/

namespace Tactic

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

structure NotPowerCertificate (m n : Q(ℕ)) where
  k : Q(ℕ)
  pf_left : Q($k^$n < $m)
  pf_right : Q($m < ($k + 1)^$n)

private theorem irrational_of_certificate_aux {x : ℝ} {m n k : ℕ}
    (hx : 0 ≤ x)
    (hn : 0 < n)
    (h1 : x^n = m)
    (h2 : k^n < m)
    (h3 : m < (k + 1)^n) :
    Irrational x := by
  apply irrational_nrt_of_notint_nrt n (m := m) _ _ hn
  · simpa
  intro ⟨k', h⟩
  rw [h] at h1 hx
  replace h1 : k' ^ n = m := by
    rify
    assumption
  zify at *
  rw [← h1] at h2 h3
  have : k < k' := by
    apply lt_of_pow_lt_pow_left₀ _ _ h2
    simpa using hx
  have : k' < (k + 1) := by
    apply lt_of_pow_lt_pow_left₀ _ _ h3
    simp at hx
    linarith
  linarith

private theorem irrational_of_certificate {x : ℝ} {m n k : ℕ}
    (hn : 0 < n)
    (h1 : x^n = m)
    (h2 : k^n < m)
    (h3 : m < (k + 1)^n) :
    Irrational x := by
  by_cases hx : 0 ≤ x
  · apply irrational_of_certificate_aux <;> assumption
  rw [← irrational_neg_iff]
  apply irrational_of_certificate_aux (by linarith) hn _ h2 h3
  rcases Nat.even_or_odd n with (h_even | h_odd)
  · rwa [h_even.neg_pow]
  · linarith [h_odd.pow_neg (show x < 0 by linarith)]

private theorem irrational_rpow_of_not_power {q : ℚ} {a b : ℕ}
    (h : ¬ ∃ p : ℚ, q^a = p^b) (hb : 0 < b) (hq : 0 ≤ q) :
    Irrational (Real.rpow q (a / b : ℚ)) := by
  simp at h
  simp [Irrational]
  intro x hx
  specialize h x
  absurd h
  rify
  rw [hx, ← Real.rpow_mul_natCast, div_mul_cancel₀]
  · simp
  · simp
    omega
  · simpa

private theorem not_power_nat_of_bounds {n k d : ℕ}
    (h_left : k^d < n)
    (h_right : n < (k + 1)^d) :
    ¬ ∃ m, n = m^d := by
  intro ⟨m, h⟩
  rw [h] at h_left h_right
  have : k < m := by exact lt_of_pow_lt_pow_left' d h_left
  have : m < k + 1 := by exact lt_of_pow_lt_pow_left' d h_right
  omega

private theorem not_power_rat_of_num_den {a b d : ℕ}
    (h_coprime : a.Coprime b)
    (ha : ¬ ∃ x, a = x^d)
    (hb : ¬ ∃ y, b = y^d) :
    ¬ ∃ q, 0 ≤ q ∧ (a / b : ℚ) = q^d := by
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
  obtain ⟨x, hx'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x' by sorry)
  rw [hx'] at h
  simp at ha hb
  specialize ha x
  specialize hb y
  simp [div_pow] at h
  rw [div_eq_div_iff] at h
  rotate_left
  · simpa
  · apply pow_ne_zero
    simp [y]
  sorry

private theorem irrational_rpow_rat_rat {x y : ℝ} {x_num x_den y_num y_den k_num k_den : ℕ}
    (hx_isRat : IsRat x (Int.ofNat x_num) x_den)
    (hy_isRat : IsRat y (Int.ofNat y_num) y_den)
    (hx_coprime : Nat.Coprime x_num x_den)
    (hn1 : k_num^y_den < x_num^y_num)
    (hn2 : x_num^y_num < (k_num + 1)^y_den)
    (hd1 : k_den^y_den < x_den^y_num)
    (hd2 : x_den^y_num < (k_den + 1)^y_den) :
    Irrational (x^y) := by
  rcases hx_isRat with ⟨hx_inv, hx_eq⟩
  rcases hy_isRat with ⟨hy_inv, hy_eq⟩
  rw [hy_eq]
  rw [Real.rpow_intCast_mul sorry]
  simp
  apply irrational_nrt_of_notint_nrt
  all_goals sorry

private theorem irrational_rpow_nat_rat {x y : ℝ} {x_num y_num y_den k : ℕ}
    (hx_isNat : IsNat x x_num)
    (hy_isRat : IsRat y (Int.ofNat y_num) y_den)
    (hn1 : k^y_den < x_num^y_num)
    (hn2 : x_num^y_num < (k + 1)^y_den) :
    Irrational (x^y) := by
  sorry

private theorem irrational_sqrt_rat {x : ℝ} {num den num_k den_k : ℕ}
    (hx_isRat : IsRat x (Int.ofNat num) den)
    (hx_coprime : Nat.Coprime num den)
    (hn1 : num_k^2 < num)
    (hn2 : num < (num_k + 1)^2)
    (hd1 : den_k^2 < den)
    (hd2 : den < (den_k + 1)^2) :
    Irrational (Real.sqrt x) := by
  sorry

private theorem irrational_sqrt_of_certificate {x : ℝ} {m k : ℕ}
    (h_isNat : IsNat x m)
    (h1 : k^2 < m)
    (h2 : m < (k + 1)^2) :
    Irrational (Real.sqrt x) := by
  rw [h_isNat.out]
  apply @irrational_of_certificate _ m 2 k
  · simp
  · simp
  all_goals assumption

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

def findNotPowerCertificate (m n : Q(ℕ)) : MetaM (NotPowerCertificate m n) := do
  let .isNat (_ : Q(AddMonoidWithOne ℕ)) m _ := ← derive m | failure
  let .isNat (_ : Q(AddMonoidWithOne ℕ)) n _ := ← derive n | failure
  let mVal := m.natLit!
  let nVal := n.natLit!
  let .some k := findNotPowerCertificateCore mVal nVal | failure
  let .isBool true pf_left ← derive q($k^$n < $m) | failure
  let .isBool true pf_right ← derive q($m < ($k + 1)^$n) | failure
  return ⟨q($k), pf_left, pf_right⟩

@[norm_num Irrational (Real.rpow _ _)]
def evalIrrationalRpow : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (Real.rpow $x $y)) =>
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
            have : $g =Q 1 := ⟨⟩
            let numCert ← findNotPowerCertificate q($x_num'^$y_num') y_den
            let denCert ← findNotPowerCertificate q($x_den^$y_num') y_den
            assumeInstancesCommute
            let x_isRat' : Q(IsRat $x (Int.ofNat $x_num') $x_den) := x_isRat
            let y_isRat' : Q(IsRat $y (Int.ofNat $y_num') $y_den) := y_isRat
            return .isTrue q(irrational_rpow_rat_rat $x_isRat' $y_isRat' $pf_coprime
              $numCert.pf_left $numCert.pf_right $denCert.pf_left $denCert.pf_right)
          | _ => failure
        | _ => failure
    | _ => failure
  | _ => failure

@[norm_num Irrational (Real.sqrt _)]
def evalIrrationalSqrt : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (Real.sqrt $x)) =>
    match ← derive x with
    | .isNat sℝ ex pf =>
      let cert ← findNotPowerCertificate ex q(nat_lit 2)
      assumeInstancesCommute
      return .isTrue q(irrational_sqrt_of_certificate $pf $cert.pf_left $cert.pf_right)
    | .isRat sℝ eq en ed pf =>
      match en with
      | ~q(Int.ofNat $n') =>
        let ⟨g, pf_coprime⟩ := proveNatGCD n' ed
        if g.natLit! != 1 then failure
        have : $g =Q 1 := ⟨⟩
        let numCert ← findNotPowerCertificate n' q(nat_lit 2)
        let denCert ← findNotPowerCertificate ed q(nat_lit 2)
        assumeInstancesCommute
        return .isTrue q(irrational_sqrt_rat $pf $pf_coprime $numCert.pf_left $numCert.pf_right
          $denCert.pf_left $denCert.pf_right)
      | _ => failure
    | _ => failure
  | _ => failure

end NormNum

end Tactic
