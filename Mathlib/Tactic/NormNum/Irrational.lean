/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.NormNum.Prime

/-! # `norm_num` extension for `Nat.sqrt`

This module defines a `norm_num` extension for `Nat.sqrt`.
-/

namespace Tactic

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

structure NotPowerCertificate (m n : Q(ℕ)) where
  p : Q(ℕ)
  q : Q(ℕ)
  k : Q(ℕ)
  pf1 : Q($m = $p^$k * $q)
  pf2 : Q($m ≠ 0)
  pf3 : Q($q % $p ≠ 0)
  pf4 : Q($k % $n ≠ 0)
  pf5 : Q(Nat.Prime $p)

def findNotPowerCertificateCore (m n : ℕ) : Option (ℕ × ℕ × ℕ) := Id.run do
  let mut x := m
  let mut p := 2
  let mut k := 0
  while x > 1 do
    if x % p == 0 then
      k := k + 1
      x := x / p
    else
      if k > 0 && k % n ≠ 0 then
        return .some (p, m / p^k, k)
      k := 0
      p := p + 1
  if k > 0 && k % n ≠ 0 then
    return .some (p, m / p^k, k)
  return .none

def findNotPowerCertificate (m n : Q(ℕ)) : MetaM (NotPowerCertificate m n) := do
  let mVal := m.natLit!
  let nVal := n.natLit!
  let .some (p, q, k) := findNotPowerCertificateCore mVal nVal | failure
  let pf1 : Q($m = $p^$k * $q) := (q(Eq.refl $m) : Expr)

  let .isBool _ pf2 := ← derive q($m ≠ 0) | failure
  let .isBool _ pf3 := ← derive q($q % $p ≠ 0) | failure
  let .isBool _ pf4 ← derive q($k % $n ≠ 0) | failure
  let .isBool _ pf5 ← derive q(Nat.Prime $p) | failure
  return ⟨q($p), q($q), q($k), pf1, pf2, pf3, pf4, pf5⟩

private theorem irrational_of_certificate (x : ℝ) (m n p q k : ℕ)
    (h1 : x^n = m)
    (h2 : m ≠ 0)
    (h3 : m = p^k * q)
    (h4 : q % p ≠ 0)
    (h5 : k % n ≠ 0)
    (h6 : p.Prime) :
    Irrational x := by
  have _ : Fact (Nat.Prime p) := ⟨h6⟩
  apply irrational_nrt_of_n_not_dvd_multiplicity n _ p
  · exact h1
  · convert h5
    rw [FiniteMultiplicity.multiplicity_eq_iff]
    · constructor
      · simp [h3]
      · simp [h3, pow_succ]
        rw [Int.mul_dvd_mul_iff_left]
        · rwa [Int.ofNat_dvd, Nat.dvd_iff_mod_eq_zero]
        · apply pow_ne_zero
          simp
          exact Nat.Prime.ne_zero h6
    · rw [Int.finiteMultiplicity_iff]
      simp [h2]
      exact Nat.Prime.ne_one h6
  · exact Int.ofNat_ne_zero.mpr h2

private theorem irrational_sqrt_of_certificate {m p q k : ℕ}
    (h1 : m = p^k * q)
    (h2 : m ≠ 0)
    (h3 : q % p ≠ 0)
    (h4 : k % 2 ≠ 0)
    (h5 : p.Prime) :
    Irrational (Real.sqrt m) := by
  apply irrational_of_certificate _ m 2 p q k
  · simp
  all_goals assumption

@[norm_num Irrational (Real.sqrt _)]
def evalIrrationalSqrt : NormNumExt where eval {u α} e := do
  have inst : AddMonoidWithOne ℝ := by infer_instance
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (Real.sqrt $x)) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat (sℝ : Q(AddMonoidWithOne ℝ)) ex pf =>
      let cert ← findNotPowerCertificate ex q(nat_lit 2)
      return .isTrue q(irrational_sqrt_of_certificate $cert.pf1 $cert.pf2 $cert.pf3 $cert.pf4
        $cert.pf5)
    | _ => failure
  | _ => failure

end NormNum

end Tactic
