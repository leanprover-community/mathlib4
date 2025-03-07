/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.Rify

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
  let mVal := m.natLit!
  let nVal := n.natLit!
  let .some k := findNotPowerCertificateCore mVal nVal | failure
  let .isBool true pf_left := ← derive q($k^$n < $m) | failure
  let .isBool true pf_right := ← derive q($m < ($k + 1)^$n) | failure
  return ⟨q($k), pf_left, pf_right⟩

@[norm_num Irrational (Real.sqrt _)]
def evalIrrationalSqrt : NormNumExt where eval {u α} e := do
  have inst : AddMonoidWithOne ℝ := by infer_instance
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (Real.sqrt $x)) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat (sℝ : Q(AddMonoidWithOne ℝ)) ex pf =>
      let cert ← findNotPowerCertificate ex q(nat_lit 2)
      assumeInstancesCommute
      return .isTrue q(irrational_sqrt_of_certificate $pf $cert.pf_left $cert.pf_right)
    | _ => failure
  | _ => failure

end NormNum

end Tactic
