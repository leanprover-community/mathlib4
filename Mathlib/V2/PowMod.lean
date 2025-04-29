/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum.PowMod

/-!
# Proof-producing evaluation of `a ^ b % n`

Note that `Mathlib.Tactic.NormNum.PowMod` contains a similar tactic, but that runs significantly
slower and less efficiently than the one here.
-/

open Nat

/-- The pow-mod function, named explicitly to allow more precise control of reduction. -/
def powMod (a b n : ℕ) : ℕ := a ^ b % n
/-- The pow-mod auxiliary function, named explicitly to allow more precise control of reduction. -/
def powModAux (a b c n : ℕ) : ℕ := (a ^ b * c) % n

lemma powModAux_zero_eq {a c n m : ℕ} (hm : c % n = m) : powModAux a 0 c n = m := by
  simpa [powModAux]

lemma powModAux_one_eq {a c n m : ℕ} (hm : (a * c) % n = m) : powModAux a 1 c n = m := by
  simp_all [powModAux]

lemma powModAux_even_eq {a a' b b' c n m : ℕ}
    (ha' : a * a % n = a') (hb' : 2 * b' = b)
    (h : powModAux a' b' c n = m) :
    powModAux a b c n = m := by
  rw [← ha', powModAux, mul_mod] at h
  rw [← hb', powModAux, pow_mul, mul_mod, pow_two, pow_mod, h]

lemma powModAux_odd_eq {a a' b b' c c' n m : ℕ}
    (hb' : 2 * b' + 1 = b) (ha' : a * a % n = a') (hc' : a * c % n = c')
    (h : powModAux a' b' c' n = m) :
    powModAux a b c n = m := by
  rw [← ha', ← hc', powModAux, mul_mod, mod_mod] at h
  rw [← hb', powModAux, pow_succ, pow_mul, mul_assoc, mul_mod, pow_mod, pow_two, h]

lemma powMod_eq {a b n m : ℕ} (h : powModAux a b 1 n = m) : powMod a b n = m := by
  simp_all [powModAux, powMod]

lemma powMod_ne {a b n m m' : ℕ} (hm : bne m' m) (h : powMod a b n = m') :
    powMod a b n ≠ m := by
  simp_all

namespace Tactic.powMod

open Lean Meta Elab Tactic

/-- Given `a, b, c, n : ℕ`, return `(m, ⊢ ℕ, ⊢ powModAux a b c n = m)`. -/
def mkPowModAuxEq (a b c n : ℕ) (aE bE cE nE : Expr) : MetaM (ℕ × Expr × Expr) :=
  if b = 0 then do
    let m : ℕ := c % n
    let mE : Expr := mkNatLit m
    let hm : Expr ← mkEqRefl mE
    return (m, mE, mkApp5 (mkConst ``powModAux_zero_eq []) aE cE nE mE hm)
  else if b = 1 then do
    let m : ℕ := (a * c) % n
    let mE : Expr := mkNatLit m
    let hm : Expr ← mkEqRefl mE
    return (m, mE, mkApp5 (mkConst ``powModAux_one_eq []) aE cE nE mE hm)
  else if Even b then do
    let b' := b / 2
    let a' := a * a % n
    let a'E := mkNatLit a'
    let b'E := mkNatLit b'
    let ha' : Expr ← mkEqRefl a'E
    let hb' : Expr ← mkEqRefl bE
    let (m, mE, eq) ← mkPowModAuxEq a' b' c n a'E b'E cE nE
    return (m, mE, mkApp10 (mkConst ``powModAux_even_eq []) aE a'E bE b'E cE nE mE ha' hb' eq)
  else do
    let a' := a * a % n
    let b' := b / 2
    let c' := a * c % n
    let a'E := mkNatLit a'
    let b'E := mkNatLit b'
    let c'E := mkNatLit c'
    let hb' : Expr ← mkEqRefl bE
    let ha' : Expr ← mkEqRefl a'E
    let hc' : Expr ← mkEqRefl c'E
    let (m, mE, eq) ← mkPowModAuxEq a' b' c' n a'E b'E c'E nE
    return (m, mE,
      mkApp5 (mkApp7 (mkConst ``powModAux_odd_eq []) aE a'E bE b'E cE c'E nE) mE hb' ha' hc' eq)

/-- Given `a, b, n : ℕ`, return `(m, ⊢ powMod a b n = m)`. -/
def mkPowModEq (a b n : ℕ) (aE bE nE : Expr) : MetaM (ℕ × Expr × Expr) := do
  let (m, mE, eq) ← mkPowModAuxEq a b 1 n aE bE (mkNatLit 1) nE
  return (m, mE, ← mkAppM ``powMod_eq #[eq])

/-- Given `a, b, n, m : ℕ`, if `powMod a b n = m` then return a proof of that fact. -/
def provePowModEq (a b n m : ℕ) (aE bE nE : Expr) : MetaM Expr := do
  let (m', _, eq) ← mkPowModEq a b n aE bE nE
  unless m = m' do throwError "attempted to prove {a} ^ {b} % {n} = {m} but it's actually {m'}"
  return eq

/-- Given `a, b, n, m : ℕ`, if `powMod a b n ≠ m` then return a proof of that fact. -/
def provePowModNe (a b n m : ℕ) (aE bE nE mE : Expr) : MetaM Expr := do
  let (m', m'E, eq) ← mkPowModEq a b n aE bE nE
  if m = m' then throwError "attempted to prove {a} ^ {b} % {n} ≠ {m} but it is {m'}"
  let ne := reflBoolTrue
  return mkApp7 (mkConst ``powMod_ne []) aE bE nE mE m'E ne eq

def extract_numerals (lhsE : Expr) : MetaM (ℕ × ℕ × ℕ) := do
  let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
  let some a := aE.nat? | throwError "base is not a numeral"
  let some b := bE.nat? | throwError "exponent is not a numeral"
  let some n := nE.nat? | throwError "modulus is not a numeral"
  return (a, b, n)

def prove_pow_mod_tac (g : MVarId) : MetaM Unit := do
  let t : Expr ← g.getType
  match_expr t with
  | Eq ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let pf ← provePowModEq a b n rhs aE bE nE
    g.assign pf
  | Ne ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let pf ← provePowModNe a b n rhs aE bE nE rhsE
    g.assign pf
  | _ => throwError "not an accepted expression"

elab "prove_pow_mod" : tactic =>
  liftMetaFinishingTactic prove_pow_mod_tac

end Tactic.powMod

example :
    powMod
      5
      85083351022467190124442353598696803287939269665616
      85083351022467190124442353598696803287939269665617 = 1 := by
  prove_pow_mod

example : powMod 2304821 1 2308 = 1437 := by
  prove_pow_mod

example : powMod 2 23408 2307 = 778 := by
  prove_pow_mod

example : powMod 2 23408 2307 ≠ 1 := by
  prove_pow_mod
