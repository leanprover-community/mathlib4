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
    (ha' : a * a % n = a') (hb' : b' <<< 1 = b)
    (h : powModAux a' b' c n = m) :
    powModAux a b c n = m := by
  rw [← ha', powModAux, mul_mod] at h
  rw [Nat.shiftLeft_eq, mul_comm, pow_one] at hb'
  rw [← hb', powModAux, pow_mul, mul_mod, pow_two, pow_mod, h]

lemma powModAux_odd_eq {a a' b b' c c' n m : ℕ}
    (hb' : 2 * b' + 1 = b) (ha' : a * a % n = a') (hc' : a * c % n = c')
    (h : powModAux a' b' c' n = m) :
    powModAux a b c n = m := by
  rw [← ha', ← hc', powModAux, mul_mod, mod_mod] at h
  rw [← hb', powModAux, pow_succ, pow_mul, mul_assoc, mul_mod, pow_mod, pow_two, h]

lemma powMod_eq (a : ℕ) {a' b n m : ℕ} (h : powModAux a' b 1 n = m) (ha : a % n = a') :
    powMod a b n = m := by
  rwa [powModAux, mul_one, ← ha, pow_mod, mod_mod, ← pow_mod] at h

lemma powMod_ne {a b n m : ℕ} (m' : ℕ) (hm : bne m' m) (h : powMod a b n = m') :
    powMod a b n ≠ m := by
  simp_all

def powModTR (a b n : ℕ) : ℕ :=
  aux (a % n) b 1 (b + 1) (by omega) where
  aux (a b c : ℕ) (fuel : ℕ) (hfuel : b < fuel) : ℕ :=
    match fuel with
    | 0 => by omega
    | fuel + 1 =>
      if hb : b = 0 then c % n
      else if b = 1 then (a * c) % n
      else if b % 2 = 0 then
        aux (a * a % n) (b / 2) c fuel (by omega)
      else
        aux (a * a % n) (b / 2) (a * c % n) fuel (by omega)

set_option allowUnsafeReducibility true

@[semireducible]
partial def aux (n a b c : ℕ) : ℕ :=
    if b = 0 then c % n
    else if b = 1 then (a * c) % n
    else if b % 2 = 0 then
      aux n (a * a % n) (b / 2) c
    else
      aux n (a * a % n) (b / 2) (a * c % n)

def powModTR' (a b n : ℕ) : ℕ :=
  let rec @[semireducible] aux (a b c : ℕ) : ℕ :=
    if b = 0 then c % n
    else if b = 1 then (a * c) % n
    else if b % 2 = 0 then
      aux (a * a % n) (b / 2) c
    else
      aux (a * a % n) (b / 2) (a * c % n)
    partial_fixpoint
  aux (a % n) b 1

-- #print powModTR'.aux

-- #exit

lemma powModTR_aux_congr (n a b c fuel1 fuel2) (hfuel1 : b < fuel1) (hfuel2 : b < fuel2) :
    powModTR.aux n a b c fuel1 hfuel1 = powModTR.aux n a b c fuel2 hfuel2 :=
  match fuel1, fuel2 with
  | 0, _ => by omega
  | _, 0 => by omega
  | fuel1 + 1, fuel2 + 1 => by
    simp only [powModTR.aux]
    split
    · simp
    split
    · simp
    split
    · rw [powModTR_aux_congr]
    · rw [powModTR_aux_congr]

lemma powModTR_aux_eq (n a b c fuel) (hfuel : b < fuel) :
    powModTR.aux n a b c fuel hfuel = powModAux a b c n := by
  induction a, b, c, fuel, hfuel using powModTR.aux.induct n with
  | case1 a b c hfuel => omega
  | case2 a c fuel hfuel =>
    rw [powModTR.aux, dif_pos rfl]
    exact (powModAux_zero_eq rfl).symm
  | case3 a c fuel hfuel h =>
    rw [powModTR.aux, dif_neg h, if_pos rfl]
    exact (powModAux_one_eq rfl).symm
  | case4 a b c fuel hfuel h₁ h₂ h₃ ih1 =>
    rw [powModTR.aux, dif_neg h₁, if_neg h₂, if_pos h₃, ih1]
    exact (powModAux_even_eq rfl (by omega) rfl).symm
  | case5 a b c fuel hfuel h₁ h₂ h₃ ih1 =>
    rw [powModTR.aux, dif_neg h₁, if_neg h₂, if_neg h₃, ih1]
    exact (powModAux_odd_eq (by omega) rfl rfl rfl).symm

lemma powModTR_eq (a b n) :
    powModTR a b n = powMod a b n := by
  apply (powMod_eq _ _ rfl).symm
  rw [powModTR, powModTR_aux_eq]

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
  let a' := a % n
  let a'E := mkNatLit a'
  let (m, mE, eq) ← mkPowModAuxEq a' b 1 n a'E bE (mkNatLit 1) nE
  return (m, mE, ← mkAppM ``powMod_eq #[aE, eq, ← mkEqRefl a'E])

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

macro "prove_pow_mod2" : tactic => `(tactic| {rw [← powModTR_eq]; decide +native})

#time
example :
    powMod 2
      2112421871326486211461011031931945323874719289347729538762174157135451276986
      2112421871326486211461011031931945323874719289347729538762174157135451276987 =
      1 := by
  prove_pow_mod

#time
example :
    powMod 2
      2112421871326486211461011031931945323874719289347729538762174157135451276986
      2112421871326486211461011031931945323874719289347729538762174157135451276987 =
      1 := by
  prove_pow_mod2

#exit

example : powMod 2304821 1 2308 = 1437 := by
  prove_pow_mod

example : powMod 2 23408 2307 = 778 := by
  prove_pow_mod

example : powMod 2 23408 2307 ≠ 1 := by
  prove_pow_mod

example : powMod 2 385273928 1000000007 = 3 := by
  prove_pow_mod
