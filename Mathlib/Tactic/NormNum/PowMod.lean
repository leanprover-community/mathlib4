/-
Copyright (c) 2023 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Tactic.NormNum.Pow

/-!
# `norm_num` handling for expressions of the form `a ^ b % m`.

These expressions can often be evaluated efficiently in cases where first evaluating `a ^ b` and
then reducing mod `m` is not feasible. We provide a function `evalNatPowMod` which is used by the
`reduce_mod_char` tactic to efficiently evaluate powers in rings with positive characteristic.

The approach taken here is identical to (and copied from) the development in `NormNum/Pow.lean`.

## TODO

* Adapt the `norm_num` extensions for `Nat.mod` and `Int.emod` to efficiently evaluate expressions
  of the form `a ^ b % m` using `evalNatPowMod`.

-/

set_option autoImplicit true

namespace Mathlib
open Lean hiding Rat mkRat
open Meta

namespace Meta.NormNum
open Qq

structure IsNatPowModT (p : Prop) (a b m c : Nat) : Prop where
  run' : p → Nat.mod (Nat.pow a b) m = c

theorem IsNatPowModT.run (p : IsNatPowModT (Nat.mod (Nat.pow a (nat_lit 1)) m = Nat.mod a m) a b m c) :
  Nat.mod (Nat.pow a b) m = c := p.run' (congr_arg (fun x => x % m) (Nat.pow_one a))

theorem IsNatPowModT.trans (h1 : IsNatPowModT p a b m c)
    (h2 : IsNatPowModT (Nat.mod (Nat.pow a b) m = c) a b' m c') : IsNatPowModT p a b' m c' :=
  ⟨h2.run' ∘ h1.run'⟩

theorem IsNatPowModT.bit0 :
    IsNatPowModT (Nat.mod (Nat.pow a b) m = c) a (nat_lit 2 * b) m (Nat.mod (Nat.mul c c) m) :=
  ⟨fun h1 => by simpa [two_mul, pow_add, ← h1] using Nat.mul_mod _ _ _⟩

theorem natPow_zero_natMod_zero : Nat.mod (Nat.pow a (nat_lit 0)) (nat_lit 0) = 1 := rfl
theorem natPow_zero_natMod_one : Nat.mod (Nat.pow a (nat_lit 0)) (nat_lit 1) = 0 := rfl
theorem natPow_zero_natMod_succ_succ : Nat.mod (Nat.pow a (nat_lit 0)) (Nat.succ (Nat.succ m)) = 1 := by
  rw [natPow_zero]
  apply Nat.mod_eq_of_lt
  exact Nat.one_lt_succ_succ _
theorem zero_natPow_natMod : Nat.mod (Nat.pow (nat_lit 0) (Nat.succ b)) m = nat_lit 0 := by
  rw [zero_natPow]
  exact Nat.zero_mod _

theorem IsNatPowModT.bit1 :
    IsNatPowModT (Nat.mod (Nat.pow a b) m = c) a (nat_lit 2 * b + 1) m
      (Nat.mod (Nat.mul c (Nat.mod (Nat.mul c a) m)) m) :=
  ⟨by
    rintro rfl
    show a ^ (2 * b + 1) % m = (a ^ b % m) * ((a ^ b % m * a) % m) % m
    rw [pow_add, two_mul, pow_add, pow_one, Nat.mul_mod (a ^ b % m) a, Nat.mod_mod,
      ← Nat.mul_mod (a ^ b) a, ← Nat.mul_mod, mul_assoc]⟩

partial def evalNatPowMod (a b m : Q(ℕ)) : (c : Q(ℕ)) × Q(Nat.mod (Nat.pow $a $b) $m = $c) :=
  if b.natLit! = 0 then
    haveI : $b =Q 0 := ⟨⟩
    if m.natLit! = 0 then
      haveI : $m =Q 0 := ⟨⟩
      ⟨q(nat_lit 1), q(natPow_zero_natMod_zero)⟩
    else
      have m' : Q(ℕ) := mkRawNatLit (m.natLit! - 1)
      if m'.natLit! = 0 then
        haveI : $m =Q 1 := ⟨⟩
        ⟨q(nat_lit 0), q(natPow_zero_natMod_one)⟩
      else
        have m'' : Q(ℕ) := mkRawNatLit (m'.natLit! - 1)
        haveI : $m =Q Nat.succ (Nat.succ $m'') := ⟨⟩
        ⟨q(nat_lit 1), q(natPow_zero_natMod_succ_succ)⟩
  else if a.natLit! = 0 then
    haveI : $a =Q 0 := ⟨⟩
    have b' : Q(ℕ) := mkRawNatLit (b.natLit! - 1)
    haveI : $b =Q Nat.succ $b' := ⟨⟩
    ⟨q(nat_lit 0), q(zero_natPow_natMod)⟩
  else
    have c₀ : Q(ℕ) := mkRawNatLit (a.natLit! % m.natLit!)
    haveI : $c₀ =Q Nat.mod $a $m := ⟨⟩
    let ⟨c, p⟩ := go b.natLit!.log2 a m (mkRawNatLit 1) c₀ b
    ⟨c, q(($p).run)⟩
where
  /-- Invariants: `a ^ b₀ % m = c₀`, `depth > 0`, `b >>> depth = b₀` -/
  go (depth : Nat) (a m b₀ c₀ b : Q(ℕ)) :
      (c : Q(ℕ)) × Q(IsNatPowModT (Nat.mod (Nat.pow $a $b₀) $m = $c₀) $a $b $m $c) :=
    let b' := b.natLit!
    let m' := m.natLit!
    if depth ≤ 1 then
      let a' := a.natLit!
      let c₀' := c₀.natLit!
      if b' &&& 1 == 0 then
        have c : Q(ℕ) := mkRawNatLit ((c₀' * c₀') % m')
        haveI : $c =Q Nat.mod (Nat.mul $c₀ $c₀) $m := ⟨⟩
        haveI : $b =Q 2 * $b₀ := ⟨⟩
        ⟨c, q(IsNatPowModT.bit0)⟩
      else
        have c : Q(ℕ) := mkRawNatLit ((c₀' * ((c₀' * a') % m')) % m')
        haveI : $c =Q Nat.mod (Nat.mul $c₀ (Nat.mod (Nat.mul $c₀ $a) $m)) $m := ⟨⟩
        haveI : $b =Q 2 * $b₀ + 1 := ⟨⟩
        ⟨c, q(IsNatPowModT.bit1)⟩
    else
      let d := depth >>> 1
      have hi : Q(ℕ) := mkRawNatLit (b' >>> d)
      let ⟨c1, p1⟩ := go (depth - d) a m b₀ c₀ hi
      let ⟨c2, p2⟩ := go d a m hi c1 b
      ⟨c2, q(($p1).trans $p2)⟩
