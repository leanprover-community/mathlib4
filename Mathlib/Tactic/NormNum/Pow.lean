/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.NormNum.Basic

/-!
## `norm_num` plugin for `^`.
-/

set_option autoImplicit true

namespace Mathlib
open Lean hiding Rat mkRat
open Meta

namespace Meta.NormNum
open Qq

theorem natPow_zero : Nat.pow a (nat_lit 0) = nat_lit 1 := rfl
theorem natPow_one : Nat.pow a (nat_lit 1) = a := Nat.pow_one _
theorem zero_natPow : Nat.pow (nat_lit 0) (Nat.succ b) = nat_lit 0 := rfl
theorem one_natPow : Nat.pow (nat_lit 1) b = nat_lit 1 := Nat.one_pow _

/-- This is an opaque wrapper around `Nat.pow` to prevent lean from unfolding the definition of
`Nat.pow` on numerals. The arbitrary precondition `p` is actually a formula of the form
`Nat.pow a' b' = c'` but we usually don't care to unfold this proposition so we just carry a
reference to it. -/
structure IsNatPowT (p : Prop) (a b c : Nat) : Prop where
  /-- Unfolds the assertion. -/
  run' : p → Nat.pow a b = c

theorem IsNatPowT.run
    (p : IsNatPowT (Nat.pow a (nat_lit 1) = a) a b c) : Nat.pow a b = c := p.run' (Nat.pow_one _)

/-- This is the key to making the proof proceed as a balanced tree of applications instead of
a linear sequence. It is just modus ponens after unwrapping the definitions. -/
theorem IsNatPowT.trans (h1 : IsNatPowT p a b c) (h2 : IsNatPowT (Nat.pow a b = c) a b' c') :
    IsNatPowT p a b' c' := ⟨h2.run' ∘ h1.run'⟩

theorem IsNatPowT.bit0 : IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b) (Nat.mul c c) :=
  ⟨fun h1 => by simp [two_mul, pow_add, ← h1]⟩
theorem IsNatPowT.bit1 :
    IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b + nat_lit 1) (Nat.mul c (Nat.mul c a)) :=
  ⟨fun h1 => by simp [two_mul, pow_add, mul_assoc, ← h1]⟩

/--
Proves `Nat.pow a b = c` where `a` and `b` are raw nat literals. This could be done by just
`rfl` but the kernel does not have a special case implementation for `Nat.pow` so this would
proceed by unary recursion on `b`, which is too slow and also leads to deep recursion.

We instead do the proof by binary recursion, but this can still lead to deep recursion,
so we use an additional trick to do binary subdivision on `log2 b`. As a result this produces
a proof of depth `log (log b)` which will essentially never overflow before the numbers involved
themselves exceed memory limits.
-/
partial def evalNatPow (a b : Q(ℕ)) : (c : Q(ℕ)) × Q(Nat.pow $a $b = $c) :=
  if b.natLit! = 0 then
    haveI : $b =Q 0 := ⟨⟩
    ⟨q(nat_lit 1), q(natPow_zero)⟩
  else if a.natLit! = 0 then
    haveI : $a =Q 0 := ⟨⟩
    have b' : Q(ℕ) := mkRawNatLit (b.natLit! - 1)
    haveI : $b =Q Nat.succ $b' := ⟨⟩
    ⟨q(nat_lit 0), q(zero_natPow)⟩
  else if a.natLit! = 1 then
    haveI : $a =Q 1 := ⟨⟩
    ⟨q(nat_lit 1), q(one_natPow)⟩
  else if b.natLit! = 1 then
    haveI : $b =Q 1 := ⟨⟩
    ⟨a, q(natPow_one)⟩
  else
    let ⟨c, p⟩ := go b.natLit!.log2 a (mkRawNatLit 1) a b _ .rfl
    ⟨c, q(($p).run)⟩
where
  /-- Invariants: `a ^ b₀ = c₀`, `depth > 0`, `b >>> depth = b₀`, `p := Nat.pow $a $b₀ = $c₀` -/
  go (depth : Nat) (a b₀ c₀ b : Q(ℕ)) (p : Q(Prop)) (hp : $p =Q (Nat.pow $a $b₀ = $c₀)) :
      (c : Q(ℕ)) × Q(IsNatPowT $p $a $b $c) :=
    let b' := b.natLit!
    if depth ≤ 1 then
      let a' := a.natLit!
      let c₀' := c₀.natLit!
      if b' &&& 1 == 0 then
        have c : Q(ℕ) := mkRawNatLit (c₀' * c₀')
        haveI : $c =Q Nat.mul $c₀ $c₀ := ⟨⟩
        haveI : $b =Q 2 * $b₀ := ⟨⟩
        ⟨c, q(IsNatPowT.bit0)⟩
      else
        have c : Q(ℕ) := mkRawNatLit (c₀' * (c₀' * a'))
        haveI : $c =Q Nat.mul $c₀ (Nat.mul $c₀ $a) := ⟨⟩
        haveI : $b =Q 2 * $b₀ + 1 := ⟨⟩
        ⟨c, q(IsNatPowT.bit1)⟩
    else
      let d := depth >>> 1
      have hi : Q(ℕ) := mkRawNatLit (b' >>> d)
      let ⟨c1, p1⟩ := go (depth - d) a b₀ c₀ hi p (by exact hp)
      let ⟨c2, p2⟩ := go d a hi c1 b q(Nat.pow $a $hi = $c1) ⟨⟩
      ⟨c2, q(($p1).trans $p2)⟩

theorem intPow_ofNat (h1 : Nat.pow a b = c) :
    Int.pow (Int.ofNat a) b = Int.ofNat c := by simp [← h1]

theorem intPow_negOfNat_bit0 (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' = b) (hc : c' * c' = c) :
    Int.pow (Int.negOfNat a) b = Int.ofNat c := by
  rw [← hb, Int.negOfNat_eq, Int.pow_eq, pow_mul, neg_pow_two, ← pow_mul, two_mul, pow_add, ← hc,
    ← h1]
  simp

theorem intPow_negOfNat_bit1 (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' + nat_lit 1 = b) (hc : c' * (c' * a) = c) :
    Int.pow (Int.negOfNat a) b = Int.negOfNat c := by
  rw [← hb, Int.negOfNat_eq, Int.negOfNat_eq, Int.pow_eq, pow_succ, pow_mul, neg_pow_two, ← pow_mul,
    two_mul, pow_add, ← hc, ← h1]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- Evaluates `Int.pow a b = c` where `a` and `b` are raw integer literals. -/
partial def evalIntPow (za : ℤ) (a : Q(ℤ)) (b : Q(ℕ)) : ℤ × (c : Q(ℤ)) × Q(Int.pow $a $b = $c) :=
  have a' : Q(ℕ) := a.appArg!
  if 0 ≤ za then
    haveI : $a =Q .ofNat $a' := ⟨⟩
    let ⟨c, p⟩ := evalNatPow a' b
    ⟨c.natLit!, q(.ofNat $c), q(intPow_ofNat $p)⟩
  else
    haveI : $a =Q .negOfNat $a' := ⟨⟩
    let b' := b.natLit!
    have b₀ : Q(ℕ) := mkRawNatLit (b' >>> 1)
    let ⟨c₀, p⟩ := evalNatPow a' b₀
    let c' := c₀.natLit!
    if b' &&& 1 == 0 then
      have c : Q(ℕ) := mkRawNatLit (c' * c')
      have pc : Q($c₀ * $c₀ = $c) := (q(Eq.refl $c) : Expr)
      have pb : Q(2 * $b₀ = $b) := (q(Eq.refl $b) : Expr)
      ⟨c.natLit!, q(.ofNat $c), q(intPow_negOfNat_bit0 $p $pb $pc)⟩
    else
      have c : Q(ℕ) := mkRawNatLit (c' * (c' * a'.natLit!))
      have pc : Q($c₀ * ($c₀ * $a') = $c) := (q(Eq.refl $c) : Expr)
      have pb : Q(2 * $b₀ + 1 = $b) := (q(Eq.refl $b) : Expr)
      ⟨-c.natLit!, q(.negOfNat $c), q(intPow_negOfNat_bit1 $p $pb $pc)⟩

-- see note [norm_num lemma function equality]
theorem isNat_pow {α} [Semiring α] : ∀ {f : α → ℕ → α} {a : α} {b a' b' c : ℕ},
    f = HPow.hPow → IsNat a a' → IsNat b b' → Nat.pow a' b' = c → IsNat (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

-- see note [norm_num lemma function equality]
theorem isInt_pow {α} [Ring α] : ∀ {f : α → ℕ → α} {a : α} {b : ℕ} {a' : ℤ} {b' : ℕ} {c : ℤ},
    f = HPow.hPow → IsInt a a' → IsNat b b' → Int.pow a' b' = c → IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

-- see note [norm_num lemma function equality]
theorem isRat_pow {α} [Ring α] {f : α → ℕ → α} {a : α} {an cn : ℤ} {ad b b' cd : ℕ} :
    f = HPow.hPow → IsRat a an ad → IsNat b b' →
    Int.pow an b' = cn → Nat.pow ad b' = cd →
    IsRat (f a b) cn cd := by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow]

/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℕ`. -/
@[norm_num (_ : α) ^ (_ : ℕ)]
def evalPow : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → ℕ → $α)) (a : Q($α))) (b : Q(ℕ)) ← whnfR e | failure
  let ⟨nb, pb⟩ ← deriveNat b q(instAddMonoidWithOneNat)
  let sα ← inferSemiring α
  let ra ← derive a
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := $α))
  haveI' : $e =Q $a ^ $b := ⟨⟩
  haveI' : $f =Q HPow.hPow := ⟨⟩
  let rec
  /-- Main part of `evalPow`. -/
  core : Option (Result e) := do
    match ra with
    | .isBool .. => failure
    | .isNat sα na pa =>
      assumeInstancesCommute
      have ⟨c, r⟩ := evalNatPow na nb
      return .isNat sα c q(isNat_pow (f := $f) (.refl $f) $pa $pb $r)
    | .isNegNat rα .. =>
      assumeInstancesCommute
      let ⟨za, na, pa⟩ ← ra.toInt rα
      have ⟨zc, c, r⟩ := evalIntPow za na nb
      return .isInt rα c zc q(isInt_pow (f := $f) (.refl $f) $pa $pb $r)
    | .isRat dα qa na da pa =>
      assumeInstancesCommute
      have ⟨zc, nc, r1⟩ := evalIntPow qa.num na nb
      have ⟨dc, r2⟩ := evalNatPow da nb
      let qc := mkRat zc dc.natLit!
      return .isRat' dα qc nc dc q(isRat_pow (f := $f) (.refl $f) $pa $pb $r1 $r2)
  core

theorem isNat_zpow_pos {α : Type*} [DivisionSemiring α] {a : α} {b : ℤ} {nb ne : ℕ}
    (pb : IsNat b nb) (pe' : IsNat (a ^ nb) ne) :
    IsNat (a ^ b) ne := by
  rwa [pb.out, zpow_natCast]

theorem isNat_zpow_neg {α : Type*} [DivisionSemiring α] {a : α} {b : ℤ} {nb ne : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNat (a ^ nb)⁻¹ ne) :
    IsNat (a ^ b) ne := by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

theorem isInt_zpow_pos {α : Type*} [DivisionRing α] {a : α} {b : ℤ} {nb ne : ℕ}
    (pb : IsNat b nb) (pe' : IsInt (a ^ nb) (Int.negOfNat ne)) :
    IsInt (a ^ b) (Int.negOfNat ne) := by
  rwa [pb.out, zpow_natCast]

theorem isInt_zpow_neg {α : Type*} [DivisionRing α] {a : α} {b : ℤ} {nb ne : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsInt (a ^ nb)⁻¹ (Int.negOfNat ne)) :
    IsInt (a ^ b) (Int.negOfNat ne) := by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

theorem isRat_zpow_pos {α : Type*} [DivisionRing α] {a : α} {b : ℤ} {nb : ℕ}
    {num : ℤ} {den : ℕ}
    (pb : IsNat b nb) (pe' : IsRat (a^nb) num den) :
    IsRat (a^b) num den := by
  rwa [pb.out, zpow_natCast]

theorem isRat_zpow_neg {α : Type*} [DivisionRing α] {a : α} {b : ℤ} {nb : ℕ}
    {num : ℤ} {den : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsRat ((a^nb)⁻¹) num den) :
    IsRat (a^b) num den := by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℤ`. -/
@[norm_num (_ : α) ^ (_ : ℤ)]
def evalZPow : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → ℤ → $α)) (a : Q($α))) (b : Q(ℤ)) ← whnfR e | failure
  let _c ← synthInstanceQ q(DivisionSemiring $α)
  let rb ← derive (α := q(ℤ)) b
  have h : $e =Q $a ^ $b := ⟨⟩
  h.check
  match rb with
  | .isBool .. | .isRat _ .. => failure
  | .isNat sβ nb pb =>
    match ← derive q($a ^ $nb) with
    | .isBool .. => failure
    | .isNat sα' ne' pe' =>
      assumeInstancesCommute
      return .isNat sα' ne' q(isNat_zpow_pos $pb $pe')
    | .isNegNat sα' ne' pe' =>
      let _c ← synthInstanceQ q(DivisionRing $α)
      assumeInstancesCommute
      return .isNegNat sα' ne' q(isInt_zpow_pos $pb $pe')
    | .isRat sα' qe' nume' dene' pe' =>
      assumeInstancesCommute
      return .isRat sα' qe' nume' dene' q(isRat_zpow_pos $pb $pe')
  | .isNegNat sβ nb pb =>
    match ← derive q(($a ^ $nb)⁻¹) with
    | .isBool .. => failure
    | .isNat sα' ne' pe' =>
      assumeInstancesCommute
      return .isNat sα' ne' q(isNat_zpow_neg $pb $pe')
    | .isNegNat sα' ne' pe' =>
      let _c ← synthInstanceQ q(DivisionRing $α)
      assumeInstancesCommute
      return .isNegNat sα' ne' q(isInt_zpow_neg $pb $pe')
    | .isRat sα' qe' nume' dene' pe' =>
      assumeInstancesCommute
      return .isRat sα' qe' nume' dene' q(isRat_zpow_neg $pb $pe')
