/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.GroupPower.Lemmas

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

-- partial def evalPow' {α : Q(Type u)} (ha' : Q(NatCast $α)) (ha : Q(HPow $α ℕ $α)) (a b : Q(ℕ)) :
--   (c : Q(ℕ)) × Q(HPow.hPow (@Nat.cast _ $ha' $a) $b = $c) :=
-- sorry

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
  ⟨fun h1 => by
    -- TODO: clean up this proof
    simp [two_mul, pow_add, mul_assoc, ← h1]
    have : ∀ a b, Nat.mod a b = a % b := fun x y => rfl
    simp [this, Nat.mul_mod]⟩

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
  if b.natLit! = 0 then -- a^0 = 1
    haveI : $b =Q 0 := ⟨⟩
    ⟨q(nat_lit 1), q(natPow_zero)⟩
  else if a.natLit! = 0 then -- 0^b = 0
    haveI : $a =Q 0 := ⟨⟩
    have b' : Q(ℕ) := mkRawNatLit (b.natLit! - 1)
    haveI : $b =Q Nat.succ $b' := ⟨⟩
    ⟨q(nat_lit 0), q(zero_natPow)⟩
  else if a.natLit! = 1 then -- 1^b = 1
    haveI : $a =Q 1 := ⟨⟩
    ⟨q(nat_lit 1), q(one_natPow)⟩
  else if b.natLit! = 1 then -- a^1 = a
    haveI : $b =Q 1 := ⟨⟩
    ⟨a, q(natPow_one)⟩
  else
    let ⟨c, p⟩ := go b.natLit!.log2 a (mkRawNatLit 1) a b
    ⟨c, q(($p).run)⟩
where
  /-- Invariants: `a ^ b₀ = c₀`, `depth > 0`, `b >>> depth = b₀`, `p := Nat.pow $a $b₀ = $c₀` -/
  go (depth : Nat) (a b₀ c₀ b : Q(ℕ)) : (c : Q(ℕ)) × Q(IsNatPowT (Nat.pow $a $b₀ = $c₀) $a $b $c) :=
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
      let ⟨c1, p1⟩ := go (depth - d) a b₀ c₀ hi
      let ⟨c2, p2⟩ := go d a hi c1 b
      ⟨c2, q(($p1).trans $p2)⟩

theorem intPow_ofNat (h1 : Nat.pow a b = c) :
    Int.pow (Int.ofNat a) b = Int.ofNat c := by simp [← h1]

theorem intPow_negOfNat_bit0 (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' = b) (hc : c' * c' = c) :
    Int.pow (Int.negOfNat a) b = Int.ofNat c := by
  rw [← hb, Int.negOfNat_eq, pow_eq, pow_mul, neg_pow_two, ← pow_mul, two_mul, pow_add, ← hc, ← h1]
  simp

theorem intPow_negOfNat_bit1 (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' + nat_lit 1 = b) (hc : c' * (c' * a) = c) :
    Int.pow (Int.negOfNat a) b = Int.negOfNat c := by
  rw [← hb, Int.negOfNat_eq, Int.negOfNat_eq, pow_eq, pow_succ, pow_mul, neg_pow_two, ← pow_mul,
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

theorem isNat_powMod : ∀ {f : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℕ} {a a' b b' m m' c : ℕ},
    f = HPow.hPow → g = HMod.hMod → IsNat a a' → IsNat b b' → IsNat m m' →
      Nat.mod (Nat.pow a' b') m' = c → IsNat (g (f a b) m) c
  | _, _, _, _, _, _, _, _, _, rfl, rfl, ⟨rfl⟩, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

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
@[norm_num (_ : α) ^ (_ : ℕ), Pow.pow _ (_ : ℕ)]
def evalPow : NormNumExt where eval {u α} e := do
  -- Explicitly catch the case handled by `evalPowMod` and fail here so that we don't time out
  -- here when `evalPowMod` would handle it just fine.
  if let .app (.app (f : Q(ℕ → ℕ → ℕ)) (.app (.app (g : Q(ℕ → ℕ → ℕ)) (_ : Q(ℕ))) (_ : Q(ℕ))))
    (_ : Q(ℕ)) ← whnfR e then throwError "will be handled later {f} {g}"

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

@[norm_num (_ : ℕ) ^ (_ : ℕ) % (_ : ℕ)]
def evalPowMod : NormNumExt where eval {u α} e := do
  let .app (.app (g : Q(ℕ → ℕ → ℕ)) (.app (.app (f : Q(ℕ → ℕ → ℕ)) (a : Q(ℕ))) (b : Q(ℕ))))
    (m : Q(ℕ)) ← whnfR e | failure
  let ⟨na, pa⟩ ← deriveNat a q(instAddMonoidWithOneNat)
  let ⟨nb, pb⟩ ← deriveNat b q(instAddMonoidWithOneNat)
  let ⟨nm, pm⟩ ← deriveNat m q(instAddMonoidWithOneNat)
  -- let ra ← derive (α := q(ℕ)) a
  -- let rm ← derive (α := q(ℕ)) m
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := ℕ))
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq g q(HMod.hMod (α := ℕ))
  haveI' : u =QL 0 := ⟨⟩
  haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q $a ^ $b % $m := ⟨⟩
  haveI' : $f =Q HPow.hPow := ⟨⟩
  haveI' : $g =Q HMod.hMod := ⟨⟩
  let rec
  core : Option (Result e) := do
    assumeInstancesCommute
    have ⟨c, r⟩ := evalNatPowMod na nb nm
    return .isNat q(instAddMonoidWithOneNat) c
      q(isNat_powMod (f := $f) (g := $g) (.refl $f) (.refl $g) $pa $pb $pm $r)
  core

set_option trace.Tactic.norm_num true

lemma yeah : 11 ^ 987654318 % 987654319 = 1 := by
  norm_num
