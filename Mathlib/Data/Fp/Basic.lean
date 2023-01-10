/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fp.basic
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Semiquot
import Mathbin.Data.Rat.Floor

/-!
# Implementation of floating-point numbers (experimental).
-/


def Int.shift2 (a b : ℕ) : ℤ → ℕ × ℕ
  | Int.ofNat e => (a.shiftl e, b)
  | -[e+1] => (a, b.shiftl e.succ)
#align int.shift2 Int.shift2

namespace Fp

inductive Rmode
  | NE
  deriving Inhabited
#align fp.rmode Fp.Rmode

-- round to nearest even
class FloatCfg where
  (prec emax : ℕ)
  prec_pos : 0 < prec
  prec_max : prec ≤ emax
#align fp.float_cfg Fp.FloatCfg

variable [C : FloatCfg]

include C

def prec :=
  C.prec
#align fp.prec Fp.prec

def emax :=
  C.emax
#align fp.emax Fp.emax

def emin : ℤ :=
  1 - C.emax
#align fp.emin Fp.emin

def ValidFinite (e : ℤ) (m : ℕ) : Prop :=
  emin ≤ e + prec - 1 ∧ e + prec - 1 ≤ emax ∧ e = max (e + m.size - prec) emin
#align fp.valid_finite Fp.ValidFinite

instance decValidFinite (e m) : Decidable (ValidFinite e m) := by
  unfold valid_finite <;> infer_instance
#align fp.dec_valid_finite Fp.decValidFinite

inductive Float
  | inf : Bool → float
  | nan : float
  | Finite : Bool → ∀ e m, ValidFinite e m → float
#align fp.float Fp.Float

def Float.isFinite : Float → Bool
  | float.finite s e m f => true
  | _ => false
#align fp.float.is_finite Fp.Float.isFinite

def toRat : ∀ f : Float, f.isFinite → ℚ
  | float.finite s e m f, _ =>
    let (n, d) := Int.shift2 m 1 e
    let r := mkRat n d
    if s then -r else r
#align fp.to_rat Fp.toRat

theorem Float.Zero.valid : ValidFinite emin 0 :=
  ⟨by
    rw [add_sub_assoc]
    apply le_add_of_nonneg_right
    apply sub_nonneg_of_le
    apply Int.ofNat_le_ofNat_of_le
    exact C.prec_pos,
    suffices prec ≤ 2 * emax by
      rw [← Int.ofNat_le] at this
      rw [← sub_nonneg] at *
      simp only [emin, emax] at *
      ring_nf
      assumption
    le_trans C.prec_max (Nat.le_mul_of_pos_left (by decide)),
    by rw [max_eq_right] <;> simp [sub_eq_add_neg]⟩
#align fp.float.zero.valid Fp.Float.Zero.valid

def Float.zero (s : Bool) : Float :=
  Float.finite s emin 0 Float.Zero.valid
#align fp.float.zero Fp.Float.zero

instance : Inhabited Float :=
  ⟨Float.zero true⟩

protected def Float.sign' : Float → Semiquot Bool
  | float.inf s => pure s
  | float.nan => ⊤
  | float.finite s e m f => pure s
#align fp.float.sign' Fp.Float.sign'

protected def Float.sign : Float → Bool
  | float.inf s => s
  | float.nan => false
  | float.finite s e m f => s
#align fp.float.sign Fp.Float.sign

protected def Float.isZero : Float → Bool
  | float.finite s e 0 f => true
  | _ => false
#align fp.float.is_zero Fp.Float.isZero

protected def Float.neg : Float → Float
  | float.inf s => Float.inf (not s)
  | float.nan => Float.nan
  | float.finite s e m f => Float.finite (not s) e m f
#align fp.float.neg Fp.Float.neg

/- warning: fp.div_nat_lt_two_pow -> Fp.divNatLtTwoPow is a dubious translation:
lean 3 declaration is
  forall [C : Fp.FloatCfg], Nat -> Nat -> Int -> Bool
but is expected to have type
  Nat -> Nat -> Int -> Bool
Case conversion may be inaccurate. Consider using '#align fp.div_nat_lt_two_pow Fp.divNatLtTwoPowₓ'. -/
def divNatLtTwoPow (n d : ℕ) : ℤ → Bool
  | Int.ofNat e => n < d.shiftl e
  | -[e+1] => n.shiftl e.succ < d
#align fp.div_nat_lt_two_pow Fp.divNatLtTwoPow

-- TODO(Mario): Prove these and drop 'meta'
unsafe def of_pos_rat_dn (n : ℕ+) (d : ℕ+) : float × Bool :=
  by
  let e₁ : ℤ := n.1.size - d.1.size - prec
  cases' h₁ : Int.shift2 d.1 n.1 (e₁ + prec) with d₁ n₁
  let e₂ := if n₁ < d₁ then e₁ - 1 else e₁
  let e₃ := max e₂ emin
  cases' h₂ : Int.shift2 d.1 n.1 (e₃ + prec) with d₂ n₂
  let r := mkRat n₂ d₂
  let m := r.floor
  refine' (float.finite ff e₃ (Int.toNat m) _, r.denom = 1)
  · exact undefined
#align fp.of_pos_rat_dn fp.of_pos_rat_dn

unsafe def next_up_pos (e m) (v : ValidFinite e m) : Float :=
  let m' := m.succ
  if ss : m'.size = m.size then
    Float.finite false e m' (by unfold valid_finite at * <;> rw [ss] <;> exact v)
  else if h : e = emax then Float.inf false else Float.finite false e.succ (Nat.div2 m') undefined
#align fp.next_up_pos fp.next_up_pos

unsafe def next_dn_pos (e m) (v : ValidFinite e m) : Float :=
  match m with
  | 0 => next_up_pos _ _ Float.Zero.valid
  | Nat.succ m' =>
    if ss : m'.size = m.size then
      Float.finite false e m' (by unfold valid_finite at * <;> rw [ss] <;> exact v)
    else
      if h : e = emin then Float.finite false emin m' undefined
      else Float.finite false e.pred (bit1 m') undefined
#align fp.next_dn_pos fp.next_dn_pos

unsafe def next_up : Float → Float
  | float.finite ff e m f => next_up_pos e m f
  | float.finite tt e m f => float.neg <| next_dn_pos e m f
  | f => f
#align fp.next_up fp.next_up

unsafe def next_dn : Float → Float
  | float.finite ff e m f => next_dn_pos e m f
  | float.finite tt e m f => float.neg <| next_up_pos e m f
  | f => f
#align fp.next_dn fp.next_dn

unsafe def of_rat_up : ℚ → Float
  | ⟨0, _, _, _⟩ => Float.zero false
  | ⟨Nat.succ n, d, h, _⟩ =>
    let (f, exact) := of_pos_rat_dn n.succPnat ⟨d, h⟩
    if exact then f else next_up f
  | ⟨-[n+1], d, h, _⟩ => Float.neg (of_pos_rat_dn n.succPnat ⟨d, h⟩).1
#align fp.of_rat_up fp.of_rat_up

unsafe def of_rat_dn (r : ℚ) : Float :=
  float.neg <| of_rat_up (-r)
#align fp.of_rat_dn fp.of_rat_dn

unsafe def of_rat : Rmode → ℚ → Float
  | rmode.NE, r =>
    let low := of_rat_dn r
    let high := of_rat_up r
    if hf : high.isFinite then
      if r = toRat _ hf then high
      else
        if lf : low.isFinite then
          if r - toRat _ lf > toRat _ hf - r then high
          else
            if r - toRat _ lf < toRat _ hf - r then low
            else
              match low, lf with
              | float.finite s e m f, _ => if 2 ∣ m then low else high
        else Float.inf true
    else Float.inf false
#align fp.of_rat fp.of_rat

namespace Float

instance : Neg Float :=
  ⟨Float.neg⟩

unsafe def add (mode : Rmode) : Float → Float → Float
  | nan, _ => nan
  | _, nan => nan
  | inf tt, inf ff => nan
  | inf ff, inf tt => nan
  | inf s₁, _ => inf s₁
  | _, inf s₂ => inf s₂
  | Finite s₁ e₁ m₁ v₁, Finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    of_rat mode (toRat f₁ rfl + toRat f₂ rfl)
#align fp.float.add fp.float.add

unsafe instance : Add Float :=
  ⟨float.add Rmode.NE⟩

unsafe def sub (mode : Rmode) (f1 f2 : Float) : Float :=
  add mode f1 (-f2)
#align fp.float.sub fp.float.sub

unsafe instance : Sub Float :=
  ⟨float.sub Rmode.NE⟩

unsafe def mul (mode : Rmode) : Float → Float → Float
  | nan, _ => nan
  | _, nan => nan
  | inf s₁, f₂ => if f₂.isZero then nan else inf (xor s₁ f₂.sign)
  | f₁, inf s₂ => if f₁.isZero then nan else inf (xor f₁.sign s₂)
  | Finite s₁ e₁ m₁ v₁, Finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    of_rat mode (toRat f₁ rfl * toRat f₂ rfl)
#align fp.float.mul fp.float.mul

unsafe def div (mode : Rmode) : Float → Float → Float
  | nan, _ => nan
  | _, nan => nan
  | inf s₁, inf s₂ => nan
  | inf s₁, f₂ => inf (xor s₁ f₂.sign)
  | f₁, inf s₂ => zero (xor f₁.sign s₂)
  | Finite s₁ e₁ m₁ v₁, Finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    if f₂.isZero then inf (xor s₁ s₂) else of_rat mode (toRat f₁ rfl / toRat f₂ rfl)
#align fp.float.div fp.float.div

end Float

end Fp

