/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fp.basic
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Semiquot
import Mathlib.Data.Rat.Floor

/-!
# Implementation of floating-point numbers (experimental).
-/


def Int.shift2 (a b : ℕ) : ℤ → ℕ × ℕ
  | Int.ofNat e => (a.shiftl e, b)
  | Int.negSucc e => (a, b.shiftl e.succ)
#align int.shift2 Int.shift2

namespace FP

inductive Rmode
  | NE
  deriving Inhabited
#align fp.rmode FP.Rmode

-- round to nearest even
class FloatCfg where
  (prec emax : ℕ)
  prec_pos : 0 < prec
  prec_max : prec ≤ emax
#align fp.float_cfg FP.FloatCfg

variable [C : FloatCfg]

-- Porting note: no longer needed
--include C

def prec :=
  C.prec
#align fp.prec FP.prec

def emax :=
  C.emax
#align fp.emax FP.emax

def emin : ℤ :=
  1 - C.emax
#align fp.emin FP.emin

def ValidFinite (e : ℤ) (m : ℕ) : Prop :=
  emin ≤ e + prec - 1 ∧ e + prec - 1 ≤ emax ∧ e = max (e + m.size - prec) emin
#align fp.valid_finite FP.ValidFinite

instance decValidFinite (e m) : Decidable (ValidFinite e m) := by
  (unfold ValidFinite; infer_instance)
#align fp.dec_valid_finite FP.decValidFinite

inductive Float
  | Inf : Bool → Float
  | Nan : Float
  | Finite : Bool → ∀ e m, ValidFinite e m → Float
#align fp.float FP.Float

def Float.isFinite : Float → Bool
  | Float.Finite _ _ _ _ => true
  | _ => false
#align fp.float.is_finite FP.Float.isFinite

def toRat : ∀ f : Float, f.isFinite → ℚ
  | Float.Finite s e m _, _ =>
    let (n, d) := Int.shift2 m 1 e
    let r := mkRat n d
    if s then -r else r
#align fp.to_rat FP.toRat

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
      rw [mul_comm]
      assumption
    le_trans C.prec_max (Nat.le_mul_of_pos_left (by decide)),
    by (rw [max_eq_right]; simp [sub_eq_add_neg])⟩
#align fp.float.zero.valid FP.Float.Zero.valid

def Float.zero (s : Bool) : Float :=
  Float.Finite s emin 0 Float.Zero.valid
#align fp.float.zero FP.Float.zero

instance : Inhabited Float :=
  ⟨Float.zero true⟩

protected def Float.sign' : Float → Semiquot Bool
  | Float.Inf s => pure s
  | Float.Nan => ⊤
  | Float.Finite s _ _ _ => pure s
#align fp.float.sign' FP.Float.sign'

protected def Float.sign : Float → Bool
  | Float.Inf s => s
  | Float.Nan => false
  | Float.Finite s _ _ _ => s
#align fp.float.sign FP.Float.sign

protected def Float.isZero : Float → Bool
  | Float.Finite _ _ 0 _ => true
  | _ => false
#align fp.float.is_zero FP.Float.isZero

protected def Float.neg : Float → Float
  | Float.Inf s => Float.Inf (not s)
  | Float.Nan => Float.Nan
  | Float.Finite s e m f => Float.Finite (not s) e m f
#align fp.float.neg FP.Float.neg

/- warning: fp.div_nat_lt_two_pow -> FP.divNatLtTwoPow is a dubious translation:
lean 3 declaration is
  forall [C : FP.FloatCfg], Nat -> Nat -> Int -> Bool
but is expected to have type
  Nat -> Nat -> Int -> Bool
Case conversion may be inaccurate. Consider using '#align fp.div_nat_lt_two_pow FP.divNatLtTwoPowₓ'. -/
def divNatLtTwoPowₓ (n d : ℕ) : ℤ → Bool
  | Int.ofNat e => n < d.shiftl e
  | Int.negSucc e => n.shiftl e.succ < d
#align fp.div_nat_lt_two_pow FP.divNatLtTwoPowₓ


-- TODO(Mario): Prove these and drop 'meta'
unsafe def of_pos_rat_dn (n : ℕ+) (d : ℕ+) : Float × Bool := by
  let e₁ : ℤ := n.1.size - d.1.size - prec
  cases' h₁ : Int.shift2 d.1 n.1 (e₁ + prec) with d₁ n₁
  let e₂ := if n₁ < d₁ then e₁ - 1 else e₁
  let e₃ := max e₂ emin
  cases' h₂ : Int.shift2 d.1 n.1 (e₃ + prec) with d₂ n₂
  let r := mkRat n₂ d₂
  let m := r.floor
  refine' (Float.Finite Bool.false e₃ (Int.toNat m) _, r.den = 1)
  -- Porting note: TODO understand how to hande `undefined`, also for the next def
  · exact undefined
#align fp.of_pos_rat_dn FP.of_pos_rat_dn

unsafe def next_up_pos (e m) (v : ValidFinite e m) : Float :=
  let m' := m.succ
  if ss : m'.size = m.size then
    Float.Finite false e m' (by unfold ValidFinite at * <;> rw [ss] <;> exact v)
  else if h : e = emax then Float.Inf false else Float.Finite false e.succ (Nat.div2 m') undefined
#align fp.next_up_pos FP.next_up_pos

unsafe def next_dn_pos (e m) (v : ValidFinite e m) : Float :=
  match m with
  | 0 => next_up_pos _ _ Float.Zero.valid
  | Nat.succ m' =>
    if ss : m'.size = m.size then
      Float.Finite false e m' (by unfold ValidFinite at * <;> rw [ss] <;> exact v)
    else
      if h : e = emin then Float.Finite false emin m' undefined
      else Float.Finite false e.pred (bit1 m') undefined
#align fp.next_dn_pos FP.next_dn_pos

unsafe def next_up : Float → Float
  | Float.Finite Bool.false e m f => next_up_pos e m f
  | Float.Finite Bool.true e m f => Float.neg <| next_dn_pos e m f
  | f => f
#align fp.next_up FP.next_up

unsafe def next_dn : Float → Float
  | Float.Finite Bool.false e m f => next_dn_pos e m f
  | Float.Finite Bool.true e m f => Float.neg <| next_up_pos e m f
  | f => f
#align fp.next_dn FP.next_dn

unsafe def of_rat_up : ℚ → Float
  | ⟨0, _, _, _⟩ => Float.zero false
  | ⟨Nat.succ n, d, h, _⟩ =>
    let (f, exact) := of_pos_rat_dn n.succPNat ⟨d, Nat.pos_of_ne_zero h⟩
    if exact then f else next_up f
  | ⟨Int.negSucc n, d, h, _⟩ => Float.neg (of_pos_rat_dn n.succPNat ⟨d, Nat.pos_of_ne_zero h⟩).1
#align fp.of_rat_up FP.of_rat_up

unsafe def of_rat_dn (r : ℚ) : Float :=
  Float.neg <| of_rat_up (-r)
#align fp.of_rat_dn FP.of_rat_dn

unsafe def of_rat : Rmode → ℚ → Float
  | Rmode.NE, r =>
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
              | Float.Finite _ _ m _, _ => if 2 ∣ m then low else high
        else Float.Inf true
    else Float.Inf false
#align fp.of_rat FP.of_rat

namespace Float

instance : Neg Float :=
  ⟨Float.neg⟩

unsafe def add (mode : Rmode) : Float → Float → Float
  | Nan, _ => Nan
  | _, Nan => Nan
  | Inf Bool.true, Inf Bool.false=> Nan
  | Inf Bool.false, Inf Bool.true => Nan
  | Inf s₁, _ => Inf s₁
  | _, Inf s₂ => Inf s₂
  | Finite s₁ e₁ m₁ v₁, Finite s₂ e₂ m₂ v₂ =>
    let f₁ := Finite s₁ e₁ m₁ v₁
    let f₂ := Finite s₂ e₂ m₂ v₂
    of_rat mode (toRat f₁ rfl + toRat f₂ rfl)
#align fp.float.add FP.Float.add

unsafe instance : Add Float :=
  ⟨Float.add Rmode.NE⟩

unsafe def sub (mode : Rmode) (f1 f2 : Float) : Float :=
  add mode f1 (-f2)
#align fp.float.sub FP.Float.sub

unsafe instance : Sub Float :=
  ⟨Float.sub Rmode.NE⟩

unsafe def mul (mode : Rmode) : Float → Float → Float
  | Nan, _ => Nan
  | _, Nan => Nan
  | Inf s₁, f₂ => if f₂.isZero then Nan else Inf (xor s₁ f₂.sign)
  | f₁, Inf s₂ => if f₁.isZero then Nan else Inf (xor f₁.sign s₂)
  | Finite s₁ e₁ m₁ v₁, Finite s₂ e₂ m₂ v₂ =>
    let f₁ := Finite s₁ e₁ m₁ v₁
    let f₂ := Finite s₂ e₂ m₂ v₂
    of_rat mode (toRat f₁ rfl * toRat f₂ rfl)
#align fp.float.mul FP.Float.mul

unsafe def div (mode : Rmode) : Float → Float → Float
  | Nan, _ => Nan
  | _, Nan => Nan
  | Inf _, Inf _ => Nan
  | Inf s₁, f₂ => Inf (xor s₁ f₂.sign)
  | f₁, Inf s₂ => zero (xor f₁.sign s₂)
  | Finite s₁ e₁ m₁ v₁, Finite s₂ e₂ m₂ v₂ =>
    let f₁ := Finite s₁ e₁ m₁ v₁
    let f₂ := Finite s₂ e₂ m₂ v₂
    if f₂.isZero then Inf (xor s₁ s₂) else of_rat mode (toRat f₁ rfl / toRat f₂ rfl)
#align fp.float.div FP.Float.div

end Float

end FP
