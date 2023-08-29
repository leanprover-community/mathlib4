/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Semiquot
import Mathlib.Data.Rat.Floor

#align_import data.fp.basic from "leanprover-community/mathlib"@"7b78d1776212a91ecc94cf601f83bdcc46b04213"

/-!
# Implementation of floating-point numbers (experimental).
-/

-- Porting note: TODO add docs and remove `@[nolint docBlame]`

@[nolint docBlame]
def Int.shift2 (a b : ℕ) : ℤ → ℕ × ℕ
  | Int.ofNat e => (a <<< e, b)
  | Int.negSucc e => (a, b <<< e.succ)
#align int.shift2 Int.shift2

namespace FP

@[nolint docBlame]
inductive RMode
  | NE -- round to nearest even
  deriving Inhabited
#align fp.rmode FP.RMode

@[nolint docBlame]
class FloatCfg where
  (prec emax : ℕ)
  precPos : 0 < prec
  precMax : prec ≤ emax
attribute [nolint docBlame] FloatCfg.prec FloatCfg.emax FloatCfg.precPos FloatCfg.precMax
#align fp.float_cfg FP.FloatCfg

variable [C : FloatCfg]

@[nolint docBlame]
def prec :=
  C.prec
#align fp.prec FP.prec

@[nolint docBlame]
def emax :=
  C.emax
#align fp.emax FP.emax

@[nolint docBlame]
def emin : ℤ :=
  1 - C.emax
#align fp.emin FP.emin

@[nolint docBlame]
def ValidFinite (e : ℤ) (m : ℕ) : Prop :=
  emin ≤ e + prec - 1 ∧ e + prec - 1 ≤ emax ∧ e = max (e + m.size - prec) emin
#align fp.valid_finite FP.ValidFinite

instance decValidFinite (e m) : Decidable (ValidFinite e m) := by
  (unfold ValidFinite; infer_instance)
   -- ⊢ Decidable (emin ≤ e + ↑prec - 1 ∧ e + ↑prec - 1 ≤ ↑emax ∧ e = max (e + ↑(Nat …
                       -- 🎉 no goals
#align fp.dec_valid_finite FP.decValidFinite

@[nolint docBlame]
inductive Float
  | inf : Bool → Float
  | nan : Float
  | finite : Bool → ∀ e m, ValidFinite e m → Float
#align fp.float FP.Float

@[nolint docBlame]
def Float.isFinite : Float → Bool
  | Float.finite _ _ _ _ => true
  | _ => false
#align fp.float.is_finite FP.Float.isFinite

@[nolint docBlame]
def toRat : ∀ f : Float, f.isFinite → ℚ
  | Float.finite s e m _, _ =>
    let (n, d) := Int.shift2 m 1 e
    let r := mkRat n d
    if s then -r else r
#align fp.to_rat FP.toRat

theorem Float.Zero.valid : ValidFinite emin 0 :=
  ⟨by
    rw [add_sub_assoc]
    -- ⊢ emin ≤ emin + (↑prec - 1)
    apply le_add_of_nonneg_right
    -- ⊢ 0 ≤ ↑prec - 1
    apply sub_nonneg_of_le
    -- ⊢ 1 ≤ ↑prec
    apply Int.ofNat_le_ofNat_of_le
    -- ⊢ 1 ≤ prec
    exact C.precPos,
    -- 🎉 no goals
    suffices prec ≤ 2 * emax by
      rw [← Int.ofNat_le] at this
      -- ⊢ emin + ↑prec - 1 ≤ ↑emax
      rw [← sub_nonneg] at *
      -- ⊢ 0 ≤ ↑emax - (emin + ↑prec - 1)
      simp only [emin, emax] at *
      -- ⊢ 0 ≤ ↑FloatCfg.emax - (1 - ↑FloatCfg.emax + ↑prec - 1)
      ring_nf
                                                   -- 🎉 no goals
      -- ⊢ 0 ≤ ↑FloatCfg.emax * 2 - ↑prec
      rw [mul_comm]
      -- ⊢ 0 ≤ 2 * ↑FloatCfg.emax - ↑prec
      assumption
      -- 🎉 no goals
    le_trans C.precMax (Nat.le_mul_of_pos_left (by decide)),
    by (rw [max_eq_right]; simp [sub_eq_add_neg])⟩
        -- ⊢ emin + ↑(Nat.size 0) - ↑prec ≤ emin
                           -- 🎉 no goals
#align fp.float.zero.valid FP.Float.Zero.valid

@[nolint docBlame]
def Float.zero (s : Bool) : Float :=
  Float.finite s emin 0 Float.Zero.valid
#align fp.float.zero FP.Float.zero

instance : Inhabited Float :=
  ⟨Float.zero true⟩

@[nolint docBlame]
protected def Float.sign' : Float → Semiquot Bool
  | Float.inf s => pure s
  | Float.nan => ⊤
  | Float.finite s _ _ _ => pure s
#align fp.float.sign' FP.Float.sign'

@[nolint docBlame]
protected def Float.sign : Float → Bool
  | Float.inf s => s
  | Float.nan => false
  | Float.finite s _ _ _ => s
#align fp.float.sign FP.Float.sign

@[nolint docBlame]
protected def Float.isZero : Float → Bool
  | Float.finite _ _ 0 _ => true
  | _ => false
#align fp.float.is_zero FP.Float.isZero

@[nolint docBlame]
protected def Float.neg : Float → Float
  | Float.inf s => Float.inf (not s)
  | Float.nan => Float.nan
  | Float.finite s e m f => Float.finite (not s) e m f
#align fp.float.neg FP.Float.neg

@[nolint docBlame]
def divNatLtTwoPow (n d : ℕ) : ℤ → Bool
  | Int.ofNat e => n < d <<< e
  | Int.negSucc e => n <<< e.succ < d
#align fp.div_nat_lt_two_pow FP.divNatLtTwoPowₓ -- Porting note: TC argument `[C : FP.FloatCfg]` no longer present


-- TODO(Mario): Prove these and drop 'unsafe'
@[nolint docBlame]
unsafe def ofPosRatDn (n : ℕ+) (d : ℕ+) : Float × Bool := by
  let e₁ : ℤ := n.1.size - d.1.size - prec
  -- ⊢ Float × Bool
  cases' h₁ : Int.shift2 d.1 n.1 (e₁ + prec) with d₁ n₁
  -- ⊢ Float × Bool
  let e₂ := if n₁ < d₁ then e₁ - 1 else e₁
  -- ⊢ Float × Bool
  let e₃ := max e₂ emin
  -- ⊢ Float × Bool
  cases' h₂ : Int.shift2 d.1 n.1 (e₃ + prec) with d₂ n₂
  -- ⊢ Float × Bool
  let r := mkRat n₂ d₂
  -- ⊢ Float × Bool
  let m := r.floor
  -- ⊢ Float × Bool
  refine' (Float.finite Bool.false e₃ (Int.toNat m) _, r.den = 1)
  -- ⊢ ValidFinite e₃ (Int.toNat m)
  · exact lcProof
    -- 🎉 no goals
#align fp.of_pos_rat_dn FP.ofPosRatDn

-- Porting note: remove this line when you dropped 'lcProof'
set_option linter.unusedVariables false in
@[nolint docBlame]
unsafe def nextUpPos (e m) (v : ValidFinite e m) : Float :=
  let m' := m.succ
  if ss : m'.size = m.size then
    Float.finite false e m' (by unfold ValidFinite at *; rw [ss]; exact v)
                                -- ⊢ emin ≤ e + ↑prec - 1 ∧ e + ↑prec - 1 ≤ ↑emax ∧ e = max (e + ↑(Nat.size m') - …
                                                         -- ⊢ emin ≤ e + ↑prec - 1 ∧ e + ↑prec - 1 ≤ ↑emax ∧ e = max (e + ↑(Nat.size m) -  …
                                                                  -- 🎉 no goals
  else if h : e = emax then Float.inf false else Float.finite false e.succ (Nat.div2 m') lcProof
#align fp.next_up_pos FP.nextUpPos

set_option linter.deprecated false in
-- Porting note: remove this line when you dropped 'lcProof'
set_option linter.unusedVariables false in
@[nolint docBlame]
unsafe def nextDnPos (e m) (v : ValidFinite e m) : Float :=
  match m with
  | 0 => nextUpPos _ _ Float.Zero.valid
  | Nat.succ m' =>
    -- Porting note: was `m'.size = m.size`
    if ss : m'.size = m'.succ.size then
      Float.finite false e m' (by unfold ValidFinite at *; rw [ss]; exact v)
                                  -- ⊢ emin ≤ e + ↑prec - 1 ∧ e + ↑prec - 1 ≤ ↑emax ∧ e = max (e + ↑(Nat.size m') - …
                                                           -- ⊢ emin ≤ e + ↑prec - 1 ∧ e + ↑prec - 1 ≤ ↑emax ∧ e = max (e + ↑(Nat.size (Nat. …
                                                                    -- 🎉 no goals
    else
      if h : e = emin then Float.finite false emin m' lcProof
      else Float.finite false e.pred (bit1 m') lcProof
#align fp.next_dn_pos FP.nextDnPos

@[nolint docBlame]
unsafe def nextUp : Float → Float
  | Float.finite Bool.false e m f => nextUpPos e m f
  | Float.finite Bool.true e m f => Float.neg <| nextDnPos e m f
  | f => f
#align fp.next_up FP.nextUp

@[nolint docBlame]
unsafe def nextDn : Float → Float
  | Float.finite Bool.false e m f => nextDnPos e m f
  | Float.finite Bool.true e m f => Float.neg <| nextUpPos e m f
  | f => f
#align fp.next_dn FP.nextDn

@[nolint docBlame]
unsafe def ofRatUp : ℚ → Float
  | ⟨0, _, _, _⟩ => Float.zero false
  | ⟨Nat.succ n, d, h, _⟩ =>
    let (f, exact) := ofPosRatDn n.succPNat ⟨d, Nat.pos_of_ne_zero h⟩
    if exact then f else nextUp f
  | ⟨Int.negSucc n, d, h, _⟩ => Float.neg (ofPosRatDn n.succPNat ⟨d, Nat.pos_of_ne_zero h⟩).1
#align fp.of_rat_up FP.ofRatUp

@[nolint docBlame]
unsafe def ofRatDn (r : ℚ) : Float :=
  Float.neg <| ofRatUp (-r)
#align fp.of_rat_dn FP.ofRatDn

@[nolint docBlame]
unsafe def ofRat : RMode → ℚ → Float
  | RMode.NE, r =>
    let low := ofRatDn r
    let high := ofRatUp r
    if hf : high.isFinite then
      if r = toRat _ hf then high
      else
        if lf : low.isFinite then
          if r - toRat _ lf > toRat _ hf - r then high
          else
            if r - toRat _ lf < toRat _ hf - r then low
            else
              match low, lf with
              | Float.finite _ _ m _, _ => if 2 ∣ m then low else high
        else Float.inf true
    else Float.inf false
#align fp.of_rat FP.ofRat

namespace Float

instance : Neg Float :=
  ⟨Float.neg⟩

@[nolint docBlame]
unsafe def add (mode : RMode) : Float → Float → Float
  | nan, _ => nan
  | _, nan => nan
  | inf Bool.true, inf Bool.false=> nan
  | inf Bool.false, inf Bool.true => nan
  | inf s₁, _ => inf s₁
  | _, inf s₂ => inf s₂
  | finite s₁ e₁ m₁ v₁, finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    ofRat mode (toRat f₁ rfl + toRat f₂ rfl)
#align fp.float.add FP.Float.add

unsafe instance : Add Float :=
  ⟨Float.add RMode.NE⟩

@[nolint docBlame]
unsafe def sub (mode : RMode) (f1 f2 : Float) : Float :=
  add mode f1 (-f2)
#align fp.float.sub FP.Float.sub

unsafe instance : Sub Float :=
  ⟨Float.sub RMode.NE⟩

@[nolint docBlame]
unsafe def mul (mode : RMode) : Float → Float → Float
  | nan, _ => nan
  | _, nan => nan
  | inf s₁, f₂ => if f₂.isZero then nan else inf (xor s₁ f₂.sign)
  | f₁, inf s₂ => if f₁.isZero then nan else inf (xor f₁.sign s₂)
  | finite s₁ e₁ m₁ v₁, finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    ofRat mode (toRat f₁ rfl * toRat f₂ rfl)
#align fp.float.mul FP.Float.mul

@[nolint docBlame]
unsafe def div (mode : RMode) : Float → Float → Float
  | nan, _ => nan
  | _, nan => nan
  | inf _, inf _ => nan
  | inf s₁, f₂ => inf (xor s₁ f₂.sign)
  | f₁, inf s₂ => zero (xor f₁.sign s₂)
  | finite s₁ e₁ m₁ v₁, finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    if f₂.isZero then inf (xor s₁ s₂) else ofRat mode (toRat f₁ rfl / toRat f₂ rfl)
#align fp.float.div FP.Float.div

end Float

end FP
