/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Prime

/-!
# Euclidean algorithm for ℕ

This file sets up a version of the Euclidean algorithm that only works with natural numbers.
Given `0 < a, b`, it computes the unique `(w, x, y, z, d)` such that the following identities hold:
* `a = (w + x) d`
* `b = (y + z) d`
* `w * z = x * y + 1`
`d` is then the gcd of `a` and `b`, and `a' := a / d = w + x` and `b' := b / d = y + z` are coprime.

This story is closely related to the structure of SL₂(ℕ) (as a free monoid on two generators) and
the theory of continued fractions.

## Main declarations

* `XgcdType`: Helper type in defining the gcd. Encapsulates `(wp, x, y, zp, ap, bp)`. where `wp`
  `zp`, `ap`, `bp` are the variables getting changed through the algorithm.
* `IsSpecial`: States `wp * zp = x * y + 1`
* `IsReduced`: States `ap = a ∧ bp = b`

## Notes

See `Nat.Xgcd` for a very similar algorithm allowing values in `ℤ`.
-/


open Nat

namespace PNat

/-- A term of `XgcdType` is a system of six naturals.  They should
be thought of as representing the matrix
[[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]
together with the vector [a, b] = [ap + 1, bp + 1].
-/
structure XgcdType where
  /-- `wp` is a variable which changes through the algorithm. -/
  wp : ℕ
  /-- `x` satisfies `a / d = w + x` at the final step. -/
  x : ℕ
  /-- `y` satisfies `b / d = z + y` at the final step. -/
  y : ℕ
  /-- `zp` is a variable which changes through the algorithm. -/
  zp : ℕ
  /-- `ap` is a variable which changes through the algorithm. -/
  ap : ℕ
  /-- `bp` is a variable which changes through the algorithm. -/
  bp : ℕ
  deriving Inhabited

namespace XgcdType

variable (u : XgcdType)

instance : SizeOf XgcdType :=
  ⟨fun u => u.bp⟩

/-- The `Repr` instance converts terms to strings in a way that
reflects the matrix/vector interpretation as above. -/
instance : Repr XgcdType where
  reprPrec
  | g, _ => s!"[[[{repr (g.wp + 1)}, {repr g.x}], \
                 [{repr g.y}, {repr (g.zp + 1)}]], \
                [{repr (g.ap + 1)}, {repr (g.bp + 1)}]]"

/-- Another `mk` using ℕ and ℕ+ -/
def mk' (w : ℕ+) (x : ℕ) (y : ℕ) (z : ℕ+) (a : ℕ+) (b : ℕ+) : XgcdType :=
  mk w.val.pred x y z.val.pred a.val.pred b.val.pred

/-- `w = wp + 1` -/
def w : ℕ+ :=
  succPNat u.wp

/-- `z = zp + 1` -/
def z : ℕ+ :=
  succPNat u.zp

/-- `a = ap + 1` -/
def a : ℕ+ :=
  succPNat u.ap

/-- `b = bp + 1` -/
def b : ℕ+ :=
  succPNat u.bp

/-- `r = a % b`: remainder -/
def r : ℕ :=
  (u.ap + 1) % (u.bp + 1)

/-- `q = ap / bp`: quotient -/
def q : ℕ :=
  (u.ap + 1) / (u.bp + 1)

/-- `qp = q - 1` -/
def qp : ℕ :=
  u.q - 1

/-- The map `v` gives the product of the matrix
[[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]
and the vector [a, b] = [ap + 1, bp + 1].  The map
`vp` gives [sp, tp] such that v = [sp + 1, tp + 1].
-/
def vp : ℕ × ℕ :=
  ⟨u.wp + u.x + u.ap + u.wp * u.ap + u.x * u.bp, u.y + u.zp + u.bp + u.y * u.ap + u.zp * u.bp⟩

/-- `v = [sp + 1, tp + 1]`, check `vp` -/
def v : ℕ × ℕ :=
  ⟨u.w * u.a + u.x * u.b, u.y * u.a + u.z * u.b⟩

/-- `succ₂ [t.1, t.2] = [t.1.succ, t.2.succ]` -/
def succ₂ (t : ℕ × ℕ) : ℕ × ℕ :=
  ⟨t.1.succ, t.2.succ⟩

theorem v_eq_succ_vp : u.v = succ₂ u.vp := by
  ext <;> dsimp [v, vp, w, z, a, b, succ₂] <;> ring_nf

/-- `IsSpecial` holds if the matrix has determinant one. -/
def IsSpecial : Prop :=
  u.wp + u.zp + u.wp * u.zp = u.x * u.y

/-- `IsSpecial'` is an alternative of `IsSpecial`. -/
def IsSpecial' : Prop :=
  u.w * u.z = succPNat (u.x * u.y)

theorem isSpecial_iff : u.IsSpecial ↔ u.IsSpecial' := by
  dsimp [IsSpecial, IsSpecial']
  let ⟨wp, x, y, zp, ap, bp⟩ := u
  constructor <;> intro h <;> simp only [w, succPNat, succ_eq_add_one, z] at * <;>
    simp only [← coe_inj, mul_coe, mk_coe] at *
  · simp_all [← h]; ring
  · simp only [Nat.mul_add, Nat.add_mul, one_mul, mul_one, ← Nat.add_assoc,
      Nat.add_right_cancel_iff] at h
    rw [← h]; ring

/-- `IsReduced` holds if the two entries in the vector are the
same.  The reduction algorithm will produce a system with this
property, whose product vector is the same as for the original
system. -/
def IsReduced : Prop :=
  u.ap = u.bp

/-- `IsReduced'` is an alternative of `IsReduced`. -/
def IsReduced' : Prop :=
  u.a = u.b

theorem isReduced_iff : u.IsReduced ↔ u.IsReduced' :=
  succPNat_inj.symm

/-- `flip` flips the placement of variables during the algorithm. -/
def flip : XgcdType where
  wp := u.zp
  x := u.y
  y := u.x
  zp := u.wp
  ap := u.bp
  bp := u.ap

@[simp]
theorem flip_w : (flip u).w = u.z :=
  rfl

@[simp]
theorem flip_x : (flip u).x = u.y :=
  rfl

@[simp]
theorem flip_y : (flip u).y = u.x :=
  rfl

@[simp]
theorem flip_z : (flip u).z = u.w :=
  rfl

@[simp]
theorem flip_a : (flip u).a = u.b :=
  rfl

@[simp]
theorem flip_b : (flip u).b = u.a :=
  rfl

theorem flip_isReduced : (flip u).IsReduced ↔ u.IsReduced := by
  dsimp [IsReduced, flip]
  constructor <;> intro h <;> exact h.symm

theorem flip_isSpecial : (flip u).IsSpecial ↔ u.IsSpecial := by
  dsimp [IsSpecial, flip]
  rw [mul_comm u.x, mul_comm u.zp, add_comm u.zp]

theorem flip_v : (flip u).v = u.v.swap := by
  dsimp [v]
  ext
  · simp only
    ring
  · simp only
    ring

/-- Properties of division with remainder for a / b. -/
theorem rq_eq : u.r + (u.bp + 1) * u.q = u.ap + 1 :=
  Nat.mod_add_div (u.ap + 1) (u.bp + 1)

theorem qp_eq (hr : u.r = 0) : u.q = u.qp + 1 := by
  by_cases hq : u.q = 0
  · let h := u.rq_eq
    rw [hr, hq, mul_zero, add_zero] at h
    cases h
  · exact (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hq)).symm

/-- The following function provides the starting point for
our algorithm.  We will apply an iterative reduction process
to it, which will produce a system satisfying IsReduced.
The gcd can be read off from this final system.
-/
def start (a b : ℕ+) : XgcdType :=
  ⟨0, 0, 0, 0, a - 1, b - 1⟩

theorem start_isSpecial (a b : ℕ+) : (start a b).IsSpecial := by
  dsimp [start, IsSpecial]

theorem start_v (a b : ℕ+) : (start a b).v = ⟨a, b⟩ := by
  dsimp [start, v, XgcdType.a, XgcdType.b, w, z]
  rw [one_mul, one_mul, zero_mul, zero_mul]
  have := a.pos
  have := b.pos
  congr <;> omega

/-- `finish` happens when the reducing process ends. -/
def finish : XgcdType :=
  XgcdType.mk u.wp ((u.wp + 1) * u.qp + u.x) u.y (u.y * u.qp + u.zp) u.bp u.bp

theorem finish_isReduced : u.finish.IsReduced := by
  dsimp [IsReduced]
  rfl

theorem finish_isSpecial (hs : u.IsSpecial) : u.finish.IsSpecial := by
  dsimp [IsSpecial, finish] at hs ⊢
  rw [add_mul _ _ u.y, add_comm _ (u.x * u.y), ← hs]
  ring

theorem finish_v (hr : u.r = 0) : u.finish.v = u.v := by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  rw [hr, zero_add] at ha
  ext
  · change (u.wp + 1) * u.b + ((u.wp + 1) * u.qp + u.x) * u.b = u.w * u.a + u.x * u.b
    have : u.wp + 1 = u.w := rfl
    rw [this, ← ha, u.qp_eq hr]
    ring
  · change u.y * u.b + (u.y * u.qp + u.z) * u.b = u.y * u.a + u.z * u.b
    rw [← ha, u.qp_eq hr]
    ring

/-- This is the main reduction step, which is used when u.r ≠ 0, or
equivalently b does not divide a. -/
def step : XgcdType :=
  XgcdType.mk (u.y * u.q + u.zp) u.y ((u.wp + 1) * u.q + u.x) u.wp u.bp (u.r - 1)

/-- We will apply the above step recursively.  The following result
is used to ensure that the process terminates. -/
theorem step_wf (hr : u.r ≠ 0) : SizeOf.sizeOf u.step < SizeOf.sizeOf u := by
  change u.r - 1 < u.bp
  have h₀ : u.r - 1 + 1 = u.r := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hr)
  have h₁ : u.r < u.bp + 1 := Nat.mod_lt (u.ap + 1) u.bp.succ_pos
  rw [← h₀] at h₁
  exact lt_of_succ_lt_succ h₁

theorem step_isSpecial (hs : u.IsSpecial) : u.step.IsSpecial := by
  dsimp [IsSpecial, step] at hs ⊢
  rw [mul_add, mul_comm u.y u.x, ← hs]
  ring

/-- The reduction step does not change the product vector. -/
theorem step_v (hr : u.r ≠ 0) : u.step.v = u.v.swap := by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  let hr : u.r - 1 + 1 = u.r := (add_comm _ 1).trans (add_tsub_cancel_of_le (Nat.pos_of_ne_zero hr))
  ext
  · change ((u.y * u.q + u.z) * u.b + u.y * (u.r - 1 + 1) : ℕ) = u.y * u.a + u.z * u.b
    rw [← ha, hr]
    ring
  · change ((u.w * u.q + u.x) * u.b + u.w * (u.r - 1 + 1) : ℕ) = u.w * u.a + u.x * u.b
    rw [← ha, hr]
    ring

/-- We can now define the full reduction function, which applies
step as long as possible, and then applies finish. Note that the
"have" statement puts a fact in the local context, and the
equation compiler uses this fact to help construct the full
definition in terms of well-founded recursion.  The same fact
needs to be introduced in all the inductive proofs of properties
given below. -/
def reduce (u : XgcdType) : XgcdType :=
  dite (u.r = 0) (fun _ => u.finish) fun _h =>
    flip (reduce u.step)
decreasing_by apply u.step_wf _h

theorem reduce_a {u : XgcdType} (h : u.r = 0) : u.reduce = u.finish := by
  rw [reduce]
  exact if_pos h

theorem reduce_b {u : XgcdType} (h : u.r ≠ 0) : u.reduce = u.step.reduce.flip := by
  rw [reduce]
  exact if_neg h

theorem reduce_isReduced : ∀ u : XgcdType, u.reduce.IsReduced
  | u =>
    dite (u.r = 0)
      (fun h => by
        rw [reduce_a h]
        exact u.finish_isReduced)
      fun h => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h, flip_isReduced]
      apply reduce_isReduced

theorem reduce_isReduced' (u : XgcdType) : u.reduce.IsReduced' :=
  (isReduced_iff _).mp u.reduce_isReduced

theorem reduce_isSpecial : ∀ u : XgcdType, u.IsSpecial → u.reduce.IsSpecial
  | u =>
    dite (u.r = 0)
      (fun h hs => by
        rw [reduce_a h]
        exact u.finish_isSpecial hs)
      fun h hs => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h]
      exact (flip_isSpecial _).mpr (reduce_isSpecial _ (u.step_isSpecial hs))

theorem reduce_isSpecial' (u : XgcdType) (hs : u.IsSpecial) : u.reduce.IsSpecial' :=
  (isSpecial_iff _).mp (u.reduce_isSpecial hs)

theorem reduce_v : ∀ u : XgcdType, u.reduce.v = u.v
  | u =>
    dite (u.r = 0) (fun h => by rw [reduce_a h, finish_v u h]) fun h => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h, flip_v, reduce_v (step u), step_v u h, Prod.swap_swap]

end XgcdType

section gcd

variable (a b : ℕ+)

/-- Extended Euclidean algorithm -/
def xgcd : XgcdType :=
  (XgcdType.start a b).reduce

/-- `gcdD a b = gcd a b` -/
def gcdD : ℕ+ :=
  (xgcd a b).a

/-- Final value of `w` -/
def gcdW : ℕ+ :=
  (xgcd a b).w

/-- Final value of `x` -/
def gcdX : ℕ :=
  (xgcd a b).x

/-- Final value of `y` -/
def gcdY : ℕ :=
  (xgcd a b).y

/-- Final value of `z` -/
def gcdZ : ℕ+ :=
  (xgcd a b).z

/-- Final value of `a / d` -/
def gcdA' : ℕ+ :=
  succPNat ((xgcd a b).wp + (xgcd a b).x)

/-- Final value of `b / d` -/
def gcdB' : ℕ+ :=
  succPNat ((xgcd a b).y + (xgcd a b).zp)

theorem gcdA'_coe : (gcdA' a b : ℕ) = gcdW a b + gcdX a b := by
  dsimp [gcdA', gcdX, gcdW, XgcdType.w]
  rw [add_right_comm]

theorem gcdB'_coe : (gcdB' a b : ℕ) = gcdY a b + gcdZ a b := by
  dsimp [gcdB', gcdY, gcdZ, XgcdType.z]
  rw [add_assoc]

theorem gcd_props :
    let d := gcdD a b
    let w := gcdW a b
    let x := gcdX a b
    let y := gcdY a b
    let z := gcdZ a b
    let a' := gcdA' a b
    let b' := gcdB' a b
    w * z = succPNat (x * y) ∧
      a = a' * d ∧
        b = b' * d ∧
          z * a' = succPNat (x * b') ∧
            w * b' = succPNat (y * a') ∧ (z * a : ℕ) = x * b + d ∧ (w * b : ℕ) = y * a + d := by
  intro d w x y z a' b'
  let u := XgcdType.start a b
  let ur := u.reduce
  have hb : d = ur.b := u.reduce_isReduced'
  have ha' : (a' : ℕ) = w + x := gcdA'_coe a b
  have hb' : (b' : ℕ) = y + z := gcdB'_coe a b
  have hdet : w * z = succPNat (x * y) := u.reduce_isSpecial' rfl
  constructor
  · exact hdet
  have hdet' : (w * z : ℕ) = x * y + 1 := by rw [← mul_coe, hdet, succPNat_coe]
  let hv : Prod.mk (w * d + x * ur.b : ℕ) (y * d + z * ur.b : ℕ) = ⟨a, b⟩ :=
    u.reduce_v.trans (XgcdType.start_v a b)
  rw [← hb, ← add_mul, ← add_mul, ← ha', ← hb'] at hv
  have ha'' : (a : ℕ) = a' * d := (congr_arg Prod.fst hv).symm
  have hb'' : (b : ℕ) = b' * d := (congr_arg Prod.snd hv).symm
  constructor
  · exact eq ha''
  constructor
  · exact eq hb''
  have hza' : (z * a' : ℕ) = x * b' + 1 := by
    rw [ha', hb', mul_add, mul_add, mul_comm (z : ℕ), hdet']
    ring
  have hwb' : (w * b' : ℕ) = y * a' + 1 := by
    rw [ha', hb', mul_add, mul_add, hdet']
    ring
  constructor
  · apply eq
    rw [succPNat_coe, Nat.succ_eq_add_one, mul_coe, hza']
  constructor
  · apply eq
    rw [succPNat_coe, Nat.succ_eq_add_one, mul_coe, hwb']
  rw [ha'', hb'']
  repeat rw [← @mul_assoc]
  rw [hza', hwb']
  constructor <;> ring

theorem gcd_eq : gcdD a b = gcd a b := by
  rcases gcd_props a b with ⟨_, h₁, h₂, _, _, h₅, _⟩
  apply dvd_antisymm
  · apply dvd_gcd
    · exact Dvd.intro (gcdA' a b) (h₁.trans (mul_comm _ _)).symm
    · exact Dvd.intro (gcdB' a b) (h₂.trans (mul_comm _ _)).symm
  · have h₇ : (gcd a b : ℕ) ∣ gcdZ a b * a := (Nat.gcd_dvd_left a b).trans (dvd_mul_left _ _)
    have h₈ : (gcd a b : ℕ) ∣ gcdX a b * b := (Nat.gcd_dvd_right a b).trans (dvd_mul_left _ _)
    rw [h₅] at h₇
    rw [dvd_iff]
    exact (Nat.dvd_add_iff_right h₈).mpr h₇

theorem gcd_det_eq : gcdW a b * gcdZ a b = succPNat (gcdX a b * gcdY a b) :=
  (gcd_props a b).1

theorem gcd_a_eq : a = gcdA' a b * gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.1

theorem gcd_b_eq : b = gcdB' a b * gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.1

theorem gcd_rel_left' : gcdZ a b * gcdA' a b = succPNat (gcdX a b * gcdB' a b) :=
  (gcd_props a b).2.2.2.1

theorem gcd_rel_right' : gcdW a b * gcdB' a b = succPNat (gcdY a b * gcdA' a b) :=
  (gcd_props a b).2.2.2.2.1

theorem gcd_rel_left : (gcdZ a b * a : ℕ) = gcdX a b * b + gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.1

theorem gcd_rel_right : (gcdW a b * b : ℕ) = gcdY a b * a + gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.2

end gcd

end PNat
