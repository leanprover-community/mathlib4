/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

! This file was ported from Lean 3 source module data.pnat.xgcd
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Ring
import Mathbin.Data.Pnat.Prime

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

* `xgcd_type`: Helper type in defining the gcd. Encapsulates `(wp, x, y, zp, ap, bp)`. where `wp`
  `zp`, `ap`, `bp` are the variables getting changed through the algorithm.
* `is_special`: States `wp * zp = x * y + 1`
* `is_reduced`: States `ap = a ∧ bp = b`

## Notes

See `nat.xgcd` for a very similar algorithm allowing values in `ℤ`.
-/


open Nat

namespace PNat

/-- A term of xgcd_type is a system of six naturals.  They should
 be thought of as representing the matrix
 [[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]
 together with the vector [a, b] = [ap + 1, bp + 1].
-/
structure XgcdType where
  (wp x y zp ap bp : ℕ)
  deriving Inhabited
#align pnat.xgcd_type PNat.XgcdType

namespace XgcdType

variable (u : XgcdType)

instance : SizeOf XgcdType :=
  ⟨fun u => u.bp⟩

/-- The has_repr instance converts terms to strings in a way that
 reflects the matrix/vector interpretation as above. -/
instance : Repr XgcdType :=
  ⟨fun u =>
    "[[[" ++ repr (u.wp + 1) ++ ", " ++ repr u.x ++ "], [" ++ repr u.y ++ ", " ++ repr (u.zp + 1) ++
              "]], [" ++
            repr (u.ap + 1) ++
          ", " ++
        repr (u.bp + 1) ++
      "]]"⟩

def mk' (w : ℕ+) (x : ℕ) (y : ℕ) (z : ℕ+) (a : ℕ+) (b : ℕ+) : XgcdType :=
  mk w.val.pred x y z.val.pred a.val.pred b.val.pred
#align pnat.xgcd_type.mk' PNat.XgcdType.mk'

def w : ℕ+ :=
  succPNat u.wp
#align pnat.xgcd_type.w PNat.XgcdType.w

def z : ℕ+ :=
  succPNat u.zp
#align pnat.xgcd_type.z PNat.XgcdType.z

def a : ℕ+ :=
  succPNat u.ap
#align pnat.xgcd_type.a PNat.XgcdType.a

def b : ℕ+ :=
  succPNat u.bp
#align pnat.xgcd_type.b PNat.XgcdType.b

def r : ℕ :=
  (u.ap + 1) % (u.bp + 1)
#align pnat.xgcd_type.r PNat.XgcdType.r

def q : ℕ :=
  (u.ap + 1) / (u.bp + 1)
#align pnat.xgcd_type.q PNat.XgcdType.q

def qp : ℕ :=
  u.q - 1
#align pnat.xgcd_type.qp PNat.XgcdType.qp

/-- The map v gives the product of the matrix
 [[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]
 and the vector [a, b] = [ap + 1, bp + 1].  The map
 vp gives [sp, tp] such that v = [sp + 1, tp + 1].
-/
def vp : ℕ × ℕ :=
  ⟨u.wp + u.x + u.ap + u.wp * u.ap + u.x * u.bp, u.y + u.zp + u.bp + u.y * u.ap + u.zp * u.bp⟩
#align pnat.xgcd_type.vp PNat.XgcdType.vp

def v : ℕ × ℕ :=
  ⟨u.w * u.a + u.x * u.b, u.y * u.a + u.z * u.b⟩
#align pnat.xgcd_type.v PNat.XgcdType.v

def succ₂ (t : ℕ × ℕ) : ℕ × ℕ :=
  ⟨t.1.succ, t.2.succ⟩
#align pnat.xgcd_type.succ₂ PNat.XgcdType.succ₂

theorem v_eq_succ_vp : u.V = succ₂ u.vp := by
  ext <;> dsimp [v, vp, w, z, a, b, succ₂] <;> repeat' rw [Nat.succ_eq_add_one] <;> ring
#align pnat.xgcd_type.v_eq_succ_vp PNat.XgcdType.v_eq_succ_vp

/-- is_special holds if the matrix has determinant one. -/
def IsSpecial : Prop :=
  u.wp + u.zp + u.wp * u.zp = u.x * u.y
#align pnat.xgcd_type.is_special PNat.XgcdType.IsSpecial

def IsSpecial' : Prop :=
  u.w * u.z = succPNat (u.x * u.y)
#align pnat.xgcd_type.is_special' PNat.XgcdType.IsSpecial'

theorem is_special_iff : u.IsSpecial ↔ u.IsSpecial' :=
  by
  dsimp [is_special, is_special']
  constructor <;> intro h
  · apply Eq
    dsimp [w, z, succ_pnat]
    rw [← h]
    repeat' rw [Nat.succ_eq_add_one]
    ring
  · apply Nat.succ.inj
    replace h := congr_arg (coe : ℕ+ → ℕ) h
    rw [mul_coe, w, z] at h
    repeat' rw [succ_pnat_coe, Nat.succ_eq_add_one] at h
    repeat' rw [Nat.succ_eq_add_one]
    rw [← h]
    ring
#align pnat.xgcd_type.is_special_iff PNat.XgcdType.is_special_iff

/-- is_reduced holds if the two entries in the vector are the
 same.  The reduction algorithm will produce a system with this
 property, whose product vector is the same as for the original
 system. -/
def IsReduced : Prop :=
  u.ap = u.bp
#align pnat.xgcd_type.is_reduced PNat.XgcdType.IsReduced

def IsReduced' : Prop :=
  u.a = u.b
#align pnat.xgcd_type.is_reduced' PNat.XgcdType.IsReduced'

theorem is_reduced_iff : u.IsReduced ↔ u.IsReduced' :=
  succPNat_inj.symm
#align pnat.xgcd_type.is_reduced_iff PNat.XgcdType.is_reduced_iff

def flip : XgcdType where
  wp := u.zp
  x := u.y
  y := u.x
  zp := u.wp
  ap := u.bp
  bp := u.ap
#align pnat.xgcd_type.flip PNat.XgcdType.flip

@[simp]
theorem flip_w : (flip u).w = u.z :=
  rfl
#align pnat.xgcd_type.flip_w PNat.XgcdType.flip_w

@[simp]
theorem flip_x : (flip u).x = u.y :=
  rfl
#align pnat.xgcd_type.flip_x PNat.XgcdType.flip_x

@[simp]
theorem flip_y : (flip u).y = u.x :=
  rfl
#align pnat.xgcd_type.flip_y PNat.XgcdType.flip_y

@[simp]
theorem flip_z : (flip u).z = u.w :=
  rfl
#align pnat.xgcd_type.flip_z PNat.XgcdType.flip_z

@[simp]
theorem flip_a : (flip u).a = u.b :=
  rfl
#align pnat.xgcd_type.flip_a PNat.XgcdType.flip_a

@[simp]
theorem flip_b : (flip u).b = u.a :=
  rfl
#align pnat.xgcd_type.flip_b PNat.XgcdType.flip_b

theorem flip_is_reduced : (flip u).IsReduced ↔ u.IsReduced :=
  by
  dsimp [is_reduced, flip]
  constructor <;> intro h <;> exact h.symm
#align pnat.xgcd_type.flip_is_reduced PNat.XgcdType.flip_is_reduced

theorem flip_is_special : (flip u).IsSpecial ↔ u.IsSpecial :=
  by
  dsimp [is_special, flip]
  rw [mul_comm u.x, mul_comm u.zp, add_comm u.zp]
#align pnat.xgcd_type.flip_is_special PNat.XgcdType.flip_is_special

theorem flip_v : (flip u).V = u.V.swap := by
  dsimp [v]
  ext
  · simp only
    ring
  · simp only
    ring
#align pnat.xgcd_type.flip_v PNat.XgcdType.flip_v

/-- Properties of division with remainder for a / b.  -/
theorem rq_eq : u.R + (u.bp + 1) * u.q = u.ap + 1 :=
  Nat.mod_add_div (u.ap + 1) (u.bp + 1)
#align pnat.xgcd_type.rq_eq PNat.XgcdType.rq_eq

theorem qp_eq (hr : u.R = 0) : u.q = u.qp + 1 :=
  by
  by_cases hq : u.q = 0
  · let h := u.rq_eq
    rw [hr, hq, mul_zero, add_zero] at h
    cases h
  · exact (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hq)).symm
#align pnat.xgcd_type.qp_eq PNat.XgcdType.qp_eq

/-- The following function provides the starting point for
 our algorithm.  We will apply an iterative reduction process
 to it, which will produce a system satisfying is_reduced.
 The gcd can be read off from this final system.
-/
def start (a b : ℕ+) : XgcdType :=
  ⟨0, 0, 0, 0, a - 1, b - 1⟩
#align pnat.xgcd_type.start PNat.XgcdType.start

theorem start_is_special (a b : ℕ+) : (start a b).IsSpecial :=
  by
  dsimp [start, is_special]
  rfl
#align pnat.xgcd_type.start_is_special PNat.XgcdType.start_is_special

theorem start_v (a b : ℕ+) : (start a b).V = ⟨a, b⟩ :=
  by
  dsimp [start, v, xgcd_type.a, xgcd_type.b, w, z]
  rw [one_mul, one_mul, zero_mul, zero_mul, zero_add, add_zero]
  rw [← Nat.pred_eq_sub_one, ← Nat.pred_eq_sub_one]
  rw [Nat.succ_pred_eq_of_pos a.pos, Nat.succ_pred_eq_of_pos b.pos]
#align pnat.xgcd_type.start_v PNat.XgcdType.start_v

def finish : XgcdType :=
  XgcdType.mk u.wp ((u.wp + 1) * u.qp + u.x) u.y (u.y * u.qp + u.zp) u.bp u.bp
#align pnat.xgcd_type.finish PNat.XgcdType.finish

theorem finish_is_reduced : u.finish.IsReduced :=
  by
  dsimp [is_reduced]
  rfl
#align pnat.xgcd_type.finish_is_reduced PNat.XgcdType.finish_is_reduced

theorem finish_is_special (hs : u.IsSpecial) : u.finish.IsSpecial :=
  by
  dsimp [is_special, finish] at hs⊢
  rw [add_mul _ _ u.y, add_comm _ (u.x * u.y), ← hs]
  ring
#align pnat.xgcd_type.finish_is_special PNat.XgcdType.finish_is_special

theorem finish_v (hr : u.R = 0) : u.finish.V = u.V :=
  by
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
#align pnat.xgcd_type.finish_v PNat.XgcdType.finish_v

/-- This is the main reduction step, which is used when u.r ≠ 0, or
 equivalently b does not divide a. -/
def step : XgcdType :=
  XgcdType.mk (u.y * u.q + u.zp) u.y ((u.wp + 1) * u.q + u.x) u.wp u.bp (u.R - 1)
#align pnat.xgcd_type.step PNat.XgcdType.step

/-- We will apply the above step recursively.  The following result
 is used to ensure that the process terminates. -/
theorem step_wf (hr : u.R ≠ 0) : SizeOf.sizeOf u.step < SizeOf.sizeOf u :=
  by
  change u.r - 1 < u.bp
  have h₀ : u.r - 1 + 1 = u.r := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hr)
  have h₁ : u.r < u.bp + 1 := Nat.mod_lt (u.ap + 1) u.bp.succ_pos
  rw [← h₀] at h₁
  exact lt_of_succ_lt_succ h₁
#align pnat.xgcd_type.step_wf PNat.XgcdType.step_wf

theorem step_is_special (hs : u.IsSpecial) : u.step.IsSpecial :=
  by
  dsimp [is_special, step] at hs⊢
  rw [mul_add, mul_comm u.y u.x, ← hs]
  ring
#align pnat.xgcd_type.step_is_special PNat.XgcdType.step_is_special

/-- The reduction step does not change the product vector. -/
theorem step_v (hr : u.R ≠ 0) : u.step.V = u.V.swap :=
  by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  let hr : u.r - 1 + 1 = u.r := (add_comm _ 1).trans (add_tsub_cancel_of_le (Nat.pos_of_ne_zero hr))
  ext
  · change ((u.y * u.q + u.z) * u.b + u.y * (u.r - 1 + 1) : ℕ) = u.y * u.a + u.z * u.b
    rw [← ha, hr]
    ring
  · change ((u.w * u.q + u.x) * u.b + u.w * (u.r - 1 + 1) : ℕ) = u.w * u.a + u.x * u.b
    rw [← ha, hr]
    ring
#align pnat.xgcd_type.step_v PNat.XgcdType.step_v

/-- We can now define the full reduction function, which applies
 step as long as possible, and then applies finish. Note that the
 "have" statement puts a fact in the local context, and the
 equation compiler uses this fact to help construct the full
 definition in terms of well-founded recursion.  The same fact
 needs to be introduced in all the inductive proofs of properties
 given below. -/
def reduce : XgcdType → XgcdType
  | u =>
    dite (u.R = 0) (fun h => u.finish) fun h =>
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      flip (reduce u.step)
#align pnat.xgcd_type.reduce PNat.XgcdType.reduce

theorem reduce_a {u : XgcdType} (h : u.R = 0) : u.reduce = u.finish :=
  by
  rw [reduce]
  simp only
  rw [if_pos h]
#align pnat.xgcd_type.reduce_a PNat.XgcdType.reduce_a

theorem reduce_b {u : XgcdType} (h : u.R ≠ 0) : u.reduce = u.step.reduce.flip :=
  by
  rw [reduce]
  simp only
  rw [if_neg h, step]
#align pnat.xgcd_type.reduce_b PNat.XgcdType.reduce_b

theorem reduce_reduced : ∀ u : XgcdType, u.reduce.IsReduced
  | u =>
    dite (u.R = 0)
      (fun h => by
        rw [reduce_a h]
        exact u.finish_is_reduced)
      fun h => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h, flip_is_reduced]
      apply reduce_reduced
#align pnat.xgcd_type.reduce_reduced PNat.XgcdType.reduce_reduced

theorem reduce_reduced' (u : XgcdType) : u.reduce.IsReduced' :=
  (is_reduced_iff _).mp u.reduce_reduced
#align pnat.xgcd_type.reduce_reduced' PNat.XgcdType.reduce_reduced'

theorem reduce_special : ∀ u : XgcdType, u.IsSpecial → u.reduce.IsSpecial
  | u =>
    dite (u.R = 0)
      (fun h hs => by
        rw [reduce_a h]
        exact u.finish_is_special hs)
      fun h hs => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h]
      exact (flip_is_special _).mpr (reduce_special _ (u.step_is_special hs))
#align pnat.xgcd_type.reduce_special PNat.XgcdType.reduce_special

theorem reduce_special' (u : XgcdType) (hs : u.IsSpecial) : u.reduce.IsSpecial' :=
  (is_special_iff _).mp (u.reduce_special hs)
#align pnat.xgcd_type.reduce_special' PNat.XgcdType.reduce_special'

theorem reduce_v : ∀ u : XgcdType, u.reduce.V = u.V
  | u =>
    dite (u.R = 0) (fun h => by rw [reduce_a h, finish_v u h]) fun h =>
      by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h, flip_v, reduce_v (step u), step_v u h, Prod.swap_swap]
#align pnat.xgcd_type.reduce_v PNat.XgcdType.reduce_v

end XgcdType

section Gcd

variable (a b : ℕ+)

def xgcd : XgcdType :=
  (XgcdType.start a b).reduce
#align pnat.xgcd PNat.xgcd

def gcdD : ℕ+ :=
  (xgcd a b).a
#align pnat.gcd_d PNat.gcdD

def gcdW : ℕ+ :=
  (xgcd a b).w
#align pnat.gcd_w PNat.gcdW

def gcdX : ℕ :=
  (xgcd a b).x
#align pnat.gcd_x PNat.gcdX

def gcdY : ℕ :=
  (xgcd a b).y
#align pnat.gcd_y PNat.gcdY

def gcdZ : ℕ+ :=
  (xgcd a b).z
#align pnat.gcd_z PNat.gcdZ

def gcdA' : ℕ+ :=
  succPNat ((xgcd a b).wp + (xgcd a b).x)
#align pnat.gcd_a' PNat.gcdA'

def gcdB' : ℕ+ :=
  succPNat ((xgcd a b).y + (xgcd a b).zp)
#align pnat.gcd_b' PNat.gcdB'

theorem gcd_a'_coe : (gcdA' a b : ℕ) = gcdW a b + gcdX a b :=
  by
  dsimp [gcd_a', gcd_x, gcd_w, xgcd_type.w]
  rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, add_right_comm]
#align pnat.gcd_a'_coe PNat.gcd_a'_coe

theorem gcd_b'_coe : (gcdB' a b : ℕ) = gcdY a b + gcdZ a b :=
  by
  dsimp [gcd_b', gcd_y, gcd_z, xgcd_type.z]
  rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, add_assoc]
#align pnat.gcd_b'_coe PNat.gcd_b'_coe

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
            w * b' = succPNat (y * a') ∧ (z * a : ℕ) = x * b + d ∧ (w * b : ℕ) = y * a + d :=
  by
  intros
  let u := xgcd_type.start a b
  let ur := u.reduce
  have ha : d = ur.a := rfl
  have hb : d = ur.b := u.reduce_reduced'
  have ha' : (a' : ℕ) = w + x := gcd_a'_coe a b
  have hb' : (b' : ℕ) = y + z := gcd_b'_coe a b
  have hdet : w * z = succ_pnat (x * y) := u.reduce_special' rfl
  constructor
  exact hdet
  have hdet' : (w * z : ℕ) = x * y + 1 := by rw [← mul_coe, hdet, succ_pnat_coe]
  have huv : u.v = ⟨a, b⟩ := xgcd_type.start_v a b
  let hv : Prod.mk (w * d + x * ur.b : ℕ) (y * d + z * ur.b : ℕ) = ⟨a, b⟩ :=
    u.reduce_v.trans (xgcd_type.start_v a b)
  rw [← hb, ← add_mul, ← add_mul, ← ha', ← hb'] at hv
  have ha'' : (a : ℕ) = a' * d := (congr_arg Prod.fst hv).symm
  have hb'' : (b : ℕ) = b' * d := (congr_arg Prod.snd hv).symm
  constructor
  exact Eq ha''
  constructor
  exact Eq hb''
  have hza' : (z * a' : ℕ) = x * b' + 1 :=
    by
    rw [ha', hb', mul_add, mul_add, mul_comm (z : ℕ), hdet']
    ring
  have hwb' : (w * b' : ℕ) = y * a' + 1 :=
    by
    rw [ha', hb', mul_add, mul_add, hdet']
    ring
  constructor
  · apply Eq
    rw [succ_pnat_coe, Nat.succ_eq_add_one, mul_coe, hza']
  constructor
  · apply Eq
    rw [succ_pnat_coe, Nat.succ_eq_add_one, mul_coe, hwb']
  rw [ha'', hb'']
  repeat' rw [← mul_assoc]
  rw [hza', hwb']
  constructor <;> ring
#align pnat.gcd_props PNat.gcd_props

theorem gcd_eq : gcdD a b = gcd a b :=
  by
  rcases gcd_props a b with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩
  apply dvd_antisymm
  · apply dvd_gcd
    exact Dvd.intro (gcd_a' a b) (h₁.trans (mul_comm _ _)).symm
    exact Dvd.intro (gcd_b' a b) (h₂.trans (mul_comm _ _)).symm
  · have h₇ : (gcd a b : ℕ) ∣ gcd_z a b * a := (Nat.gcd_dvd_left a b).trans (dvd_mul_left _ _)
    have h₈ : (gcd a b : ℕ) ∣ gcd_x a b * b := (Nat.gcd_dvd_right a b).trans (dvd_mul_left _ _)
    rw [h₅] at h₇
    rw [dvd_iff]
    exact (Nat.dvd_add_iff_right h₈).mpr h₇
#align pnat.gcd_eq PNat.gcd_eq

theorem gcd_det_eq : gcdW a b * gcdZ a b = succPNat (gcdX a b * gcdY a b) :=
  (gcd_props a b).1
#align pnat.gcd_det_eq PNat.gcd_det_eq

theorem gcd_a_eq : a = gcdA' a b * gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.1
#align pnat.gcd_a_eq PNat.gcd_a_eq

theorem gcd_b_eq : b = gcdB' a b * gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.1
#align pnat.gcd_b_eq PNat.gcd_b_eq

theorem gcd_rel_left' : gcdZ a b * gcdA' a b = succPNat (gcdX a b * gcdB' a b) :=
  (gcd_props a b).2.2.2.1
#align pnat.gcd_rel_left' PNat.gcd_rel_left'

theorem gcd_rel_right' : gcdW a b * gcdB' a b = succPNat (gcdY a b * gcdA' a b) :=
  (gcd_props a b).2.2.2.2.1
#align pnat.gcd_rel_right' PNat.gcd_rel_right'

theorem gcd_rel_left : (gcdZ a b * a : ℕ) = gcdX a b * b + gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.1
#align pnat.gcd_rel_left PNat.gcd_rel_left

theorem gcd_rel_right : (gcdW a b * b : ℕ) = gcdY a b * a + gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.2
#align pnat.gcd_rel_right PNat.gcd_rel_right

end Gcd

end PNat

