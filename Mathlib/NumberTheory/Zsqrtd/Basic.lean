/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Associated
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Star.Unitary

#align_import number_theory.zsqrtd.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-! # ℤ[√d]

The ring of integers adjoined with a square root of `d : ℤ`.

After defining the norm, we show that it is a linearly ordered commutative ring,
as well as an integral domain.

We provide the universal property, that ring homomorphisms `ℤ√d →+* R` correspond
to choices of square roots of `d` in `R`.

-/


/-- The ring of integers adjoined with a square root of `d`.
  These have the form `a + b √d` where `a b : ℤ`. The components
  are called `re` and `im` by analogy to the negative `d` case. -/
structure Zsqrtd (d : ℤ) where
  re : ℤ
  im : ℤ
  deriving DecidableEq
#align zsqrtd Zsqrtd

prefix:100 "ℤ√" => Zsqrtd

namespace Zsqrtd

section

variable {d : ℤ}

theorem ext : ∀ {z w : ℤ√d}, z = w ↔ z.re = w.re ∧ z.im = w.im
  | ⟨x, y⟩, ⟨x', y'⟩ =>
    ⟨fun h => by injection h; constructor <;> assumption,
                 -- ⊢ { re := x, im := y }.re = { re := x', im := y' }.re ∧ { re := x, im := y }.i …
                              -- ⊢ { re := x, im := y }.re = { re := x', im := y' }.re
                                              -- 🎉 no goals
                                              -- 🎉 no goals
     fun ⟨h₁, h₂⟩ => by congr⟩
                        -- 🎉 no goals
#align zsqrtd.ext Zsqrtd.ext

/-- Convert an integer to a `ℤ√d` -/
def ofInt (n : ℤ) : ℤ√d :=
  ⟨n, 0⟩
#align zsqrtd.of_int Zsqrtd.ofInt

theorem ofInt_re (n : ℤ) : (ofInt n : ℤ√d).re = n :=
  rfl
#align zsqrtd.of_int_re Zsqrtd.ofInt_re

theorem ofInt_im (n : ℤ) : (ofInt n : ℤ√d).im = 0 :=
  rfl
#align zsqrtd.of_int_im Zsqrtd.ofInt_im

/-- The zero of the ring -/
instance : Zero (ℤ√d) :=
  ⟨ofInt 0⟩

@[simp]
theorem zero_re : (0 : ℤ√d).re = 0 :=
  rfl
#align zsqrtd.zero_re Zsqrtd.zero_re

@[simp]
theorem zero_im : (0 : ℤ√d).im = 0 :=
  rfl
#align zsqrtd.zero_im Zsqrtd.zero_im

instance : Inhabited (ℤ√d) :=
  ⟨0⟩

/-- The one of the ring -/
instance : One (ℤ√d) :=
  ⟨ofInt 1⟩

@[simp]
theorem one_re : (1 : ℤ√d).re = 1 :=
  rfl
#align zsqrtd.one_re Zsqrtd.one_re

@[simp]
theorem one_im : (1 : ℤ√d).im = 0 :=
  rfl
#align zsqrtd.one_im Zsqrtd.one_im

/-- The representative of `√d` in the ring -/
def sqrtd : ℤ√d :=
  ⟨0, 1⟩
#align zsqrtd.sqrtd Zsqrtd.sqrtd

@[simp]
theorem sqrtd_re : (sqrtd : ℤ√d).re = 0 :=
  rfl
#align zsqrtd.sqrtd_re Zsqrtd.sqrtd_re

@[simp]
theorem sqrtd_im : (sqrtd : ℤ√d).im = 1 :=
  rfl
#align zsqrtd.sqrtd_im Zsqrtd.sqrtd_im

/-- Addition of elements of `ℤ√d` -/
instance : Add (ℤ√d) :=
  ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]
theorem add_def (x y x' y' : ℤ) : (⟨x, y⟩ + ⟨x', y'⟩ : ℤ√d) = ⟨x + x', y + y'⟩ :=
  rfl
#align zsqrtd.add_def Zsqrtd.add_def

@[simp]
theorem add_re (z w : ℤ√d) : (z + w).re = z.re + w.re :=
  rfl
#align zsqrtd.add_re Zsqrtd.add_re

@[simp]
theorem add_im (z w : ℤ√d) : (z + w).im = z.im + w.im :=
  rfl
#align zsqrtd.add_im Zsqrtd.add_im

section bit
set_option linter.deprecated false

@[simp]
theorem bit0_re (z) : (bit0 z : ℤ√d).re = bit0 z.re :=
  rfl
#align zsqrtd.bit0_re Zsqrtd.bit0_re

@[simp]
theorem bit0_im (z) : (bit0 z : ℤ√d).im = bit0 z.im :=
  rfl
#align zsqrtd.bit0_im Zsqrtd.bit0_im

@[simp]
theorem bit1_re (z) : (bit1 z : ℤ√d).re = bit1 z.re :=
  rfl
#align zsqrtd.bit1_re Zsqrtd.bit1_re

@[simp]
theorem bit1_im (z) : (bit1 z : ℤ√d).im = bit0 z.im := by simp [bit1]
                                                          -- 🎉 no goals
#align zsqrtd.bit1_im Zsqrtd.bit1_im

end bit

/-- Negation in `ℤ√d` -/
instance : Neg (ℤ√d) :=
  ⟨fun z => ⟨-z.1, -z.2⟩⟩

@[simp]
theorem neg_re (z : ℤ√d) : (-z).re = -z.re :=
  rfl
#align zsqrtd.neg_re Zsqrtd.neg_re

@[simp]
theorem neg_im (z : ℤ√d) : (-z).im = -z.im :=
  rfl
#align zsqrtd.neg_im Zsqrtd.neg_im

/-- Multiplication in `ℤ√d` -/
instance : Mul (ℤ√d) :=
  ⟨fun z w => ⟨z.1 * w.1 + d * z.2 * w.2, z.1 * w.2 + z.2 * w.1⟩⟩

@[simp]
theorem mul_re (z w : ℤ√d) : (z * w).re = z.re * w.re + d * z.im * w.im :=
  rfl
#align zsqrtd.mul_re Zsqrtd.mul_re

@[simp]
theorem mul_im (z w : ℤ√d) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl
#align zsqrtd.mul_im Zsqrtd.mul_im

instance addCommGroup : AddCommGroup (ℤ√d) := by
  refine
  { add := (· + ·)
    zero := (0 : ℤ√d)
    sub := fun a b => a + -b
    neg := Neg.neg
    zsmul := @zsmulRec (ℤ√d) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
    nsmul := @nsmulRec (ℤ√d) ⟨0⟩ ⟨(· + ·)⟩
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    add_left_neg := ?_
    add_comm := ?_ } <;>
  intros <;>
  -- ⊢ a✝ + b✝ + c✝ = a✝ + (b✝ + c✝)
  -- ⊢ 0 + a✝ = a✝
  -- ⊢ a✝ + 0 = a✝
  -- ⊢ -a✝ + a✝ = 0
  -- ⊢ a✝ + b✝ = b✝ + a✝
  simp [ext, add_comm, add_left_comm]
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals

instance addGroupWithOne : AddGroupWithOne (ℤ√d) :=
  { Zsqrtd.addCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt
    one := 1 }

instance commRing : CommRing (ℤ√d) := by
  refine
  { Zsqrtd.addGroupWithOne with
    add := (· + ·)
    zero := (0 : ℤ√d)
    mul := (· * ·)
    one := 1
    npow := @npowRec (ℤ√d) ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  -- ⊢ a✝ + b✝ = b✝ + a✝
  -- ⊢ a✝ * (b✝ + c✝) = a✝ * b✝ + a✝ * c✝
  -- ⊢ (a✝ + b✝) * c✝ = a✝ * c✝ + b✝ * c✝
  -- ⊢ 0 * a✝ = 0
  -- ⊢ a✝ * 0 = 0
  -- ⊢ a✝ * b✝ * c✝ = a✝ * (b✝ * c✝)
  -- ⊢ 1 * a✝ = a✝
  -- ⊢ a✝ * 1 = a✝
  -- ⊢ a✝ * b✝ = b✝ * a✝
  refine ext.mpr ⟨?_, ?_⟩ <;>
  -- ⊢ (a✝ + b✝).re = (b✝ + a✝).re
  simp <;>
  -- ⊢ a✝.re + b✝.re = b✝.re + a✝.re
  -- ⊢ a✝.im + b✝.im = b✝.im + a✝.im
  -- ⊢ a✝.re * (b✝.re + c✝.re) + d * a✝.im * (b✝.im + c✝.im) = a✝.re * b✝.re + d *  …
  -- ⊢ a✝.re * (b✝.im + c✝.im) + a✝.im * (b✝.re + c✝.re) = a✝.re * b✝.im + a✝.im *  …
  -- ⊢ (a✝.re + b✝.re) * c✝.re + d * (a✝.im + b✝.im) * c✝.im = a✝.re * c✝.re + d *  …
  -- ⊢ (a✝.re + b✝.re) * c✝.im + (a✝.im + b✝.im) * c✝.re = a✝.re * c✝.im + a✝.im *  …
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- ⊢ (a✝.re * b✝.re + d * a✝.im * b✝.im) * c✝.re + d * (a✝.re * b✝.im + a✝.im * b …
  -- ⊢ (a✝.re * b✝.re + d * a✝.im * b✝.im) * c✝.im + (a✝.re * b✝.im + a✝.im * b✝.re …
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- ⊢ a✝.re * b✝.re + d * a✝.im * b✝.im = b✝.re * a✝.re + d * b✝.im * a✝.im
  -- ⊢ a✝.re * b✝.im + a✝.im * b✝.re = b✝.re * a✝.im + b✝.im * a✝.re
  ring
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals

instance : AddMonoid (ℤ√d) := by infer_instance
                                 -- 🎉 no goals

instance : Monoid (ℤ√d) := by infer_instance
                              -- 🎉 no goals

instance : CommMonoid (ℤ√d) := by infer_instance
                                  -- 🎉 no goals

instance : CommSemigroup (ℤ√d) := by infer_instance
                                     -- 🎉 no goals

instance : Semigroup (ℤ√d) := by infer_instance
                                 -- 🎉 no goals

instance : AddCommSemigroup (ℤ√d) := by infer_instance
                                        -- 🎉 no goals

instance : AddSemigroup (ℤ√d) := by infer_instance
                                    -- 🎉 no goals

instance : CommSemiring (ℤ√d) := by infer_instance
                                    -- 🎉 no goals

instance : Semiring (ℤ√d) := by infer_instance
                                -- 🎉 no goals

instance : Ring (ℤ√d) := by infer_instance
                            -- 🎉 no goals

instance : Distrib (ℤ√d) := by infer_instance
                               -- 🎉 no goals

/-- Conjugation in `ℤ√d`. The conjugate of `a + b √d` is `a - b √d`. -/
instance : Star (ℤ√d) where
  star z := ⟨z.1, -z.2⟩

@[simp]
theorem star_mk (x y : ℤ) : star (⟨x, y⟩ : ℤ√d) = ⟨x, -y⟩ :=
  rfl
#align zsqrtd.star_mk Zsqrtd.star_mk

@[simp]
theorem star_re (z : ℤ√d) : (star z).re = z.re :=
  rfl
#align zsqrtd.star_re Zsqrtd.star_re

@[simp]
theorem star_im (z : ℤ√d) : (star z).im = -z.im :=
  rfl
#align zsqrtd.star_im Zsqrtd.star_im

instance : StarRing (ℤ√d) where
  star_involutive x := ext.mpr ⟨rfl, neg_neg _⟩
  star_mul a b := ext.mpr ⟨by simp; ring, by simp; ring⟩
                              -- ⊢ a.re * b.re + d * a.im * b.im = b.re * a.re + d * b.im * a.im
                                    -- 🎉 no goals
                                             -- ⊢ -(a.im * b.re) + -(a.re * b.im) = -(b.re * a.im) + -(b.im * a.re)
                                                   -- 🎉 no goals
  star_add a b := ext.mpr ⟨rfl, neg_add _ _⟩

-- Porting note: proof was `by decide`
instance nontrivial : Nontrivial (ℤ√d) :=
  ⟨⟨0, 1, ext.not.mpr <| by simp⟩⟩
                            -- 🎉 no goals

@[simp]
theorem coe_nat_re (n : ℕ) : (n : ℤ√d).re = n :=
  rfl
#align zsqrtd.coe_nat_re Zsqrtd.coe_nat_re

@[simp]
theorem ofNat_re (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : ℤ√d).re = n :=
  rfl

@[simp]
theorem coe_nat_im (n : ℕ) : (n : ℤ√d).im = 0 :=
  rfl
#align zsqrtd.coe_nat_im Zsqrtd.coe_nat_im

@[simp]
theorem ofNat_im (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : ℤ√d).im = 0 :=
  rfl

theorem coe_nat_val (n : ℕ) : (n : ℤ√d) = ⟨n, 0⟩ :=
  rfl
#align zsqrtd.coe_nat_val Zsqrtd.coe_nat_val

@[simp]
theorem coe_int_re (n : ℤ) : (n : ℤ√d).re = n := by cases n <;> rfl
                                                    -- ⊢ (↑(Int.ofNat a✝)).re = Int.ofNat a✝
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
#align zsqrtd.coe_int_re Zsqrtd.coe_int_re

@[simp]
theorem coe_int_im (n : ℤ) : (n : ℤ√d).im = 0 := by cases n <;> rfl
                                                    -- ⊢ (↑(Int.ofNat a✝)).im = 0
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
#align zsqrtd.coe_int_im Zsqrtd.coe_int_im

theorem coe_int_val (n : ℤ) : (n : ℤ√d) = ⟨n, 0⟩ := by simp [ext]
                                                       -- 🎉 no goals
#align zsqrtd.coe_int_val Zsqrtd.coe_int_val

instance : CharZero (ℤ√d) where cast_injective m n := by simp [ext]
                                                         -- 🎉 no goals

@[simp]
theorem ofInt_eq_coe (n : ℤ) : (ofInt n : ℤ√d) = n := by simp [ext, ofInt_re, ofInt_im]
                                                         -- 🎉 no goals
#align zsqrtd.of_int_eq_coe Zsqrtd.ofInt_eq_coe

@[simp]
theorem smul_val (n x y : ℤ) : (n : ℤ√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by simp [ext]
                                                                         -- 🎉 no goals
#align zsqrtd.smul_val Zsqrtd.smul_val

theorem smul_re (a : ℤ) (b : ℤ√d) : (↑a * b).re = a * b.re := by simp
                                                                 -- 🎉 no goals
#align zsqrtd.smul_re Zsqrtd.smul_re

theorem smul_im (a : ℤ) (b : ℤ√d) : (↑a * b).im = a * b.im := by simp
                                                                 -- 🎉 no goals
#align zsqrtd.smul_im Zsqrtd.smul_im

@[simp]
theorem muld_val (x y : ℤ) : sqrtd (d := d) * ⟨x, y⟩ = ⟨d * y, x⟩ := by simp [ext]
                                                                        -- 🎉 no goals
#align zsqrtd.muld_val Zsqrtd.muld_val

@[simp]
theorem dmuld : sqrtd (d := d) * sqrtd (d := d) = d := by simp [ext]
                                                          -- 🎉 no goals
#align zsqrtd.dmuld Zsqrtd.dmuld

@[simp]
theorem smuld_val (n x y : ℤ) : sqrtd * (n : ℤ√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩ := by simp [ext]
                                                                                      -- 🎉 no goals
#align zsqrtd.smuld_val Zsqrtd.smuld_val

theorem decompose {x y : ℤ} : (⟨x, y⟩ : ℤ√d) = x + sqrtd (d := d) * y := by simp [ext]
                                                                            -- 🎉 no goals
#align zsqrtd.decompose Zsqrtd.decompose

theorem mul_star {x y : ℤ} : (⟨x, y⟩ * star ⟨x, y⟩ : ℤ√d) = x * x - d * y * y := by
  simp [ext, sub_eq_add_neg, mul_comm]
  -- 🎉 no goals
#align zsqrtd.mul_star Zsqrtd.mul_star

protected theorem coe_int_add (m n : ℤ) : (↑(m + n) : ℤ√d) = ↑m + ↑n :=
  (Int.castRingHom _).map_add _ _
#align zsqrtd.coe_int_add Zsqrtd.coe_int_add

protected theorem coe_int_sub (m n : ℤ) : (↑(m - n) : ℤ√d) = ↑m - ↑n :=
  (Int.castRingHom _).map_sub _ _
#align zsqrtd.coe_int_sub Zsqrtd.coe_int_sub

protected theorem coe_int_mul (m n : ℤ) : (↑(m * n) : ℤ√d) = ↑m * ↑n :=
  (Int.castRingHom _).map_mul _ _
#align zsqrtd.coe_int_mul Zsqrtd.coe_int_mul

protected theorem coe_int_inj {m n : ℤ} (h : (↑m : ℤ√d) = ↑n) : m = n := by
  simpa using congr_arg re h
  -- 🎉 no goals
#align zsqrtd.coe_int_inj Zsqrtd.coe_int_inj

theorem coe_int_dvd_iff (z : ℤ) (a : ℤ√d) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im := by
  constructor
  -- ⊢ ↑z ∣ a → z ∣ a.re ∧ z ∣ a.im
  · rintro ⟨x, rfl⟩
    -- ⊢ z ∣ (↑z * x).re ∧ z ∣ (↑z * x).im
    simp only [add_zero, coe_int_re, zero_mul, mul_im, dvd_mul_right, and_self_iff,
      mul_re, mul_zero, coe_int_im]
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    -- ⊢ ↑z ∣ a
    use ⟨r, i⟩
    -- ⊢ a = ↑z * { re := r, im := i }
    rw [smul_val, ext]
    -- ⊢ a.re = { re := z * r, im := z * i }.re ∧ a.im = { re := z * r, im := z * i } …
    exact ⟨hr, hi⟩
    -- 🎉 no goals
#align zsqrtd.coe_int_dvd_iff Zsqrtd.coe_int_dvd_iff

@[simp, norm_cast]
theorem coe_int_dvd_coe_int (a b : ℤ) : (a : ℤ√d) ∣ b ↔ a ∣ b := by
  rw [coe_int_dvd_iff]
  -- ⊢ a ∣ (↑b).re ∧ a ∣ (↑b).im ↔ a ∣ b
  constructor
  -- ⊢ a ∣ (↑b).re ∧ a ∣ (↑b).im → a ∣ b
  · rintro ⟨hre, -⟩
    -- ⊢ a ∣ b
    rwa [coe_int_re] at hre
    -- 🎉 no goals
  · rw [coe_int_re, coe_int_im]
    -- ⊢ a ∣ b → a ∣ b ∧ a ∣ 0
    exact fun hc => ⟨hc, dvd_zero a⟩
    -- 🎉 no goals
#align zsqrtd.coe_int_dvd_coe_int Zsqrtd.coe_int_dvd_coe_int

protected theorem eq_of_smul_eq_smul_left {a : ℤ} {b c : ℤ√d} (ha : a ≠ 0) (h : ↑a * b = a * c) :
    b = c := by
  rw [ext] at h ⊢
  -- ⊢ b.re = c.re ∧ b.im = c.im
  apply And.imp _ _ h <;> simpa only [smul_re, smul_im] using mul_left_cancel₀ ha
  -- ⊢ (↑a * b).re = (↑a * c).re → b.re = c.re
                          -- 🎉 no goals
                          -- 🎉 no goals
#align zsqrtd.eq_of_smul_eq_smul_left Zsqrtd.eq_of_smul_eq_smul_left

section Gcd

theorem gcd_eq_zero_iff (a : ℤ√d) : Int.gcd a.re a.im = 0 ↔ a = 0 := by
  simp only [Int.gcd_eq_zero_iff, ext, eq_self_iff_true, zero_im, zero_re]
  -- 🎉 no goals
#align zsqrtd.gcd_eq_zero_iff Zsqrtd.gcd_eq_zero_iff

theorem gcd_pos_iff (a : ℤ√d) : 0 < Int.gcd a.re a.im ↔ a ≠ 0 :=
  pos_iff_ne_zero.trans <| not_congr a.gcd_eq_zero_iff
#align zsqrtd.gcd_pos_iff Zsqrtd.gcd_pos_iff

theorem coprime_of_dvd_coprime {a b : ℤ√d} (hcoprime : IsCoprime a.re a.im) (hdvd : b ∣ a) :
    IsCoprime b.re b.im := by
  apply isCoprime_of_dvd
  -- ⊢ ¬(b.re = 0 ∧ b.im = 0)
  · rintro ⟨hre, him⟩
    -- ⊢ False
    obtain rfl : b = 0 := by
      simp only [ext, hre, eq_self_iff_true, zero_im, him, and_self_iff, zero_re]
    rw [zero_dvd_iff] at hdvd
    -- ⊢ False
    simp [hdvd, zero_im, zero_re, not_isCoprime_zero_zero] at hcoprime
    -- 🎉 no goals
  · rintro z hz - hzdvdu hzdvdv
    -- ⊢ False
    apply hz
    -- ⊢ IsUnit z
    obtain ⟨ha, hb⟩ : z ∣ a.re ∧ z ∣ a.im := by
      rw [← coe_int_dvd_iff]
      apply dvd_trans _ hdvd
      rw [coe_int_dvd_iff]
      exact ⟨hzdvdu, hzdvdv⟩
    exact hcoprime.isUnit_of_dvd' ha hb
    -- 🎉 no goals
#align zsqrtd.coprime_of_dvd_coprime Zsqrtd.coprime_of_dvd_coprime

theorem exists_coprime_of_gcd_pos {a : ℤ√d} (hgcd : 0 < Int.gcd a.re a.im) :
    ∃ b : ℤ√d, a = ((Int.gcd a.re a.im : ℤ) : ℤ√d) * b ∧ IsCoprime b.re b.im := by
  obtain ⟨re, im, H1, Hre, Him⟩ := Int.exists_gcd_one hgcd
  -- ⊢ ∃ b, a = ↑↑(Int.gcd a.re a.im) * b ∧ IsCoprime b.re b.im
  rw [mul_comm] at Hre Him
  -- ⊢ ∃ b, a = ↑↑(Int.gcd a.re a.im) * b ∧ IsCoprime b.re b.im
  refine' ⟨⟨re, im⟩, _, _⟩
  -- ⊢ a = ↑↑(Int.gcd a.re a.im) * { re := re, im := im }
  · rw [smul_val, ext, ← Hre, ← Him]
    -- ⊢ a.re = { re := a.re, im := a.im }.re ∧ a.im = { re := a.re, im := a.im }.im
    constructor <;> rfl
    -- ⊢ a.re = { re := a.re, im := a.im }.re
                    -- 🎉 no goals
                    -- 🎉 no goals
  · rw [← Int.gcd_eq_one_iff_coprime, H1]
    -- 🎉 no goals
#align zsqrtd.exists_coprime_of_gcd_pos Zsqrtd.exists_coprime_of_gcd_pos

end Gcd

/-- Read `SqLe a c b d` as `a √c ≤ b √d` -/
def SqLe (a c b d : ℕ) : Prop :=
  c * a * a ≤ d * b * b
#align zsqrtd.sq_le Zsqrtd.SqLe

theorem sqLe_of_le {c d x y z w : ℕ} (xz : z ≤ x) (yw : y ≤ w) (xy : SqLe x c y d) : SqLe z c w d :=
  le_trans (mul_le_mul (Nat.mul_le_mul_left _ xz) xz (Nat.zero_le _) (Nat.zero_le _)) <|
    le_trans xy (mul_le_mul (Nat.mul_le_mul_left _ yw) yw (Nat.zero_le _) (Nat.zero_le _))
#align zsqrtd.sq_le_of_le Zsqrtd.sqLe_of_le

theorem sqLe_add_mixed {c d x y z w : ℕ} (xy : SqLe x c y d) (zw : SqLe z c w d) :
    c * (x * z) ≤ d * (y * w) :=
  Nat.mul_self_le_mul_self_iff.2 <| by
    simpa [mul_comm, mul_left_comm] using mul_le_mul xy zw (Nat.zero_le _) (Nat.zero_le _)
    -- 🎉 no goals
#align zsqrtd.sq_le_add_mixed Zsqrtd.sqLe_add_mixed

theorem sqLe_add {c d x y z w : ℕ} (xy : SqLe x c y d) (zw : SqLe z c w d) :
    SqLe (x + z) c (y + w) d := by
  have xz := sqLe_add_mixed xy zw
  -- ⊢ SqLe (x + z) c (y + w) d
  simp [SqLe, mul_assoc] at xy zw
  -- ⊢ SqLe (x + z) c (y + w) d
  simp [SqLe, mul_add, mul_comm, mul_left_comm, add_le_add, *]
  -- 🎉 no goals
#align zsqrtd.sq_le_add Zsqrtd.sqLe_add

theorem sqLe_cancel {c d x y z w : ℕ} (zw : SqLe y d x c) (h : SqLe (x + z) c (y + w) d) :
    SqLe z c w d := by
  apply le_of_not_gt
  -- ⊢ ¬c * z * z > d * w * w
  intro l
  -- ⊢ False
  refine' not_le_of_gt _ h
  -- ⊢ c * (x + z) * (x + z) > d * (y + w) * (y + w)
  simp only [SqLe, mul_add, mul_comm, mul_left_comm, add_assoc, gt_iff_lt]
  -- ⊢ d * (y * y) + (d * (y * w) + (d * (y * w) + d * (w * w))) < c * (x * x) + (c …
  have hm := sqLe_add_mixed zw (le_of_lt l)
  -- ⊢ d * (y * y) + (d * (y * w) + (d * (y * w) + d * (w * w))) < c * (x * x) + (c …
  simp only [SqLe, mul_assoc, gt_iff_lt] at l zw
  -- ⊢ d * (y * y) + (d * (y * w) + (d * (y * w) + d * (w * w))) < c * (x * x) + (c …
  exact
    lt_of_le_of_lt (add_le_add_right zw _)
      (add_lt_add_left (add_lt_add_of_le_of_lt hm (add_lt_add_of_le_of_lt hm l)) _)
#align zsqrtd.sq_le_cancel Zsqrtd.sqLe_cancel

theorem sqLe_smul {c d x y : ℕ} (n : ℕ) (xy : SqLe x c y d) : SqLe (n * x) c (n * y) d := by
  simpa [SqLe, mul_left_comm, mul_assoc] using Nat.mul_le_mul_left (n * n) xy
  -- 🎉 no goals
#align zsqrtd.sq_le_smul Zsqrtd.sqLe_smul

theorem sqLe_mul {d x y z w : ℕ} :
    (SqLe x 1 y d → SqLe z 1 w d → SqLe (x * w + y * z) d (x * z + d * y * w) 1) ∧
      (SqLe x 1 y d → SqLe w d z 1 → SqLe (x * z + d * y * w) 1 (x * w + y * z) d) ∧
        (SqLe y d x 1 → SqLe z 1 w d → SqLe (x * z + d * y * w) 1 (x * w + y * z) d) ∧
          (SqLe y d x 1 → SqLe w d z 1 → SqLe (x * w + y * z) d (x * z + d * y * w) 1) := by
  refine' ⟨_, _, _, _⟩ <;>
    · intro xy zw
      -- ⊢ SqLe (x * w + y * z) d (x * z + d * y * w) 1
      -- ⊢ SqLe (x * z + d * y * w) 1 (x * w + y * z) d
      -- ⊢ SqLe (x * z + d * y * w) 1 (x * w + y * z) d
      -- ⊢ SqLe (x * w + y * z) d (x * z + d * y * w) 1
      have :=
      -- ⊢ 0 ≤ ↑(1 * (x * z + d * y * w) * (x * z + d * y * w)) - ↑(d * (x * w + y * z) …
        Int.mul_nonneg (sub_nonneg_of_le (Int.ofNat_le_ofNat_of_le xy))
      -- ⊢ ↑(1 * (x * z + d * y * w) * (x * z + d * y * w)) - ↑(d * (x * w + y * z) * ( …
      -- ⊢ 0 ≤ ↑(d * (x * w + y * z) * (x * w + y * z)) - ↑(1 * (x * z + d * y * w) * ( …
      -- ⊢ (↑x * ↑z + ↑d * ↑y * ↑w) * (↑x * ↑z + ↑d * ↑y * ↑w) - ↑d * (↑x * ↑w + ↑y * ↑ …
          (sub_nonneg_of_le (Int.ofNat_le_ofNat_of_le zw))
      -- 🎉 no goals
      -- ⊢ ↑(d * (x * w + y * z) * (x * w + y * z)) - ↑(1 * (x * z + d * y * w) * (x *  …
      -- ⊢ 0 ≤ ↑(d * (x * w + y * z) * (x * w + y * z)) - ↑(1 * (x * z + d * y * w) * ( …
      -- ⊢ ↑d * (↑x * ↑w + ↑y * ↑z) * (↑x * ↑w + ↑y * ↑z) - (↑x * ↑z + ↑d * ↑y * ↑w) *  …
      refine' Int.le_of_ofNat_le_ofNat (le_of_sub_nonneg _)
      -- 🎉 no goals
      -- ⊢ ↑(d * (x * w + y * z) * (x * w + y * z)) - ↑(1 * (x * z + d * y * w) * (x *  …
      -- ⊢ 0 ≤ ↑(1 * (x * z + d * y * w) * (x * z + d * y * w)) - ↑(d * (x * w + y * z) …
      -- ⊢ ↑d * (↑x * ↑w + ↑y * ↑z) * (↑x * ↑w + ↑y * ↑z) - (↑x * ↑z + ↑d * ↑y * ↑w) *  …
      convert this using 1
      -- 🎉 no goals
      -- ⊢ ↑(1 * (x * z + d * y * w) * (x * z + d * y * w)) - ↑(d * (x * w + y * z) * ( …
      simp only [one_mul, Int.ofNat_add, Int.ofNat_mul]
      -- ⊢ (↑x * ↑z + ↑d * ↑y * ↑w) * (↑x * ↑z + ↑d * ↑y * ↑w) - ↑d * (↑x * ↑w + ↑y * ↑ …
      ring
      -- 🎉 no goals
#align zsqrtd.sq_le_mul Zsqrtd.sqLe_mul

open Int in
/-- "Generalized" `nonneg`. `nonnegg c d x y` means `a √c + b √d ≥ 0`;
  we are interested in the case `c = 1` but this is more symmetric -/
def Nonnegg (c d : ℕ) : ℤ → ℤ → Prop
  | (a : ℕ), (b : ℕ) => True
  | (a : ℕ), -[b+1] => SqLe (b + 1) c a d
  | -[a+1], (b : ℕ) => SqLe (a + 1) d b c
  | -[_+1], -[_+1] => False
#align zsqrtd.nonnegg Zsqrtd.Nonnegg

theorem nonnegg_comm {c d : ℕ} {x y : ℤ} : Nonnegg c d x y = Nonnegg d c y x := by
  induction x <;> induction y <;> rfl
  -- ⊢ Nonnegg c d (Int.ofNat a✝) y = Nonnegg d c y (Int.ofNat a✝)
                  -- ⊢ Nonnegg c d (Int.ofNat a✝¹) (Int.ofNat a✝) = Nonnegg d c (Int.ofNat a✝) (Int …
                  -- ⊢ Nonnegg c d (Int.negSucc a✝¹) (Int.ofNat a✝) = Nonnegg d c (Int.ofNat a✝) (I …
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align zsqrtd.nonnegg_comm Zsqrtd.nonnegg_comm

theorem nonnegg_neg_pos {c d} : ∀ {a b : ℕ}, Nonnegg c d (-a) b ↔ SqLe a d b c
  | 0, b => ⟨by simp [SqLe, Nat.zero_le], fun _ => trivial⟩
                -- 🎉 no goals
  | a + 1, b => by rw [← Int.negSucc_coe]; rfl
                   -- ⊢ Nonnegg c d (Int.negSucc a) ↑b ↔ SqLe (a + 1) d b c
                                           -- 🎉 no goals
#align zsqrtd.nonnegg_neg_pos Zsqrtd.nonnegg_neg_pos

theorem nonnegg_pos_neg {c d} {a b : ℕ} : Nonnegg c d a (-b) ↔ SqLe b c a d := by
  rw [nonnegg_comm]; exact nonnegg_neg_pos
  -- ⊢ Nonnegg d c (-↑b) ↑a ↔ SqLe b c a d
                     -- 🎉 no goals
#align zsqrtd.nonnegg_pos_neg Zsqrtd.nonnegg_pos_neg

open Int in
theorem nonnegg_cases_right {c d} {a : ℕ} :
    ∀ {b : ℤ}, (∀ x : ℕ, b = -x → SqLe x c a d) → Nonnegg c d a b
  | (b : Nat), _ => trivial
  | -[b+1], h => h (b + 1) rfl
#align zsqrtd.nonnegg_cases_right Zsqrtd.nonnegg_cases_right

theorem nonnegg_cases_left {c d} {b : ℕ} {a : ℤ} (h : ∀ x : ℕ, a = -x → SqLe x d b c) :
    Nonnegg c d a b :=
  cast nonnegg_comm (nonnegg_cases_right h)
#align zsqrtd.nonnegg_cases_left Zsqrtd.nonnegg_cases_left

section Norm

/-- The norm of an element of `ℤ[√d]`. -/
def norm (n : ℤ√d) : ℤ :=
  n.re * n.re - d * n.im * n.im
#align zsqrtd.norm Zsqrtd.norm

theorem norm_def (n : ℤ√d) : n.norm = n.re * n.re - d * n.im * n.im :=
  rfl
#align zsqrtd.norm_def Zsqrtd.norm_def

@[simp]
theorem norm_zero : norm (0 : ℤ√d) = 0 := by simp [norm]
                                             -- 🎉 no goals
#align zsqrtd.norm_zero Zsqrtd.norm_zero

@[simp]
theorem norm_one : norm (1 : ℤ√d) = 1 := by simp [norm]
                                            -- 🎉 no goals
#align zsqrtd.norm_one Zsqrtd.norm_one

@[simp]
theorem norm_int_cast (n : ℤ) : norm (n : ℤ√d) = n * n := by simp [norm]
                                                             -- 🎉 no goals
#align zsqrtd.norm_int_cast Zsqrtd.norm_int_cast

@[simp]
theorem norm_nat_cast (n : ℕ) : norm (n : ℤ√d) = n * n :=
  norm_int_cast n
#align zsqrtd.norm_nat_cast Zsqrtd.norm_nat_cast

@[simp]
theorem norm_mul (n m : ℤ√d) : norm (n * m) = norm n * norm m := by
  simp only [norm, mul_im, mul_re]
  -- ⊢ (n.re * m.re + d * n.im * m.im) * (n.re * m.re + d * n.im * m.im) - d * (n.r …
  ring
  -- 🎉 no goals
#align zsqrtd.norm_mul Zsqrtd.norm_mul

/-- `norm` as a `MonoidHom`. -/
def normMonoidHom : ℤ√d →* ℤ where
  toFun := norm
  map_mul' := norm_mul
  map_one' := norm_one
#align zsqrtd.norm_monoid_hom Zsqrtd.normMonoidHom

theorem norm_eq_mul_conj (n : ℤ√d) : (norm n : ℤ√d) = n * star n := by
  cases n
  -- ⊢ ↑(norm { re := re✝, im := im✝ }) = { re := re✝, im := im✝ } * star { re := r …
  simp [norm, star, Zsqrtd.ext, mul_comm, sub_eq_add_neg]
  -- 🎉 no goals
#align zsqrtd.norm_eq_mul_conj Zsqrtd.norm_eq_mul_conj

@[simp]
theorem norm_neg (x : ℤ√d) : (-x).norm = x.norm :=
  -- Porting note: replaced `simp` with `rw`
  -- See https://github.com/leanprover-community/mathlib4/issues/5026
  Zsqrtd.coe_int_inj <| by rw [norm_eq_mul_conj, star_neg, neg_mul_neg, norm_eq_mul_conj]
                           -- 🎉 no goals
#align zsqrtd.norm_neg Zsqrtd.norm_neg

@[simp]
theorem norm_conj (x : ℤ√d) : (star x).norm = x.norm :=
  -- Porting note: replaced `simp` with `rw`
  -- See https://github.com/leanprover-community/mathlib4/issues/5026
  Zsqrtd.coe_int_inj <| by rw [norm_eq_mul_conj, star_star, mul_comm, norm_eq_mul_conj]
                           -- 🎉 no goals
#align zsqrtd.norm_conj Zsqrtd.norm_conj

theorem norm_nonneg (hd : d ≤ 0) (n : ℤ√d) : 0 ≤ n.norm :=
  add_nonneg (mul_self_nonneg _)
    (by
      rw [mul_assoc, neg_mul_eq_neg_mul]
      -- ⊢ 0 ≤ -d * (n.im * n.im)
      exact mul_nonneg (neg_nonneg.2 hd) (mul_self_nonneg _))
      -- 🎉 no goals
#align zsqrtd.norm_nonneg Zsqrtd.norm_nonneg

theorem norm_eq_one_iff {x : ℤ√d} : x.norm.natAbs = 1 ↔ IsUnit x :=
  ⟨fun h =>
    isUnit_iff_dvd_one.2 <|
      (le_total 0 (norm x)).casesOn
        (fun hx =>
          ⟨star x, by
            rwa [← Int.coe_nat_inj', Int.natAbs_of_nonneg hx, ← @Int.cast_inj (ℤ√d) _ _,
              norm_eq_mul_conj, eq_comm] at h⟩)
        fun hx =>
          ⟨-star x, by
            rwa [← Int.coe_nat_inj', Int.ofNat_natAbs_of_nonpos hx, ← @Int.cast_inj (ℤ√d) _ _,
              Int.cast_neg, norm_eq_mul_conj, neg_mul_eq_mul_neg, eq_comm] at h⟩,
    fun h => by
    let ⟨y, hy⟩ := isUnit_iff_dvd_one.1 h
    -- ⊢ Int.natAbs (norm x) = 1
    have := congr_arg (Int.natAbs ∘ norm) hy
    -- ⊢ Int.natAbs (norm x) = 1
    rw [Function.comp_apply, Function.comp_apply, norm_mul, Int.natAbs_mul, norm_one,
      Int.natAbs_one, eq_comm, mul_eq_one] at this
    exact this.1⟩
    -- 🎉 no goals
#align zsqrtd.norm_eq_one_iff Zsqrtd.norm_eq_one_iff

theorem isUnit_iff_norm_isUnit {d : ℤ} (z : ℤ√d) : IsUnit z ↔ IsUnit z.norm := by
  rw [Int.isUnit_iff_natAbs_eq, norm_eq_one_iff]
  -- 🎉 no goals
#align zsqrtd.is_unit_iff_norm_is_unit Zsqrtd.isUnit_iff_norm_isUnit

theorem norm_eq_one_iff' {d : ℤ} (hd : d ≤ 0) (z : ℤ√d) : z.norm = 1 ↔ IsUnit z := by
  rw [← norm_eq_one_iff, ← Int.coe_nat_inj', Int.natAbs_of_nonneg (norm_nonneg hd z), Int.ofNat_one]
  -- 🎉 no goals
#align zsqrtd.norm_eq_one_iff' Zsqrtd.norm_eq_one_iff'

theorem norm_eq_zero_iff {d : ℤ} (hd : d < 0) (z : ℤ√d) : z.norm = 0 ↔ z = 0 := by
  constructor
  -- ⊢ norm z = 0 → z = 0
  · intro h
    -- ⊢ z = 0
    rw [ext, zero_re, zero_im]
    -- ⊢ z.re = 0 ∧ z.im = 0
    rw [norm_def, sub_eq_add_neg, mul_assoc] at h
    -- ⊢ z.re = 0 ∧ z.im = 0
    have left := mul_self_nonneg z.re
    -- ⊢ z.re = 0 ∧ z.im = 0
    have right := neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hd.le (mul_self_nonneg z.im))
    -- ⊢ z.re = 0 ∧ z.im = 0
    obtain ⟨ha, hb⟩ := (add_eq_zero_iff' left right).mp h
    -- ⊢ z.re = 0 ∧ z.im = 0
    constructor <;> apply eq_zero_of_mul_self_eq_zero
    -- ⊢ z.re = 0
                    -- ⊢ z.re * z.re = 0
                    -- ⊢ z.im * z.im = 0
    · exact ha
      -- 🎉 no goals
    · rw [neg_eq_zero, mul_eq_zero] at hb
      -- ⊢ z.im * z.im = 0
      exact hb.resolve_left hd.ne
      -- 🎉 no goals
  · rintro rfl
    -- ⊢ norm 0 = 0
    exact norm_zero
    -- 🎉 no goals
#align zsqrtd.norm_eq_zero_iff Zsqrtd.norm_eq_zero_iff

theorem norm_eq_of_associated {d : ℤ} (hd : d ≤ 0) {x y : ℤ√d} (h : Associated x y) :
    x.norm = y.norm := by
  obtain ⟨u, rfl⟩ := h
  -- ⊢ norm x = norm (x * ↑u)
  rw [norm_mul, (norm_eq_one_iff' hd _).mpr u.isUnit, mul_one]
  -- 🎉 no goals
#align zsqrtd.norm_eq_of_associated Zsqrtd.norm_eq_of_associated

end Norm

end

section

variable {d : ℕ}

/-- Nonnegativity of an element of `ℤ√d`. -/
def Nonneg : ℤ√d → Prop
  | ⟨a, b⟩ => Nonnegg d 1 a b
#align zsqrtd.nonneg Zsqrtd.Nonneg

instance : LE (ℤ√d) :=
  ⟨fun a b => Nonneg (b - a)⟩

instance : LT (ℤ√d) :=
  ⟨fun a b => ¬b ≤ a⟩

instance decidableNonnegg (c d a b) : Decidable (Nonnegg c d a b) := by
  cases a <;> cases b <;> unfold Nonnegg SqLe <;> infer_instance
  -- ⊢ Decidable (Nonnegg c d (Int.ofNat a✝) b)
              -- ⊢ Decidable (Nonnegg c d (Int.ofNat a✝¹) (Int.ofNat a✝))
              -- ⊢ Decidable (Nonnegg c d (Int.negSucc a✝¹) (Int.ofNat a✝))
                          -- ⊢ Decidable
                          -- ⊢ Decidable
                          -- ⊢ Decidable
                          -- ⊢ Decidable
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align zsqrtd.decidable_nonnegg Zsqrtd.decidableNonnegg

instance decidableNonneg : ∀ a : ℤ√d, Decidable (Nonneg a)
  | ⟨_, _⟩ => Zsqrtd.decidableNonnegg _ _ _ _
#align zsqrtd.decidable_nonneg Zsqrtd.decidableNonneg

instance decidableLE : @DecidableRel (ℤ√d) (· ≤ ·) := fun _ _ => decidableNonneg _
#align zsqrtd.decidable_le Zsqrtd.decidableLE

open Int in
theorem nonneg_cases : ∀ {a : ℤ√d}, Nonneg a → ∃ x y : ℕ, a = ⟨x, y⟩ ∨ a = ⟨x, -y⟩ ∨ a = ⟨-x, y⟩
  | ⟨(x : ℕ), (y : ℕ)⟩, _ => ⟨x, y, Or.inl rfl⟩
  | ⟨(x : ℕ), -[y+1]⟩, _ => ⟨x, y + 1, Or.inr <| Or.inl rfl⟩
  | ⟨-[x+1], (y : ℕ)⟩, _ => ⟨x + 1, y, Or.inr <| Or.inr rfl⟩
  | ⟨-[_+1], -[_+1]⟩, h => False.elim h
#align zsqrtd.nonneg_cases Zsqrtd.nonneg_cases

open Int in
theorem nonneg_add_lem {x y z w : ℕ} (xy : Nonneg (⟨x, -y⟩ : ℤ√d)) (zw : Nonneg (⟨-z, w⟩ : ℤ√d)) :
    Nonneg (⟨x, -y⟩ + ⟨-z, w⟩ : ℤ√d) := by
  have : Nonneg ⟨Int.subNatNat x z, Int.subNatNat w y⟩ :=
    Int.subNatNat_elim x z
      (fun m n i => SqLe y d m 1 → SqLe n 1 w d → Nonneg ⟨i, Int.subNatNat w y⟩)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d (k + j) 1 → SqLe k 1 m d → Nonneg ⟨Int.ofNat j, i⟩)
          (fun _ _ _ _ => trivial) fun m n xy zw => sqLe_cancel zw xy)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d k 1 → SqLe (k + j + 1) 1 m d → Nonneg ⟨-[j+1], i⟩)
          (fun m n xy zw => sqLe_cancel xy zw) fun m n xy zw =>
          let t := Nat.le_trans zw (sqLe_of_le (Nat.le_add_right n (m + 1)) le_rfl xy)
          have : k + j + 1 ≤ k :=
            Nat.mul_self_le_mul_self_iff.2 (by simpa [one_mul] using t)
          absurd this (not_le_of_gt <| Nat.succ_le_succ <| Nat.le_add_right _ _))
      (nonnegg_pos_neg.1 xy) (nonnegg_neg_pos.1 zw)
  rw [add_def, neg_add_eq_sub]
  -- ⊢ Nonneg { re := ↑x + -↑z, im := ↑w - ↑y }
  rwa [Int.subNatNat_eq_coe, Int.subNatNat_eq_coe] at this
  -- 🎉 no goals
#align zsqrtd.nonneg_add_lem Zsqrtd.nonneg_add_lem

theorem Nonneg.add {a b : ℤ√d} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (a + b) := by
  rcases nonneg_cases ha with ⟨x, y, rfl | rfl | rfl⟩ <;>
    rcases nonneg_cases hb with ⟨z, w, rfl | rfl | rfl⟩
  · trivial
    -- 🎉 no goals
  · refine' nonnegg_cases_right fun i h => sqLe_of_le _ _ (nonnegg_pos_neg.1 hb)
    -- ⊢ i ≤ w
    · dsimp only at h
      -- ⊢ i ≤ w
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro y (by simp [add_comm, *])))
      -- 🎉 no goals
    · apply Nat.le_add_left
      -- 🎉 no goals
  · refine' nonnegg_cases_left fun i h => sqLe_of_le _ _ (nonnegg_neg_pos.1 hb)
    -- ⊢ i ≤ z
    · dsimp only at h
      -- ⊢ i ≤ z
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro x (by simp [add_comm, *])))
      -- 🎉 no goals
    · apply Nat.le_add_left
      -- 🎉 no goals
  · refine' nonnegg_cases_right fun i h => sqLe_of_le _ _ (nonnegg_pos_neg.1 ha)
    -- ⊢ i ≤ y
    · dsimp only at h
      -- ⊢ i ≤ y
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro w (by simp [*])))
      -- 🎉 no goals
    · apply Nat.le_add_right
      -- 🎉 no goals
  · have : Nonneg ⟨_, _⟩ :=
      nonnegg_pos_neg.2 (sqLe_add (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
    rw [Nat.cast_add, Nat.cast_add, neg_add] at this
    -- ⊢ Nonneg ({ re := ↑x, im := -↑y } + { re := ↑z, im := -↑w })
    rwa [add_def]
    -- 🎉 no goals
    -- Porting note: was
    -- simpa [add_comm] using
    --   nonnegg_pos_neg.2 (sqLe_add (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
  · exact nonneg_add_lem ha hb
    -- 🎉 no goals
  · refine' nonnegg_cases_left fun i h => sqLe_of_le _ _ (nonnegg_neg_pos.1 ha)
    -- ⊢ i ≤ x
    · dsimp only at h
      -- ⊢ i ≤ x
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro _ h))
      -- 🎉 no goals
    · apply Nat.le_add_right
      -- 🎉 no goals
  · dsimp
    -- ⊢ Nonneg { re := -↑x + ↑z, im := ↑y + -↑w }
    rw [add_comm, add_comm (y : ℤ)]
    -- ⊢ Nonneg { re := ↑z + -↑x, im := -↑w + ↑y }
    exact nonneg_add_lem hb ha
    -- 🎉 no goals
  · have : Nonneg ⟨_, _⟩ :=
      nonnegg_neg_pos.2 (sqLe_add (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
    rw [Nat.cast_add, Nat.cast_add, neg_add] at this
    -- ⊢ Nonneg ({ re := -↑x, im := ↑y } + { re := -↑z, im := ↑w })
    rwa [add_def]
    -- 🎉 no goals
    -- Porting note: was
    -- simpa [add_comm] using
    --   nonnegg_neg_pos.2 (sqLe_add (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
#align zsqrtd.nonneg.add Zsqrtd.Nonneg.add

theorem nonneg_iff_zero_le {a : ℤ√d} : Nonneg a ↔ 0 ≤ a :=
  show _ ↔ Nonneg _ by simp
                       -- 🎉 no goals
#align zsqrtd.nonneg_iff_zero_le Zsqrtd.nonneg_iff_zero_le

theorem le_of_le_le {x y z w : ℤ} (xz : x ≤ z) (yw : y ≤ w) : (⟨x, y⟩ : ℤ√d) ≤ ⟨z, w⟩ :=
  show Nonneg ⟨z - x, w - y⟩ from
    match z - x, w - y, Int.le.dest_sub xz, Int.le.dest_sub yw with
    | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => trivial
#align zsqrtd.le_of_le_le Zsqrtd.le_of_le_le

open Int in
protected theorem nonneg_total : ∀ a : ℤ√d, Nonneg a ∨ Nonneg (-a)
  | ⟨(x : ℕ), (y : ℕ)⟩ => Or.inl trivial
  | ⟨-[_+1], -[_+1]⟩ => Or.inr trivial
  | ⟨0, -[_+1]⟩ => Or.inr trivial
  | ⟨-[_+1], 0⟩ => Or.inr trivial
  | ⟨(_ + 1 : ℕ), -[_+1]⟩ => Nat.le_total _ _
  | ⟨-[_+1], (_ + 1 : ℕ)⟩ => Nat.le_total _ _
#align zsqrtd.nonneg_total Zsqrtd.nonneg_total

protected theorem le_total (a b : ℤ√d) : a ≤ b ∨ b ≤ a := by
  have t := (b - a).nonneg_total
  -- ⊢ a ≤ b ∨ b ≤ a
  rwa [neg_sub] at t
  -- 🎉 no goals
#align zsqrtd.le_total Zsqrtd.le_total

instance preorder : Preorder (ℤ√d) where
  le := (· ≤ ·)
  le_refl a := show Nonneg (a - a) by simp only [sub_self]; trivial
                                      -- ⊢ Nonneg 0
                                                            -- 🎉 no goals
  le_trans a b c hab hbc := by simpa [sub_add_sub_cancel'] using hab.add hbc
                               -- 🎉 no goals
  lt := (· < ·)
  lt_iff_le_not_le a b := (and_iff_right_of_imp (Zsqrtd.le_total _ _).resolve_left).symm

open Int in
theorem le_arch (a : ℤ√d) : ∃ n : ℕ, a ≤ n := by
  obtain ⟨x, y, (h : a ≤ ⟨x, y⟩)⟩ : ∃ x y : ℕ, Nonneg (⟨x, y⟩ + -a) :=
    match -a with
    | ⟨Int.ofNat x, Int.ofNat y⟩ => ⟨0, 0, by trivial⟩
    | ⟨Int.ofNat x, -[y+1]⟩ => ⟨0, y + 1, by simp [add_def, Int.negSucc_coe, add_assoc]; trivial⟩
    | ⟨-[x+1], Int.ofNat y⟩ => ⟨x + 1, 0, by simp [Int.negSucc_coe, add_assoc]; trivial⟩
    | ⟨-[x+1], -[y+1]⟩ => ⟨x + 1, y + 1, by simp [Int.negSucc_coe, add_assoc]; trivial⟩
  refine' ⟨x + d * y, h.trans _⟩
  -- ⊢ { re := ↑x, im := ↑y } ≤ ↑(x + d * y)
  change Nonneg ⟨↑x + d * y - ↑x, 0 - ↑y⟩
  -- ⊢ Nonneg { re := ↑x + ↑d * ↑y - ↑x, im := 0 - ↑y }
  cases' y with y
  -- ⊢ Nonneg { re := ↑x + ↑d * ↑Nat.zero - ↑x, im := 0 - ↑Nat.zero }
  · simp
    -- ⊢ Nonneg { re := 0, im := 0 }
    trivial
    -- 🎉 no goals
  have h : ∀ y, SqLe y d (d * y) 1 := fun y => by
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_right (y * y) (Nat.le_mul_self d)
  rw [show (x : ℤ) + d * Nat.succ y - x = d * Nat.succ y by simp]
  -- ⊢ Nonneg { re := ↑d * ↑(Nat.succ y), im := 0 - ↑(Nat.succ y) }
  exact h (y + 1)
  -- 🎉 no goals
#align zsqrtd.le_arch Zsqrtd.le_arch

protected theorem add_le_add_left (a b : ℤ√d) (ab : a ≤ b) (c : ℤ√d) : c + a ≤ c + b :=
  show Nonneg _ by rw [add_sub_add_left_eq_sub]; exact ab
                   -- ⊢ Nonneg (b - a)
                                                 -- 🎉 no goals
#align zsqrtd.add_le_add_left Zsqrtd.add_le_add_left

protected theorem le_of_add_le_add_left (a b c : ℤ√d) (h : c + a ≤ c + b) : a ≤ b := by
  simpa using Zsqrtd.add_le_add_left _ _ h (-c)
  -- 🎉 no goals
#align zsqrtd.le_of_add_le_add_left Zsqrtd.le_of_add_le_add_left

protected theorem add_lt_add_left (a b : ℤ√d) (h : a < b) (c) : c + a < c + b := fun h' =>
  h (Zsqrtd.le_of_add_le_add_left _ _ _ h')
#align zsqrtd.add_lt_add_left Zsqrtd.add_lt_add_left

theorem nonneg_smul {a : ℤ√d} {n : ℕ} (ha : Nonneg a) : Nonneg ((n : ℤ√d) * a) := by
  rw [← Int.cast_ofNat n]
  -- ⊢ Nonneg (↑↑n * a)
  exact
    match a, nonneg_cases ha, ha with
    | _, ⟨x, y, Or.inl rfl⟩, _ => by rw [smul_val]; trivial
    | _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ha => by
      rw [smul_val]; simpa using nonnegg_pos_neg.2 (sqLe_smul n <| nonnegg_pos_neg.1 ha)
    | _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ha => by
      rw [smul_val]; simpa using nonnegg_neg_pos.2 (sqLe_smul n <| nonnegg_neg_pos.1 ha)
#align zsqrtd.nonneg_smul Zsqrtd.nonneg_smul

theorem nonneg_muld {a : ℤ√d} (ha : Nonneg a) : Nonneg (sqrtd * a) :=
  match a, nonneg_cases ha, ha with
  | _, ⟨_, _, Or.inl rfl⟩, _ => trivial
  | _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ha => by
    simp only [muld_val, mul_neg]
    -- ⊢ Nonneg { re := -(↑d * ↑y), im := ↑x }
    apply nonnegg_neg_pos.2
    -- ⊢ SqLe (d * y) 1 x d
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_pos_neg.1 ha)
    -- 🎉 no goals
  | _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ha => by
    simp only [muld_val]
    -- ⊢ Nonneg { re := ↑d * ↑y, im := -↑x }
    apply nonnegg_pos_neg.2
    -- ⊢ SqLe x d (d * y) 1
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_neg_pos.1 ha)
    -- 🎉 no goals
#align zsqrtd.nonneg_muld Zsqrtd.nonneg_muld

theorem nonneg_mul_lem {x y : ℕ} {a : ℤ√d} (ha : Nonneg a) : Nonneg (⟨x, y⟩ * a) := by
  have : (⟨x, y⟩ * a : ℤ√d) = (x : ℤ√d) * a + sqrtd * ((y : ℤ√d) * a) := by
    rw [decompose, right_distrib, mul_assoc, Int.cast_ofNat, Int.cast_ofNat]
  rw [this]
  -- ⊢ Nonneg (↑x * a + sqrtd * (↑y * a))
  exact (nonneg_smul ha).add (nonneg_muld <| nonneg_smul ha)
  -- 🎉 no goals
#align zsqrtd.nonneg_mul_lem Zsqrtd.nonneg_mul_lem

theorem nonneg_mul {a b : ℤ√d} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (a * b) :=
  match a, b, nonneg_cases ha, nonneg_cases hb, ha, hb with
  | _, _, ⟨_, _, Or.inl rfl⟩, ⟨_, _, Or.inl rfl⟩, _, _ => trivial
  | _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inr rfl⟩, _, hb => nonneg_mul_lem hb
  | _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inl rfl⟩, _, hb => nonneg_mul_lem hb
  | _, _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, _ => by
    rw [mul_comm]; exact nonneg_mul_lem ha
    -- ⊢ Nonneg ({ re := ↑z, im := ↑w } * { re := -↑x, im := ↑y })
                   -- 🎉 no goals
  | _, _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, _ => by
    rw [mul_comm]; exact nonneg_mul_lem ha
    -- ⊢ Nonneg ({ re := ↑z, im := ↑w } * { re := ↑x, im := -↑y })
                   -- 🎉 no goals
  | _, _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ⟨z, w, Or.inr <| Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨-x, y⟩ * ⟨-z, w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨x * z + d * y * w, -(x * w + y * z)⟩ := by simp [add_comm]
          ]
    exact nonnegg_pos_neg.2 (sqLe_mul.left (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
    -- 🎉 no goals
  | _, _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ⟨z, w, Or.inr <| Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨-x, y⟩ * ⟨z, -w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨-(x * z + d * y * w), x * w + y * z⟩ := by simp [add_comm]
          ]
    exact nonnegg_neg_pos.2 (sqLe_mul.right.left (nonnegg_neg_pos.1 ha) (nonnegg_pos_neg.1 hb))
    -- 🎉 no goals
  | _, _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨x, -y⟩ * ⟨-z, w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨-(x * z + d * y * w), x * w + y * z⟩ := by simp [add_comm]
          ]
    exact
        nonnegg_neg_pos.2 (sqLe_mul.right.right.left (nonnegg_pos_neg.1 ha) (nonnegg_neg_pos.1 hb))
  | _, _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨x, -y⟩ * ⟨z, -w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨x * z + d * y * w, -(x * w + y * z)⟩ := by simp [add_comm]
          ]
    exact
        nonnegg_pos_neg.2
          (sqLe_mul.right.right.right (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
#align zsqrtd.nonneg_mul Zsqrtd.nonneg_mul

protected theorem mul_nonneg (a b : ℤ√d) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by
  simp_rw [← nonneg_iff_zero_le]
  -- ⊢ Nonneg a → Nonneg b → Nonneg (a * b)
  exact nonneg_mul
  -- 🎉 no goals
#align zsqrtd.mul_nonneg Zsqrtd.mul_nonneg

theorem not_sqLe_succ (c d y) (h : 0 < c) : ¬SqLe (y + 1) c 0 d :=
  not_le_of_gt <| mul_pos (mul_pos h <| Nat.succ_pos _) <| Nat.succ_pos _
#align zsqrtd.not_sq_le_succ Zsqrtd.not_sqLe_succ

-- Porting note: renamed field and added theorem to make `x` explicit
/-- A nonsquare is a natural number that is not equal to the square of an
  integer. This is implemented as a typeclass because it's a necessary condition
  for much of the Pell equation theory. -/
class Nonsquare (x : ℕ) : Prop where
  ns' : ∀ n : ℕ, x ≠ n * n
#align zsqrtd.nonsquare Zsqrtd.Nonsquare

theorem Nonsquare.ns (x : ℕ) [Nonsquare x] : ∀ n : ℕ, x ≠ n * n := ns'

variable [dnsq : Nonsquare d]

theorem d_pos : 0 < d :=
  lt_of_le_of_ne (Nat.zero_le _) <| Ne.symm <| Nonsquare.ns d 0
#align zsqrtd.d_pos Zsqrtd.d_pos

theorem divides_sq_eq_zero {x y} (h : x * x = d * y * y) : x = 0 ∧ y = 0 :=
  let g := x.gcd y
  Or.elim g.eq_zero_or_pos
    (fun H => ⟨Nat.eq_zero_of_gcd_eq_zero_left H, Nat.eq_zero_of_gcd_eq_zero_right H⟩) fun gpos =>
    False.elim <| by
      let ⟨m, n, co, (hx : x = m * g), (hy : y = n * g)⟩ := Nat.exists_coprime gpos
      -- ⊢ False
      rw [hx, hy] at h
      -- ⊢ False
      have : m * m = d * (n * n) := by
        refine mul_left_cancel₀ (mul_pos gpos gpos).ne' ?_
        -- Porting note: was `simpa [mul_comm, mul_left_comm] using h`
        calc
          g * g * (m * m)
          _ = m * g * (m * g) := by ring
          _ = d * (n * g) * (n * g) := h
          _ = g * g * (d * (n * n)) := by ring
      have co2 :=
        let co1 := co.mul_right co
        co1.mul co1
      exact
        Nonsquare.ns d m
          (Nat.dvd_antisymm (by rw [this]; apply dvd_mul_right) <|
            co2.dvd_of_dvd_mul_right <| by simp [this])
#align zsqrtd.divides_sq_eq_zero Zsqrtd.divides_sq_eq_zero

theorem divides_sq_eq_zero_z {x y : ℤ} (h : x * x = d * y * y) : x = 0 ∧ y = 0 := by
  rw [mul_assoc, ← Int.natAbs_mul_self, ← Int.natAbs_mul_self, ← Int.ofNat_mul, ← mul_assoc] at h
  -- ⊢ x = 0 ∧ y = 0
  exact
    let ⟨h1, h2⟩ := divides_sq_eq_zero (Int.ofNat.inj h)
    ⟨Int.natAbs_eq_zero.mp h1, Int.natAbs_eq_zero.mp h2⟩
#align zsqrtd.divides_sq_eq_zero_z Zsqrtd.divides_sq_eq_zero_z

theorem not_divides_sq (x y) : (x + 1) * (x + 1) ≠ d * (y + 1) * (y + 1) := fun e => by
  have t := (divides_sq_eq_zero e).left
  -- ⊢ False
  contradiction
  -- 🎉 no goals
#align zsqrtd.not_divides_sq Zsqrtd.not_divides_sq

open Int in
theorem nonneg_antisymm : ∀ {a : ℤ√d}, Nonneg a → Nonneg (-a) → a = 0
  | ⟨0, 0⟩, _, _ => rfl
  | ⟨-[x+1], -[y+1]⟩, xy, _ => False.elim xy
  | ⟨(x + 1 : Nat), (y + 1 : Nat)⟩, _, yx => False.elim yx
  | ⟨-[x+1], 0⟩, xy, _ => absurd xy (not_sqLe_succ _ _ _ (by decide))
                                                             -- 🎉 no goals
  | ⟨(x + 1 : Nat), 0⟩, _, yx => absurd yx (not_sqLe_succ _ _ _ (by decide))
                                                                    -- 🎉 no goals
  | ⟨0, -[y+1]⟩, xy, _ => absurd xy (not_sqLe_succ _ _ _ d_pos)
  | ⟨0, (y + 1 : Nat)⟩, _, yx => absurd yx (not_sqLe_succ _ _ _ d_pos)
  | ⟨(x + 1 : Nat), -[y+1]⟩, (xy : SqLe _ _ _ _), (yx : SqLe _ _ _ _) => by
    let t := le_antisymm yx xy
    -- ⊢ { re := ↑(x + 1), im := -[y+1] } = 0
    rw [one_mul] at t
    -- ⊢ { re := ↑(x + 1), im := -[y+1] } = 0
    exact absurd t (not_divides_sq _ _)
    -- 🎉 no goals
  | ⟨-[x+1], (y + 1 : Nat)⟩, (xy : SqLe _ _ _ _), (yx : SqLe _ _ _ _) => by
    let t := le_antisymm xy yx
    -- ⊢ { re := -[x+1], im := ↑(y + 1) } = 0
    rw [one_mul] at t
    -- ⊢ { re := -[x+1], im := ↑(y + 1) } = 0
    exact absurd t (not_divides_sq _ _)
    -- 🎉 no goals
#align zsqrtd.nonneg_antisymm Zsqrtd.nonneg_antisymm

theorem le_antisymm {a b : ℤ√d} (ab : a ≤ b) (ba : b ≤ a) : a = b :=
  eq_of_sub_eq_zero <| nonneg_antisymm ba (by rwa [neg_sub])
                                              -- 🎉 no goals
#align zsqrtd.le_antisymm Zsqrtd.le_antisymm

instance linearOrder : LinearOrder (ℤ√d) :=
  { Zsqrtd.preorder with
    le_antisymm := fun _ _ => Zsqrtd.le_antisymm
    le_total := Zsqrtd.le_total
    decidableLE := Zsqrtd.decidableLE }

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : ℤ√d}, a * b = 0 → a = 0 ∨ b = 0
  | ⟨x, y⟩, ⟨z, w⟩, h => by
    injection h with h1 h2
    -- ⊢ { re := x, im := y } = 0 ∨ { re := z, im := w } = 0
    have h1 : x * z = -(d * y * w) := eq_neg_of_add_eq_zero_left h1
    -- ⊢ { re := x, im := y } = 0 ∨ { re := z, im := w } = 0
    have h2 : x * w = -(y * z) := eq_neg_of_add_eq_zero_left h2
    -- ⊢ { re := x, im := y } = 0 ∨ { re := z, im := w } = 0
    have fin : x * x = d * y * y → (⟨x, y⟩ : ℤ√d) = 0 := fun e =>
      match x, y, divides_sq_eq_zero_z e with
      | _, _, ⟨rfl, rfl⟩ => rfl
    exact
      if z0 : z = 0 then
        if w0 : w = 0 then
          Or.inr
            (match z, w, z0, w0 with
            | _, _, rfl, rfl => rfl)
        else
          Or.inl <|
            fin <|
              mul_right_cancel₀ w0 <|
                calc
                  x * x * w = -y * (x * z) := by simp [h2, mul_assoc, mul_left_comm]
                  _ = d * y * y * w := by simp [h1, mul_assoc, mul_left_comm]
      else
        Or.inl <|
          fin <|
            mul_right_cancel₀ z0 <|
              calc
                x * x * z = d * -y * (x * w) := by simp [h1, mul_assoc, mul_left_comm]
                _ = d * y * y * z := by simp [h2, mul_assoc, mul_left_comm]
#align zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero

instance : NoZeroDivisors (ℤ√d) where
  eq_zero_or_eq_zero_of_mul_eq_zero := Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero

instance : IsDomain (ℤ√d) :=
  NoZeroDivisors.to_isDomain _

protected theorem mul_pos (a b : ℤ√d) (a0 : 0 < a) (b0 : 0 < b) : 0 < a * b := fun ab =>
  Or.elim
    (eq_zero_or_eq_zero_of_mul_eq_zero
      (le_antisymm ab (Zsqrtd.mul_nonneg _ _ (le_of_lt a0) (le_of_lt b0))))
    (fun e => ne_of_gt a0 e) fun e => ne_of_gt b0 e
#align zsqrtd.mul_pos Zsqrtd.mul_pos

instance : LinearOrderedCommRing (ℤ√d) :=
  { Zsqrtd.commRing, Zsqrtd.linearOrder, Zsqrtd.nontrivial with
    add_le_add_left := Zsqrtd.add_le_add_left
    mul_pos := Zsqrtd.mul_pos
    zero_le_one := by trivial }
                      -- 🎉 no goals

instance : LinearOrderedRing (ℤ√d) := by infer_instance
                                         -- 🎉 no goals

instance : OrderedRing (ℤ√d) := by infer_instance
                                   -- 🎉 no goals

end

theorem norm_eq_zero {d : ℤ} (h_nonsquare : ∀ n : ℤ, d ≠ n * n) (a : ℤ√d) : norm a = 0 ↔ a = 0 := by
  refine' ⟨fun ha => ext.mpr _, fun h => by rw [h, norm_zero]⟩
  -- ⊢ a.re = 0.re ∧ a.im = 0.im
  dsimp only [norm] at ha
  -- ⊢ a.re = 0.re ∧ a.im = 0.im
  rw [sub_eq_zero] at ha
  -- ⊢ a.re = 0.re ∧ a.im = 0.im
  by_cases h : 0 ≤ d
  -- ⊢ a.re = 0.re ∧ a.im = 0.im
  · obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le h
    -- ⊢ a.re = 0.re ∧ a.im = 0.im
    haveI : Nonsquare d' := ⟨fun n h => h_nonsquare n <| by exact_mod_cast h⟩
    -- ⊢ a.re = 0.re ∧ a.im = 0.im
    exact divides_sq_eq_zero_z ha
    -- 🎉 no goals
  · push_neg at h
    -- ⊢ a.re = 0.re ∧ a.im = 0.im
    suffices a.re * a.re = 0 by
      rw [eq_zero_of_mul_self_eq_zero this] at ha ⊢
      simpa only [true_and_iff, or_self_right, zero_re, zero_im, eq_self_iff_true, zero_eq_mul,
        mul_zero, mul_eq_zero, h.ne, false_or_iff, or_self_iff] using ha
    apply _root_.le_antisymm _ (mul_self_nonneg _)
    -- ⊢ a.re * a.re ≤ 0
    rw [ha, mul_assoc]
    -- ⊢ d * (a.im * a.im) ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg h.le (mul_self_nonneg _)
    -- 🎉 no goals
#align zsqrtd.norm_eq_zero Zsqrtd.norm_eq_zero

variable {R : Type}

@[ext]
theorem hom_ext [Ring R] {d : ℤ} (f g : ℤ√d →+* R) (h : f sqrtd = g sqrtd) : f = g := by
  ext ⟨x_re, x_im⟩
  -- ⊢ ↑f { re := x_re, im := x_im } = ↑g { re := x_re, im := x_im }
  simp [decompose, h]
  -- 🎉 no goals
#align zsqrtd.hom_ext Zsqrtd.hom_ext

variable [CommRing R]

/-- The unique `RingHom` from `ℤ√d` to a ring `R`, constructed by replacing `√d` with the provided
root. Conversely, this associates to every mapping `ℤ√d →+* R` a value of `√d` in `R`. -/
@[simps]
def lift {d : ℤ} : { r : R // r * r = ↑d } ≃ (ℤ√d →+* R) where
  toFun r :=
    { toFun := fun a => a.1 + a.2 * (r : R)
      map_zero' := by simp
                      -- 🎉 no goals
      map_add' := fun a b => by
        simp
        -- ⊢ ↑a.re + ↑b.re + (↑a.im + ↑b.im) * ↑r = ↑a.re + ↑a.im * ↑r + (↑b.re + ↑b.im * …
                     -- 🎉 no goals
        ring
        -- 🎉 no goals
      map_one' := by simp
      map_mul' := fun a b => by
        have :
          (a.re + a.im * r : R) * (b.re + b.im * r) =
        -- ⊢ ↑a.re * ↑b.re + ↑d * ↑a.im * ↑b.im + (↑a.re * ↑b.im + ↑a.im * ↑b.re) * ↑r =  …
            a.re * b.re + (a.re * b.im + a.im * b.re) * r + a.im * b.im * (r * r) := by
        -- 🎉 no goals
          ring
        simp [this, r.prop]
        ring }
  invFun f := ⟨f sqrtd, by rw [← f.map_mul, dmuld, map_intCast]⟩
                           -- 🎉 no goals
  left_inv r := by
    ext
    -- ⊢ ↑((fun f => { val := ↑f sqrtd, property := (_ : ↑f sqrtd * ↑f sqrtd = ↑d) }) …
    simp
    -- 🎉 no goals
  right_inv f := by
    -- Porting note: was `ext`
    refine hom_ext _ _ ?_
    -- ⊢ ↑((fun r => { toMonoidHom := { toOneHom := { toFun := fun a => ↑a.re + ↑a.im …
    simp
    -- 🎉 no goals
#align zsqrtd.lift Zsqrtd.lift

/-- `lift r` is injective if `d` is non-square, and R has characteristic zero (that is, the map from
`ℤ` into `R` is injective). -/
theorem lift_injective [CharZero R] {d : ℤ} (r : { r : R // r * r = ↑d })
    (hd : ∀ n : ℤ, d ≠ n * n) : Function.Injective (lift r) :=
  (injective_iff_map_eq_zero (lift r)).mpr fun a ha => by
    have h_inj : Function.Injective ((↑) : ℤ → R) := Int.cast_injective
    -- ⊢ a = 0
    suffices lift r a.norm = 0 by
      simp only [coe_int_re, add_zero, lift_apply_apply, coe_int_im, Int.cast_zero,
        zero_mul] at this
      rwa [← Int.cast_zero, h_inj.eq_iff, norm_eq_zero hd] at this
    rw [norm_eq_mul_conj, RingHom.map_mul, ha, zero_mul]
    -- 🎉 no goals
#align zsqrtd.lift_injective Zsqrtd.lift_injective

/-- An element of `ℤ√d` has norm equal to `1` if and only if it is contained in the submonoid
of unitary elements. -/
theorem norm_eq_one_iff_mem_unitary {d : ℤ} {a : ℤ√d} : a.norm = 1 ↔ a ∈ unitary (ℤ√d) := by
  rw [unitary.mem_iff_self_mul_star, ← norm_eq_mul_conj]
  -- ⊢ norm a = 1 ↔ ↑(norm a) = 1
  norm_cast
  -- 🎉 no goals
#align zsqrtd.norm_eq_one_iff_mem_unitary Zsqrtd.norm_eq_one_iff_mem_unitary

/-- The kernel of the norm map on `ℤ√d` equals the submonoid of unitary elements. -/
theorem mker_norm_eq_unitary {d : ℤ} : MonoidHom.mker (@normMonoidHom d) = unitary (ℤ√d) :=
  Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary
#align zsqrtd.mker_norm_eq_unitary Zsqrtd.mker_norm_eq_unitary

end Zsqrtd
