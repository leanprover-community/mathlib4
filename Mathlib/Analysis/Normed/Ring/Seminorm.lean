/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies
-/
import Mathlib.Analysis.Normed.Field.Basic

#align_import analysis.normed.ring.seminorm from "leanprover-community/mathlib"@"7ea604785a41a0681eac70c5a82372493dbefc68"

/-!
# Seminorms and norms on rings

This file defines seminorms and norms on rings. These definitions are useful when one needs to
consider multiple (semi)norms on a given ring.

## Main declarations

For a ring `R`:
* `RingSeminorm`: A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes
  nonnegative values, is subadditive and submultiplicative and such that `f (-x) = f x` for all
  `x ∈ R`.
* `RingNorm`: A seminorm `f` is a norm if `f x = 0` if and only if `x = 0`.
* `MulRingSeminorm`: A multiplicative seminorm on a ring `R` is a ring seminorm that preserves
  multiplication.
* `MulRingNorm`: A multiplicative norm on a ring `R` is a ring norm that preserves multiplication.

## Notes

The corresponding hom classes are defined in `Mathlib.Analysis.Order.Hom.Basic` to be used by
absolute values.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/


open NNReal

variable {F R S : Type*} (x y : R) (r : ℝ)

/-- A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes nonnegative
  values, is subadditive and submultiplicative and such that `f (-x) = f x` for all `x ∈ R`. -/
structure RingSeminorm (R : Type*) [NonUnitalNonAssocRing R] extends AddGroupSeminorm R where
  /-- The property of a `RingSeminorm` that for all `x` and `y` in the ring, the norm of `x * y` is
    less than the norm of `x` times the norm of `y`. -/
  mul_le' : ∀ x y : R, toFun (x * y) ≤ toFun x * toFun y
#align ring_seminorm RingSeminorm

/-- A function `f : R → ℝ` is a norm on a (nonunital) ring if it is a seminorm and `f x = 0`
  implies `x = 0`. -/
structure RingNorm (R : Type*) [NonUnitalNonAssocRing R] extends RingSeminorm R, AddGroupNorm R
#align ring_norm RingNorm

/-- A multiplicative seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero and
multiplication, takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
-/
structure MulRingSeminorm (R : Type*) [NonAssocRing R] extends AddGroupSeminorm R,
  MonoidWithZeroHom R ℝ
#align mul_ring_seminorm MulRingSeminorm

/-- A multiplicative norm on a ring `R` is a multiplicative ring seminorm such that `f x = 0`
implies `x = 0`. -/
structure MulRingNorm (R : Type*) [NonAssocRing R] extends MulRingSeminorm R, AddGroupNorm R
#align mul_ring_norm MulRingNorm

attribute [nolint docBlame]
  RingSeminorm.toAddGroupSeminorm RingNorm.toAddGroupNorm RingNorm.toRingSeminorm
    MulRingSeminorm.toAddGroupSeminorm MulRingSeminorm.toMonoidWithZeroHom
    MulRingNorm.toAddGroupNorm MulRingNorm.toMulRingSeminorm

namespace RingSeminorm

section NonUnitalRing

variable [NonUnitalRing R]

instance ringSeminormClass : RingSeminormClass (RingSeminorm R) R ℝ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    -- ⊢ { toAddGroupSeminorm := toAddGroupSeminorm✝, mul_le' := mul_le'✝ } = g
    cases g
    -- ⊢ { toAddGroupSeminorm := toAddGroupSeminorm✝¹, mul_le' := mul_le'✝¹ } = { toA …
    congr
    -- ⊢ toAddGroupSeminorm✝¹ = toAddGroupSeminorm✝
    ext x
    -- ⊢ ↑toAddGroupSeminorm✝¹ x = ↑toAddGroupSeminorm✝ x
    exact congr_fun h x
    -- 🎉 no goals
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
#align ring_seminorm.ring_seminorm_class RingSeminorm.ringSeminormClass

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`. -/
instance : CoeFun (RingSeminorm R) fun _ => R → ℝ :=
  FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe (p : RingSeminorm R) : (p.toAddGroupSeminorm : R → ℝ) = p :=
  rfl
#align ring_seminorm.to_fun_eq_coe RingSeminorm.toFun_eq_coe

@[ext]
theorem ext {p q : RingSeminorm R} : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align ring_seminorm.ext RingSeminorm.ext

instance : Zero (RingSeminorm R) :=
  ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with mul_le' :=
    fun _ _ => (zero_mul _).ge }⟩

theorem eq_zero_iff {p : RingSeminorm R} : p = 0 ↔ ∀ x, p x = 0 :=
  FunLike.ext_iff
#align ring_seminorm.eq_zero_iff RingSeminorm.eq_zero_iff

theorem ne_zero_iff {p : RingSeminorm R} : p ≠ 0 ↔ ∃ x, p x ≠ 0 := by simp [eq_zero_iff]
                                                                      -- 🎉 no goals
#align ring_seminorm.ne_zero_iff RingSeminorm.ne_zero_iff

instance : Inhabited (RingSeminorm R) :=
  ⟨0⟩

/-- The trivial seminorm on a ring `R` is the `RingSeminorm` taking value `0` at `0` and `1` at
every other element. -/
instance [DecidableEq R] : One (RingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      mul_le' := fun x y => by
        by_cases h : x * y = 0
        -- ⊢ AddGroupSeminorm.toFun { toFun := src✝.toFun, map_zero' := (_ : AddGroupSemi …
        · refine' (if_pos h).trans_le (mul_nonneg _ _) <;>
          -- ⊢ 0 ≤ AddGroupSeminorm.toFun { toFun := src✝.toFun, map_zero' := (_ : AddGroup …
            · change _ ≤ ite _ _ _
              -- ⊢ 0 ≤ if x = 0 then 0 else 1
              -- ⊢ 0 ≤ if y = 0 then 0 else 1
              -- ⊢ 0 ≤ 0
              split_ifs
              -- 🎉 no goals
              -- ⊢ 0 ≤ 0
              exacts [le_rfl, zero_le_one]
              -- 🎉 no goals
        · change ite _ _ _ ≤ ite _ _ _ * ite _ _ _
          -- ⊢ (if x * y = 0 then 0 else 1) ≤ (if x = 0 then 0 else 1) * if y = 0 then 0 el …
          simp only [if_false, h, left_ne_zero_of_mul h, right_ne_zero_of_mul h, mul_one,
            le_refl] }⟩

@[simp]
theorem apply_one [DecidableEq R] (x : R) : (1 : RingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl
#align ring_seminorm.apply_one RingSeminorm.apply_one

end NonUnitalRing

section Ring

variable [Ring R] (p : RingSeminorm R)

theorem seminorm_one_eq_one_iff_ne_zero (hp : p 1 ≤ 1) : p 1 = 1 ↔ p ≠ 0 := by
  refine'
    ⟨fun h =>
      ne_zero_iff.mpr
        ⟨1, by
          rw [h]
          exact one_ne_zero⟩,
      fun h => ?_⟩
  obtain hp0 | hp0 := (map_nonneg p (1 : R)).eq_or_gt
  -- ⊢ ↑p 1 = 1
  · exfalso
    -- ⊢ False
    refine h (ext fun x => (map_nonneg _ _).antisymm' ?_)
    -- ⊢ ↑p x ≤ 0
    simpa only [hp0, mul_one, mul_zero] using map_mul_le_mul p x 1
    -- 🎉 no goals
  · refine' hp.antisymm ((le_mul_iff_one_le_left hp0).1 _)
    -- ⊢ ↑p 1 ≤ ↑p 1 * ↑p 1
    simpa only [one_mul] using map_mul_le_mul p (1 : R) _
    -- 🎉 no goals
#align ring_seminorm.seminorm_one_eq_one_iff_ne_zero RingSeminorm.seminorm_one_eq_one_iff_ne_zero

end Ring

end RingSeminorm

/-- The norm of a `NonUnitalSeminormedRing` as a `RingSeminorm`. -/
def normRingSeminorm (R : Type*) [NonUnitalSeminormedRing R] : RingSeminorm R :=
  { normAddGroupSeminorm R with
    toFun := norm
    mul_le' := norm_mul_le }
#align norm_ring_seminorm normRingSeminorm

namespace RingNorm

variable [NonUnitalRing R]

instance ringNormClass : RingNormClass (RingNorm R) R ℝ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    -- ⊢ { toRingSeminorm := toRingSeminorm✝, eq_zero_of_map_eq_zero' := eq_zero_of_m …
    cases g
    -- ⊢ { toRingSeminorm := toRingSeminorm✝¹, eq_zero_of_map_eq_zero' := eq_zero_of_ …
    congr
    -- ⊢ toRingSeminorm✝¹ = toRingSeminorm✝
    ext x
    -- ⊢ ↑toRingSeminorm✝¹ x = ↑toRingSeminorm✝ x
    exact congr_fun h x
    -- 🎉 no goals
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
#align ring_norm.ring_norm_class RingNorm.ringNormClass

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`. -/
instance : CoeFun (RingNorm R) fun _ => R → ℝ :=
  ⟨fun p => p.toFun⟩

-- Porting note: This is a syntactic tautology in Lean 4
-- @[simp]
-- theorem toFun_eq_coe (p : RingNorm R) : p.toFun = p := rfl
#noalign ring_norm.to_fun_eq_coe

@[ext]
theorem ext {p q : RingNorm R} : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align ring_norm.ext RingNorm.ext

variable (R)

/-- The trivial norm on a ring `R` is the `RingNorm` taking value `0` at `0` and `1` at every
  other element. -/
instance [DecidableEq R] : One (RingNorm R) :=
  ⟨{ (1 : RingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]
theorem apply_one [DecidableEq R] (x : R) : (1 : RingNorm R) x = if x = 0 then 0 else 1 :=
  rfl
#align ring_norm.apply_one RingNorm.apply_one

instance [DecidableEq R] : Inhabited (RingNorm R) :=
  ⟨1⟩

end RingNorm

namespace MulRingSeminorm

variable [NonAssocRing R]

instance mulRingSeminormClass : MulRingSeminormClass (MulRingSeminorm R) R ℝ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    -- ⊢ { toAddGroupSeminorm := toAddGroupSeminorm✝, map_one' := map_one'✝, map_mul' …
    cases g
    -- ⊢ { toAddGroupSeminorm := toAddGroupSeminorm✝¹, map_one' := map_one'✝¹, map_mu …
    congr
    -- ⊢ toAddGroupSeminorm✝¹ = toAddGroupSeminorm✝
    ext x
    -- ⊢ ↑toAddGroupSeminorm✝¹ x = ↑toAddGroupSeminorm✝ x
    exact congr_fun h x
    -- 🎉 no goals
  map_zero f := f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
#align mul_ring_seminorm.mul_ring_seminorm_class MulRingSeminorm.mulRingSeminormClass

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`. -/
instance : CoeFun (MulRingSeminorm R) fun _ => R → ℝ :=
  FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe (p : MulRingSeminorm R) : (p.toAddGroupSeminorm : R → ℝ) = p :=
  rfl
#align mul_ring_seminorm.to_fun_eq_coe MulRingSeminorm.toFun_eq_coe

@[ext]
theorem ext {p q : MulRingSeminorm R} : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align mul_ring_seminorm.ext MulRingSeminorm.ext

variable [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

/-- The trivial seminorm on a ring `R` is the `MulRingSeminorm` taking value `0` at `0` and `1` at
every other element. -/
instance : One (MulRingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      map_one' := if_neg one_ne_zero
      map_mul' := fun x y => by
        obtain rfl | hx := eq_or_ne x 0
        -- ⊢ AddGroupSeminorm.toFun { toFun := src✝.toFun, map_zero' := (_ : AddGroupSemi …
        · simp
          -- 🎉 no goals
        obtain rfl | hy := eq_or_ne y 0
        -- ⊢ AddGroupSeminorm.toFun { toFun := src✝.toFun, map_zero' := (_ : AddGroupSemi …
        · simp
          -- 🎉 no goals
        · simp [hx, hy] }⟩
          -- 🎉 no goals

@[simp]
theorem apply_one (x : R) : (1 : MulRingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl
#align mul_ring_seminorm.apply_one MulRingSeminorm.apply_one

instance : Inhabited (MulRingSeminorm R) :=
  ⟨1⟩

end MulRingSeminorm

namespace MulRingNorm

variable [NonAssocRing R]

instance mulRingNormClass : MulRingNormClass (MulRingNorm R) R ℝ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    -- ⊢ { toMulRingSeminorm := toMulRingSeminorm✝, eq_zero_of_map_eq_zero' := eq_zer …
    cases g
    -- ⊢ { toMulRingSeminorm := toMulRingSeminorm✝¹, eq_zero_of_map_eq_zero' := eq_ze …
    congr
    -- ⊢ toMulRingSeminorm✝¹ = toMulRingSeminorm✝
    ext x
    -- ⊢ ↑toMulRingSeminorm✝¹ x = ↑toMulRingSeminorm✝ x
    exact congr_fun h x
    -- 🎉 no goals
  map_zero f := f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
#align mul_ring_norm.mul_ring_norm_class MulRingNorm.mulRingNormClass

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`. -/
instance : CoeFun (MulRingNorm R) fun _ => R → ℝ :=
  ⟨fun p => p.toFun⟩

-- Porting note: This is a syntactic tautology in Lean 4
-- @[simp]
-- theorem toFun_eq_coe (p : MulRingNorm R) : p.toFun = p := rfl
#noalign mul_ring_norm.to_fun_eq_coe

@[ext]
theorem ext {p q : MulRingNorm R} : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align mul_ring_norm.ext MulRingNorm.ext

variable (R)

variable [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

/-- The trivial norm on a ring `R` is the `MulRingNorm` taking value `0` at `0` and `1` at every
other element. -/
instance : One (MulRingNorm R) :=
  ⟨{ (1 : MulRingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]
theorem apply_one (x : R) : (1 : MulRingNorm R) x = if x = 0 then 0 else 1 :=
  rfl
#align mul_ring_norm.apply_one MulRingNorm.apply_one

instance : Inhabited (MulRingNorm R) :=
  ⟨1⟩

end MulRingNorm

/-- A nonzero ring seminorm on a field `K` is a ring norm. -/
def RingSeminorm.toRingNorm {K : Type*} [Field K] (f : RingSeminorm K) (hnt : f ≠ 0) :
    RingNorm K :=
  { f with
    eq_zero_of_map_eq_zero' := fun x hx => by
      obtain ⟨c, hc⟩ := RingSeminorm.ne_zero_iff.mp hnt
      -- ⊢ x = 0
      by_contra hn0
      -- ⊢ False
      have hc0 : f c = 0 := by
        rw [← mul_one c, ← mul_inv_cancel hn0, ← mul_assoc, mul_comm c, mul_assoc]
        exact
          le_antisymm
            (le_trans (map_mul_le_mul f _ _)
              (by rw [← RingSeminorm.toFun_eq_coe, ← AddGroupSeminorm.toFun_eq_coe, hx,
                zero_mul]))
            (map_nonneg f _)
      exact hc hc0 }
      -- 🎉 no goals
#align ring_seminorm.to_ring_norm RingSeminorm.toRingNorm

/-- The norm of a `NonUnitalNormedRing` as a `RingNorm`. -/
@[simps!]
def normRingNorm (R : Type*) [NonUnitalNormedRing R] : RingNorm R :=
  { normAddGroupNorm R, normRingSeminorm R with }
#align norm_ring_norm normRingNorm
