/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies
-/
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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
  `MulRingNorm R` is essentially the same as `AbsoluteValue R ℝ`, and it is recommended to
  use the latter instead to avoid duplicating results.

## Notes

The corresponding hom classes are defined in `Mathlib/Analysis/Order/Hom/Basic.lean` to be used by
absolute values.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/


open NNReal

variable {R : Type*}

/-- A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes nonnegative
  values, is subadditive and submultiplicative and such that `f (-x) = f x` for all `x ∈ R`. -/
structure RingSeminorm (R : Type*) [NonUnitalNonAssocRing R] extends AddGroupSeminorm R where
  /-- The property of a `RingSeminorm` that for all `x` and `y` in the ring, the norm of `x * y` is
  less than the norm of `x` times the norm of `y`. -/
  mul_le' : ∀ x y : R, toFun (x * y) ≤ toFun x * toFun y

/-- A function `f : R → ℝ` is a norm on a (nonunital) ring if it is a seminorm and `f x = 0`
  implies `x = 0`. -/
structure RingNorm (R : Type*) [NonUnitalNonAssocRing R] extends RingSeminorm R, AddGroupNorm R

/-- A multiplicative seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero and
multiplication, takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
-/
structure MulRingSeminorm (R : Type*) [NonAssocRing R] extends AddGroupSeminorm R,
  MonoidWithZeroHom R ℝ

/-- A multiplicative norm on a ring `R` is a multiplicative ring seminorm such that `f x = 0`
implies `x = 0`.

It is recommended to use `AbsoluteValue R ℝ` instead (which works for `Semiring R`
and is equivalent to `MulRingNorm R` for a nontrivial `Ring R`). -/
structure MulRingNorm (R : Type*) [NonAssocRing R] extends MulRingSeminorm R, AddGroupNorm R

attribute [nolint docBlame]
  RingSeminorm.toAddGroupSeminorm RingNorm.toAddGroupNorm RingNorm.toRingSeminorm
    MulRingSeminorm.toAddGroupSeminorm MulRingSeminorm.toMonoidWithZeroHom
    MulRingNorm.toAddGroupNorm MulRingNorm.toMulRingSeminorm

namespace RingSeminorm

section NonUnitalRing

variable [NonUnitalRing R]

instance funLike : FunLike (RingSeminorm R) R ℝ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

instance ringSeminormClass : RingSeminormClass (RingSeminorm R) R ℝ where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'

@[simp]
theorem toFun_eq_coe (p : RingSeminorm R) : (p.toAddGroupSeminorm : R → ℝ) = p :=
  rfl

@[ext]
theorem ext {p q : RingSeminorm R} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

instance : Zero (RingSeminorm R) :=
  ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with mul_le' :=
    fun _ _ => (zero_mul _).ge }⟩

theorem eq_zero_iff {p : RingSeminorm R} : p = 0 ↔ ∀ x, p x = 0 :=
  DFunLike.ext_iff

theorem ne_zero_iff {p : RingSeminorm R} : p ≠ 0 ↔ ∃ x, p x ≠ 0 := by simp [eq_zero_iff]

instance : Inhabited (RingSeminorm R) :=
  ⟨0⟩

/-- The trivial seminorm on a ring `R` is the `RingSeminorm` taking value `0` at `0` and `1` at
every other element. -/
instance [DecidableEq R] : One (RingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      mul_le' := fun x y => by
        by_cases h : x * y = 0
        · refine (if_pos h).trans_le (mul_nonneg ?_ ?_) <;>
            · change _ ≤ ite _ _ _
              split_ifs
              exacts [le_rfl, zero_le_one]
        · change ite _ _ _ ≤ ite _ _ _ * ite _ _ _
          simp only [if_false, h, left_ne_zero_of_mul h, right_ne_zero_of_mul h, mul_one,
            le_refl] }⟩

@[simp]
theorem apply_one [DecidableEq R] (x : R) : (1 : RingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl

end NonUnitalRing

section Ring

variable [Ring R] (p : RingSeminorm R)

theorem seminorm_one_eq_one_iff_ne_zero (hp : p 1 ≤ 1) : p 1 = 1 ↔ p ≠ 0 := by
  refine
    ⟨fun h => ne_zero_iff.mpr ⟨1, by rw [h]; exact one_ne_zero⟩,
      fun h => ?_⟩
  obtain hp0 | hp0 := (apply_nonneg p (1 : R)).eq_or_lt'
  · exfalso
    refine h (ext fun x => (apply_nonneg _ _).antisymm' ?_)
    simpa only [hp0, mul_one, mul_zero] using map_mul_le_mul p x 1
  · refine hp.antisymm ((le_mul_iff_one_le_left hp0).1 ?_)
    simpa only [one_mul] using map_mul_le_mul p (1 : R) _

end Ring

section CommRing

variable [CommRing R] (p : RingSeminorm R)

theorem exists_index_pow_le (hna : IsNonarchimedean p) (x y : R) (n : ℕ) :
    ∃ (m : ℕ), m < n + 1 ∧ p ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤
      (p (x ^ m) * p (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)) := by
  obtain ⟨m, hm_lt, hm⟩ := IsNonarchimedean.add_pow_le hna n x y
  exact ⟨m, hm_lt, by gcongr⟩

end CommRing

end RingSeminorm

/-- If `f` is a ring seminorm on `a`, then `∀ {n : ℕ}, n ≠ 0 → f (a ^ n) ≤ f a ^ n`. -/
theorem map_pow_le_pow {F α : Type*} [Ring α] [FunLike F α ℝ] [RingSeminormClass F α ℝ] (f : F)
    (a : α) : ∀ {n : ℕ}, n ≠ 0 → f (a ^ n) ≤ f a ^ n
  | 0, h => absurd rfl h
  | 1, _ => by simp only [pow_one, le_refl]
  | n + 2, _ => by
    simp only [pow_succ _ (n + 1)]
    exact
      le_trans (map_mul_le_mul f _ a)
        (mul_le_mul_of_nonneg_right (map_pow_le_pow _ _ n.succ_ne_zero) (apply_nonneg f a))

/-- If `f` is a ring seminorm on `a` with `f 1 ≤ 1`, then `∀ (n : ℕ), f (a ^ n) ≤ f a ^ n`. -/
theorem map_pow_le_pow' {F α : Type*} [Ring α] [FunLike F α ℝ] [RingSeminormClass F α ℝ] {f : F}
    (hf1 : f 1 ≤ 1) (a : α) : ∀ n : ℕ, f (a ^ n) ≤ f a ^ n
  | 0 => by simp only [pow_zero, hf1]
  | n + 1 => map_pow_le_pow _ _ n.succ_ne_zero

/-- The norm of a `NonUnitalSeminormedRing` as a `RingSeminorm`. -/
def normRingSeminorm (R : Type*) [NonUnitalSeminormedRing R] : RingSeminorm R :=
  { normAddGroupSeminorm R with
    toFun := norm
    mul_le' := norm_mul_le }

namespace RingSeminorm

variable [Ring R] (p : RingSeminorm R)

open Filter Nat Real

/-- If `f` is a ring seminorm on `R` with `f 1 ≤ 1` and `s : ℕ → ℕ` is bounded by `n`, then
  `f (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))` is eventually bounded. -/
theorem isBoundedUnder (hp : p 1 ≤ 1) {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x : R} (ψ : ℕ → ℕ) :
    IsBoundedUnder LE.le atTop fun n : ℕ => p (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ)) := by
  have h_le : ∀ m : ℕ, p (x ^ s (ψ m)) ^ (1 / (ψ m : ℝ)) ≤ p x ^ ((s (ψ m) : ℝ) / (ψ m : ℝ)) := by
    intro m
    rw [← mul_one_div (s (ψ m) : ℝ), rpow_mul (apply_nonneg p x), rpow_natCast]
    exact rpow_le_rpow (apply_nonneg _ _) (map_pow_le_pow' hp x _)
      (one_div_nonneg.mpr (cast_nonneg _))
  apply isBoundedUnder_of
  by_cases! hfx : p x ≤ 1
  · use 1, fun m => le_trans (h_le m)
      (rpow_le_one (apply_nonneg _ _) hfx (div_nonneg (cast_nonneg _) (cast_nonneg _)))
  · use p x
    intro m
    apply le_trans (h_le m)
    conv_rhs => rw [← rpow_one (p x)]
    exact rpow_le_rpow_of_exponent_le hfx.le
      (div_le_one_of_le₀ (cast_le.mpr (hs_le _)) (cast_nonneg _))

end RingSeminorm

namespace RingNorm

section NonUnitalRing

variable [NonUnitalRing R]

instance funLike : FunLike (RingNorm R) R ℝ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

instance ringNormClass : RingNormClass (RingNorm R) R ℝ where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

theorem toFun_eq_coe (p : RingNorm R) : p.toFun = p := rfl

@[ext]
theorem ext {p q : RingNorm R} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

variable (R)

/-- The trivial norm on a ring `R` is the `RingNorm` taking value `0` at `0` and `1` at every
  other element. -/
instance [DecidableEq R] : One (RingNorm R) :=
  ⟨{ (1 : RingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]
theorem apply_one [DecidableEq R] (x : R) : (1 : RingNorm R) x = if x = 0 then 0 else 1 :=
  rfl

instance [DecidableEq R] : Inhabited (RingNorm R) :=
  ⟨1⟩

end NonUnitalRing

/-- The `NormedRing` structure on a ring `R` determined by a `RingNorm` -/
-- See note |reducible non-instances]
abbrev toNormedRing [Ring R] (f : RingNorm R) : NormedRing R where
  __ := ‹Ring R›
  __ := f.toAddGroupNorm.toNormedAddCommGroup
  norm_mul_le := map_mul_le_mul f

end RingNorm

namespace MulRingSeminorm

variable [NonAssocRing R]

instance funLike : FunLike (MulRingSeminorm R) R ℝ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

instance mulRingSeminormClass : MulRingSeminormClass (MulRingSeminorm R) R ℝ where
  map_zero f := f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'

@[simp]
theorem toFun_eq_coe (p : MulRingSeminorm R) : (p.toAddGroupSeminorm : R → ℝ) = p :=
  rfl

@[ext]
theorem ext {p q : MulRingSeminorm R} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

variable [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

/-- The trivial seminorm on a ring `R` is the `MulRingSeminorm` taking value `0` at `0` and `1` at
every other element. -/
instance : One (MulRingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      map_one' := if_neg one_ne_zero
      map_mul' := fun x y => by
        obtain rfl | hx := eq_or_ne x 0
        · simp
        obtain rfl | hy := eq_or_ne y 0
        · simp
        · simp [hx, hy] }⟩

@[simp]
theorem apply_one (x : R) : (1 : MulRingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl

instance : Inhabited (MulRingSeminorm R) :=
  ⟨1⟩

end MulRingSeminorm

namespace MulRingNorm

variable [NonAssocRing R]

instance funLike : FunLike (MulRingNorm R) R ℝ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

instance mulRingNormClass : MulRingNormClass (MulRingNorm R) R ℝ where
  map_zero f := f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

theorem toFun_eq_coe (p : MulRingNorm R) : p.toFun = p := rfl

@[ext]
theorem ext {p q : MulRingNorm R} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

variable (R)
variable [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

/-- The trivial norm on a ring `R` is the `MulRingNorm` taking value `0` at `0` and `1` at every
other element. -/
instance : One (MulRingNorm R) :=
  ⟨{ (1 : MulRingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]
theorem apply_one (x : R) : (1 : MulRingNorm R) x = if x = 0 then 0 else 1 :=
  rfl

instance : Inhabited (MulRingNorm R) :=
  ⟨1⟩

section MulRingNorm_equiv_AbsoluteValue

variable {R : Type*} [Ring R] [Nontrivial R]

/-- The equivalence of `MulRingNorm R` and `AbsoluteValue R ℝ` when `R` is a nontrivial ring. -/
def mulRingNormEquivAbsoluteValue : MulRingNorm R ≃ AbsoluteValue R ℝ where
  toFun N := {
    toFun := N.toFun
    map_mul' := N.map_mul'
    nonneg' := apply_nonneg N
    eq_zero' x := ⟨N.eq_zero_of_map_eq_zero' x, fun h ↦ h ▸ N.map_zero'⟩
    add_le' := N.add_le'
  }
  invFun v := {
    toFun := v.toFun
    map_zero' := (v.eq_zero' 0).mpr rfl
    add_le' := v.add_le'
    neg' := v.map_neg
    map_one' := v.map_one
    map_mul' := v.map_mul'
    eq_zero_of_map_eq_zero' x := (v.eq_zero' x).mp
  }
  left_inv N := by constructor
  right_inv v := by ext1 x; simp

lemma mulRingNormEquivAbsoluteValue_apply (N : MulRingNorm R) (x : R) :
    mulRingNormEquivAbsoluteValue N x = N x := rfl

lemma mulRingNormEquivAbsoluteValue_symm_apply (v : AbsoluteValue R ℝ) (x : R) :
    mulRingNormEquivAbsoluteValue.symm v x = v x := rfl

end MulRingNorm_equiv_AbsoluteValue

end MulRingNorm

/-- A nonzero ring seminorm on a field `K` is a ring norm. -/
def RingSeminorm.toRingNorm {K : Type*} [Field K] (f : RingSeminorm K) (hnt : f ≠ 0) :
    RingNorm K :=
  { f with
    eq_zero_of_map_eq_zero' := fun x hx => by
      obtain ⟨c, hc⟩ := RingSeminorm.ne_zero_iff.mp hnt
      by_contra hn0
      have hc0 : f c = 0 := by
        rw [← mul_one c, ← mul_inv_cancel₀ hn0, ← mul_assoc, mul_comm c, mul_assoc]
        exact
          le_antisymm
            (le_trans (map_mul_le_mul f _ _)
              (by rw [← RingSeminorm.toFun_eq_coe, ← AddGroupSeminorm.toFun_eq_coe, hx,
                zero_mul]))
            (apply_nonneg f _)
      exact hc hc0 }

/-- The norm of a `NonUnitalNormedRing` as a `RingNorm`. -/
@[simps!]
def normRingNorm (R : Type*) [NonUnitalNormedRing R] : RingNorm R :=
  { normAddGroupNorm R, normRingSeminorm R with }

open Int

/-- The seminorm on a `SeminormedRing`, as a `RingSeminorm`. -/
def SeminormedRing.toRingSeminorm (R : Type*) [SeminormedRing R] : RingSeminorm R where
  toFun     := norm
  map_zero' := norm_zero
  add_le'   := norm_add_le
  mul_le'   := norm_mul_le
  neg'      := norm_neg

/-- The norm on a `NormedRing`, as a `RingNorm`. -/
@[simps]
def NormedRing.toRingNorm (R : Type*) [NormedRing R] : RingNorm R where
  toFun     := norm
  map_zero' := norm_zero
  add_le'   := norm_add_le
  mul_le'   := norm_mul_le
  neg'      := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx

@[simp]
theorem NormedRing.toRingNorm_apply (R : Type*) [NormedRing R] (x : R) :
    (NormedRing.toRingNorm R) x = ‖x‖ :=
  rfl

/-- The norm on a `NormedField`, as a `MulRingNorm`. -/
def NormedField.toMulRingNorm (R : Type*) [NormedField R] : MulRingNorm R where
  toFun     := norm
  map_zero' := norm_zero
  map_one'  := norm_one
  add_le'   := norm_add_le
  map_mul'  := norm_mul
  neg'      := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx

/-- The norm on a `NormedField`, as an `AbsoluteValue`. -/
def NormedField.toAbsoluteValue (R : Type*) [NormedField R] : AbsoluteValue R ℝ where
  toFun     := norm
  map_mul'  := norm_mul
  nonneg'   := norm_nonneg
  eq_zero' _ := norm_eq_zero
  add_le'   := norm_add_le
