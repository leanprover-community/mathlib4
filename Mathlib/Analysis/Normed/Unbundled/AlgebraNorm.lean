/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Seminorm

/-!
# Algebra norms

We define algebra norms and multiplicative algebra norms.

## Main Definitions
* `AlgebraNorm` : an algebra norm on an `R`-algebra `S` is a ring norm on `S` compatible with
  the action of `R`.
* `MulAlgebraNorm` : a multiplicative algebra norm on an `R`-algebra `S` is a multiplicative
  ring norm on `S` compatible with the action of `R`.

## Tags

norm, algebra norm
-/

/-- An algebra norm on an `R`-algebra `S` is a ring norm on `S` compatible with the
action of `R`. -/
structure AlgebraNorm (R : Type*) [SeminormedCommRing R] (S : Type*) [Ring S] [Algebra R S] extends
  RingNorm S, Seminorm R S

attribute [nolint docBlame] AlgebraNorm.toSeminorm AlgebraNorm.toRingNorm

instance (K : Type*) [NormedField K] : Inhabited (AlgebraNorm K K) :=
  ⟨{  toFun     := norm
      map_zero' := norm_zero
      add_le'   := norm_add_le
      neg'      := norm_neg
      smul'     := norm_mul
      mul_le'   := norm_mul_le
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero.mp }⟩

/-- `AlgebraNormClass F R S` states that `F` is a type of `R`-algebra norms on the ring `S`.
You should extend this class when you extend `AlgebraNorm`. -/
class AlgebraNormClass (F : Type*) (R : outParam <| Type*) [SeminormedCommRing R]
    (S : outParam <| Type*) [Ring S] [Algebra R S] [FunLike F S ℝ] : Prop
    extends RingNormClass F S ℝ, SeminormClass F R S

namespace AlgebraNorm

variable {R : Type*} [SeminormedCommRing R] {S : Type*} [Ring S] [Algebra R S] {f : AlgebraNorm R S}

/-- The ring seminorm underlying an algebra norm. -/
def toRingSeminorm' (f : AlgebraNorm R S) : RingSeminorm S :=
  f.toRingNorm.toRingSeminorm

instance : FunLike (AlgebraNorm R S) S ℝ where
  coe f := f.toFun
  coe_injective' f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe] at h
    cases f; cases f'; congr
    simp only at h
    ext s
    erw [h]
    rfl

instance algebraNormClass : AlgebraNormClass (AlgebraNorm R S) R S where
  map_zero f        := f.map_zero'
  map_add_le_add f  := f.add_le'
  map_mul_le_mul f  := f.mul_le'
  map_neg_eq_map f  := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

theorem toFun_eq_coe (p : AlgebraNorm R S) : p.toFun = p := rfl

@[ext]
theorem ext {p q : AlgebraNorm R S} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

/-- An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`. -/
theorem extends_norm' (hf1 : f 1 = 1) (a : R) : f (a • (1 : S)) = ‖a‖ := by
  rw [← mul_one ‖a‖, ← hf1]; exact f.smul' _ _

/-- An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`. -/
theorem extends_norm (hf1 : f 1 = 1) (a : R) : f (algebraMap R S a) = ‖a‖ := by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' hf1 _

/-- The restriction of an algebra norm to a subalgebra. -/
def restriction (A : Subalgebra R S) (f : AlgebraNorm R S) : AlgebraNorm R A where
  toFun x     := f x.val
  map_zero'   := map_zero f
  add_le' x y := map_add_le_add _ _ _
  neg' x      := map_neg_eq_map _ _
  mul_le' x y := map_mul_le_mul _ _ _
  eq_zero_of_map_eq_zero' x hx := by
    rw [← ZeroMemClass.coe_eq_zero]; exact eq_zero_of_map_eq_zero f hx
  smul' r x := map_smul_eq_mul _ _ _

/-- The restriction of an algebra norm in a scalar tower. -/
def isScalarTower_restriction {A : Type*} [CommRing A] [Algebra R A] [Algebra A S]
    [IsScalarTower R A S] (hinj : Function.Injective (algebraMap A S)) (f : AlgebraNorm R S) :
    AlgebraNorm R A where
  toFun x     := f (algebraMap A S x)
  map_zero'   := by simp only [map_zero]
  add_le' x y := by simp only [map_add, map_add_le_add]
  neg' x      := by simp only [map_neg, map_neg_eq_map]
  mul_le' x y := by simp only [map_mul, map_mul_le_mul]
  eq_zero_of_map_eq_zero' x hx := by
    rw [← map_eq_zero_iff (algebraMap A S) hinj]
    exact eq_zero_of_map_eq_zero f hx
  smul' r x := by
    simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    simp only [← smul_eq_mul, algebraMap_smul, map_smul_eq_mul]

end AlgebraNorm

/-- A multiplicative algebra norm on an `R`-algebra norm `S` is a multiplicative ring norm on `S`
  compatible with the action of `R`. -/
structure MulAlgebraNorm (R : Type*) [SeminormedCommRing R] (S : Type*) [Ring S] [Algebra R S]
  extends MulRingNorm S, Seminorm R S

attribute [nolint docBlame] MulAlgebraNorm.toSeminorm MulAlgebraNorm.toMulRingNorm

instance (K : Type*) [NormedField K] : Inhabited (MulAlgebraNorm K K) :=
  ⟨{  toFun     := norm
      map_zero' := norm_zero
      add_le'   := norm_add_le
      neg'      := norm_neg
      smul'     := norm_mul
      map_one'  := norm_one
      map_mul'  := norm_mul
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero.mp }⟩

/-- `MulAlgebraNormClass F R S` states that `F` is a type of multiplicative `R`-algebra norms on
the ring `S`. You should extend this class when you extend `MulAlgebraNorm`. -/
class MulAlgebraNormClass (F : Type*) (R : outParam <| Type*) [SeminormedCommRing R]
    (S : outParam <| Type*) [Ring S] [Algebra R S] [FunLike F S ℝ] : Prop
    extends MulRingNormClass F S ℝ, SeminormClass F R S

namespace MulAlgebraNorm

variable {R S : outParam <| Type*} [SeminormedCommRing R] [Ring S] [Algebra R S]
  {f : AlgebraNorm R S}

instance : FunLike (MulAlgebraNorm R S) S ℝ where
  coe f := f.toFun
  coe_injective' f f' h:= by
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, DFunLike.coe_fn_eq] at h
    obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := f'; congr

instance mulAlgebraNormClass : MulAlgebraNormClass (MulAlgebraNorm R S) R S where
  map_zero f        := f.map_zero'
  map_add_le_add f  := f.add_le'
  map_one f         := f.map_one'
  map_mul f         := f.map_mul'
  map_neg_eq_map f  := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

theorem toFun_eq_coe (p : MulAlgebraNorm R S) : p.toFun = p := rfl

@[ext]
theorem ext {p q : MulAlgebraNorm R S} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

/-- A multiplicative `R`-algebra norm extends the norm on `R`. -/
theorem extends_norm' (f : MulAlgebraNorm R S) (a : R) : f (a • (1 : S)) = ‖a‖ := by
  rw [← mul_one ‖a‖, ← f.map_one', ← f.smul', toFun_eq_coe]

/-- A multiplicative `R`-algebra norm extends the norm on `R`. -/
theorem extends_norm (f : MulAlgebraNorm R S) (a : R) : f (algebraMap R S a) = ‖a‖ := by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' _ _

end MulAlgebraNorm

namespace MulRingNorm

variable {R : Type*} [NonAssocRing R]

/-- The ring norm underlying a multiplicative ring norm. -/
def toRingNorm (f : MulRingNorm R) : RingNorm R where
  toFun       := f
  map_zero'   := f.map_zero'
  add_le'     := f.add_le'
  neg'        := f.neg'
  mul_le' x y := le_of_eq (f.map_mul' x y)
  eq_zero_of_map_eq_zero' := f.eq_zero_of_map_eq_zero'

/-- A multiplicative ring norm is power-multiplicative. -/
theorem isPowMul {A : Type*} [Ring A] (f : MulRingNorm A) : IsPowMul f := fun x n hn => by
  cases n
  · cutsat
  · rw [map_pow]

end MulRingNorm
