/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Kenny Lau, Jiayang Hong
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!

# Quadratic Algebra

In this file we define the quadratic algebra `QuadraticAlgebra R a b` over a commutative ring `R`,
and define some algebraic structures on it.

## Main definitions

* `QuadraticAlgebra R a b`:
  [Bourbaki, *Algebra I*][bourbaki1989] with coefficients `a`, `b` in `R`.

## Warning
If `R` is a ring, then `QuadraticAlgebra a b` is an `R`-algebra, and if `R` is of characteristic
zero then the same holds for `QuadraticAlgebra a b`. In particular, in the very common case where
`R` is `ℚ` and `a` and `b` are such that `QuadraticAlgebra a b` is a field, then
`QuadraticAlgebra a b` is a `ℚ`-algebra in two ways, that are not definitionally equal. This is a
known diamond for characteristic zero fields. If you are working in this setting you should start
your file with
```
attribute [-instance] DivisionRing.toRatAlgebra
```
to keep the `CharZero` instance but to avoid having two `Algebra` instances. (Note that all the
basic theorems about `QuadraticAlgebra` are stated using the general instance
`Algebra R (QuadraticAlgebra a b)`, so you don't want to deactivate that one.)

## Tags

Quadratic algebra, quadratic extension

-/

@[expose] public section

universe u

/-- Quadratic algebra over a type with fixed coefficient where $i^2 = a + bi$, implemented as
a structure with two fields, `re` and `im`. When `R` is a commutative ring, this is isomorphic to
`R[X]/(X^2-b*X-a)`. -/
@[ext]
structure QuadraticAlgebra (R : Type u) (a b : R) : Type u where
  /-- Real part of an element in quadratic algebra -/
  re : R
  /-- Imaginary part of an element in quadratic algebra -/
  im : R
deriving DecidableEq

initialize_simps_projections QuadraticAlgebra (as_prefix re, as_prefix im)

variable {R : Type*}
namespace QuadraticAlgebra

/-- The equivalence between quadratic algebra over `R` and `R × R`. -/
@[simps symm_apply]
def equivProd (a b : R) : QuadraticAlgebra R a b ≃ R × R where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩

@[simp]
theorem mk_eta {a b} (z : QuadraticAlgebra R a b) :
    mk z.re z.im = z := rfl

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

instance [Subsingleton R] : Subsingleton (QuadraticAlgebra R a b) := (equivProd a b).subsingleton

instance [Nontrivial R] : Nontrivial (QuadraticAlgebra R a b) := (equivProd a b).nontrivial

section Zero
variable [Zero R]

/-- The natural function `R → QuadraticAlgebra R a b`.

Note that, if `R` is a ring, you should use `algebraMap` instead of `C`. -/
protected def C (x : R) : QuadraticAlgebra R a b := ⟨x, 0⟩

@[deprecated (since := "2025-12-15")] alias coe := QuadraticAlgebra.C

@[simp]
theorem re_C : (.C r : QuadraticAlgebra R a b).re = r := rfl

@[deprecated (since := "2025-12-15")] alias re_coe := re_C

@[simp]
theorem im_C : (.C r : QuadraticAlgebra R a b).im = 0 := rfl

@[deprecated (since := "2025-12-15")] alias im_coe := im_C

theorem C_injective : Function.Injective (.C : R → QuadraticAlgebra R a b) :=
  fun _ _ h => congr_arg re h

@[deprecated (since := "2025-12-15")] alias coe_injective := C_injective

@[simp]
theorem C_inj {x y : R} : (.C x : QuadraticAlgebra R a b) = .C y ↔ x = y :=
  C_injective.eq_iff

@[deprecated (since := "2025-12-15")] alias coe_inj := C_inj

instance : Zero (QuadraticAlgebra R a b) := ⟨⟨0, 0⟩⟩

@[simp] theorem re_zero : (0 : QuadraticAlgebra R a b).re = 0 := rfl

@[simp] theorem im_zero : (0 : QuadraticAlgebra R a b).im = 0 := rfl

@[simp]
theorem C_zero : (.C 0 : QuadraticAlgebra R a b) = 0 := rfl

@[deprecated (since := "2025-12-15")] alias coe_zero := C_zero

@[simp]
theorem C_eq_zero_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 0 ↔ r = 0 := by
  rw [← C_zero, C_inj]

@[deprecated (since := "2025-12-15")] alias coe_eq_zero_iff := C_eq_zero_iff

instance : Inhabited (QuadraticAlgebra R a b) := ⟨0⟩

section One
variable [One R]

instance : One (QuadraticAlgebra R a b) := ⟨⟨1, 0⟩⟩

@[scoped simp] theorem re_one : (1 : QuadraticAlgebra R a b).re = 1 := rfl

@[scoped simp] theorem im_one : (1 : QuadraticAlgebra R a b).im = 0 := rfl

@[simp]
theorem C_one : (.C 1 : QuadraticAlgebra R a b) = 1 := rfl

@[deprecated (since := "2025-12-15")] alias coe_one := C_one

@[simp]
theorem C_eq_one_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 1 ↔ r = 1 := by
  rw [← C_one, C_inj]

@[deprecated (since := "2025-12-15")] alias coe_eq_one_iff := C_eq_one_iff

end One

end Zero

section Add
variable [Add R]

instance : Add (QuadraticAlgebra R a b) where
  add z w := ⟨z.re + w.re, z.im + w.im⟩

@[simp] theorem re_add (z w : QuadraticAlgebra R a b) :
    (z + w).re = z.re + w.re := rfl

@[simp] theorem im_add (z w : QuadraticAlgebra R a b) :
    (z + w).im = z.im + w.im := rfl

@[simp]
theorem mk_add_mk (z w : QuadraticAlgebra R a b) :
    mk z.re z.im + mk w.re w.im = (mk (z.re + w.re) (z.im + w.im) : QuadraticAlgebra R a b) := rfl

end Add

section AddZeroClass
variable [AddZeroClass R]

@[simp]
theorem C_add (x y : R) : (.C (x + y) : QuadraticAlgebra R a b) = .C x + .C y := by
  ext <;> simp

@[deprecated (since := "2025-12-15")] alias coe_add := C_add

end AddZeroClass

section Neg
variable [Neg R]

instance : Neg (QuadraticAlgebra R a b) where neg z := ⟨-z.re, -z.im⟩

@[simp] theorem re_neg (z : QuadraticAlgebra R a b) : (-z).re = -z.re := rfl

@[simp] theorem im_neg (z : QuadraticAlgebra R a b) : (-z).im = -z.im := rfl

@[simp]
theorem neg_mk (x y : R) :
    - (mk x y : QuadraticAlgebra R a b) = ⟨-x, -y⟩ := rfl

end Neg

section AddGroup

@[simp]
theorem C_neg [NegZeroClass R] (x : R) : (.C (-x) : QuadraticAlgebra R a b) = -.C x := by
  ext <;> simp

@[deprecated (since := "2025-12-15")] alias coe_neg := C_neg

instance [Sub R] : Sub (QuadraticAlgebra R a b) where
  sub z w := ⟨z.re - w.re, z.im - w.im⟩

@[simp] theorem re_sub [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).re = z.re - w.re := rfl

@[simp] theorem im_sub [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).im = z.im - w.im := rfl

@[simp]
theorem mk_sub_mk [Sub R] (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) - mk x2 y2 = mk (x1 - x2) (y1 - y2) := rfl

@[simp]
theorem C_sub (r1 r2 : R) [SubNegZeroMonoid R] :
    (.C (r1 - r2) : QuadraticAlgebra R a b) = .C r1 - .C r2 :=
  QuadraticAlgebra.ext rfl zero_sub_zero.symm

@[deprecated (since := "2025-12-15")] alias coe_sub := C_sub

end AddGroup

section Mul
variable [Mul R] [Add R]

instance : Mul (QuadraticAlgebra R a b) where
  mul z w := ⟨z.1 * w.1 + a * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + b * z.2 * w.2⟩

@[simp] theorem re_mul (z w : QuadraticAlgebra R a b) :
    (z * w).re = z.re * w.re + a * z.im * w.im := rfl

@[simp] theorem im_mul (z w : QuadraticAlgebra R a b) :
    (z * w).im = z.re * w.im + z.im * w.re + b * z.im * w.im := rfl

@[simp]
theorem mk_mul_mk (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) * mk x2 y2 =
    mk (x1 * x2 + a * y1 * y2) (x1 * y2 + y1 * x2 + b * y1 * y2) := rfl

end Mul

section SMul
variable [SMul S R] [SMul T R] (s : S)

instance : SMul S (QuadraticAlgebra R a b) where smul s z := ⟨s • z.re, s • z.im⟩

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T (QuadraticAlgebra R a b) where
  smul_assoc s t z := by ext <;> exact smul_assoc _ _ _

instance [SMulCommClass S T R] : SMulCommClass S T (QuadraticAlgebra R a b) where
  smul_comm s t z := by ext <;> exact smul_comm _ _ _

instance [SMul Sᵐᵒᵖ R] [IsCentralScalar S R] : IsCentralScalar S (QuadraticAlgebra R a b) where
  op_smul_eq_smul s z := by ext <;> exact op_smul_eq_smul _ _

@[simp] theorem re_smul (s : S) (z : QuadraticAlgebra R a b) : (s • z).re = s • z.re := rfl

@[simp] theorem im_smul (s : S) (z : QuadraticAlgebra R a b) : (s • z).im = s • z.im := rfl

@[simp]
theorem smul_mk (s : S) (x y : R) :
    s • (mk x y : QuadraticAlgebra R a b) = mk (s • x) (s • y) := rfl

end SMul

section MulAction

instance [Monoid S] [MulAction S R] : MulAction S (QuadraticAlgebra R a b) where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp [mul_smul]

end MulAction

@[simp]
theorem C_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (.C (s • r) : QuadraticAlgebra R a b) = s • .C r :=
  QuadraticAlgebra.ext rfl (smul_zero _).symm

@[deprecated (since := "2025-12-15")] alias coe_smul := C_smul

instance [AddMonoid R] : AddMonoid (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addMonoid _ rfl ?_ ?_ <;> intros <;> rfl

instance [Monoid S] [AddMonoid R] [DistribMulAction S R] :
    DistribMulAction S (QuadraticAlgebra R a b) where
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp

instance [AddCommMonoid R] : AddCommMonoid (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addCommMonoid _ rfl ?_ ?_ <;> intros <;> rfl

instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S (QuadraticAlgebra R a b) where
  add_smul r s x := by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

instance [AddGroup R] : AddGroup (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addGroup _ rfl ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

instance [AddCommGroup R] : AddCommGroup (QuadraticAlgebra R a b) where

section AddCommMonoidWithOne
variable [AddCommMonoidWithOne R]

instance : AddCommMonoidWithOne (QuadraticAlgebra R a b) where
  natCast n := .C n
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp

@[simp]
theorem C_ofNat (n : ℕ) [n.AtLeastTwo] :
    (.C (ofNat(n) : R) : QuadraticAlgebra R a b) = ofNat(n) := by
  ext <;> rfl

@[deprecated (since := "2025-12-15")] alias coe_ofNat := C_ofNat

@[simp, norm_cast]
theorem re_natCast (n : ℕ) : (n : QuadraticAlgebra R a b).re = n := rfl

@[simp, norm_cast]
theorem im_natCast (n : ℕ) : (n : QuadraticAlgebra R a b).im = 0 := rfl

theorem C_natCast (n : ℕ) : .C (n : R) = (↑n : QuadraticAlgebra R a b) := rfl

@[deprecated (since := "2025-12-15")] alias coe_natCast := C_natCast

@[scoped simp]
theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).re = ofNat(n) := rfl

@[scoped simp]
theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).im = 0 := rfl

end AddCommMonoidWithOne

section AddCommGroupWithOne
variable [AddCommGroupWithOne R]

instance : AddCommGroupWithOne (QuadraticAlgebra R a b) where
  intCast n := .C n
  intCast_ofNat n := by norm_cast
  intCast_negSucc n := by rw [Int.negSucc_eq, Int.cast_neg, C_neg]; norm_cast

@[simp, norm_cast]
theorem re_intCast (n : ℤ) : (n : QuadraticAlgebra R a b).re = n := rfl

@[simp, norm_cast]
theorem im_intCast (n : ℤ) : (n : QuadraticAlgebra R a b).im = 0 := rfl

theorem C_intCast (n : ℤ) : .C (n : R) = (n : QuadraticAlgebra R a b) := rfl

@[deprecated (since := "2025-12-15")] alias coe_intCast := C_intCast

end AddCommGroupWithOne

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (QuadraticAlgebra R a b) where
  left_distrib _ _ _ := by ext <;> simpa using by simp [mul_add]; abel
  right_distrib _ _ _ := by ext <;> simpa using by simp [mul_add, add_mul]; abel
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp

theorem C_mul_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (.C r * x : QuadraticAlgebra R a b) = r • x := by
  ext <;> simp

@[deprecated (since := "2025-12-15")] alias coe_mul_eq_smul := C_mul_eq_smul

@[simp]
theorem C_mul (x y : R) : .C (x * y) = (.C x * .C y : QuadraticAlgebra R a b) := by
  ext <;> simp

@[deprecated (since := "2025-12-15")] alias coe_mul := C_mul

end NonUnitalNonAssocSemiring

section NonAssocSemiring
variable [NonAssocSemiring R]

instance instNonAssocSemiring : NonAssocSemiring (QuadraticAlgebra R a b) where
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

@[simp]
theorem nsmul_mk (n : ℕ) (x y : R) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

end NonAssocSemiring

section Semiring
variable (a b) [Semiring R]

/-- `QuadraticAlgebra.re` as a `LinearMap` -/
@[simps]
def reₗ : QuadraticAlgebra R a b →ₗ[R] R where
  toFun := re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuadraticAlgebra.im` as a `LinearMap` -/
@[simps]
def imₗ : QuadraticAlgebra R a b →ₗ[R] R where
  toFun := im
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuadraticAlgebra.equivTuple` as a `LinearEquiv` -/
def linearEquivTuple : QuadraticAlgebra R a b ≃ₗ[R] (Fin 2 → R) where
  __ := equivProd a b |>.trans <| finTwoArrowEquiv _ |>.symm
  map_add' _ _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  map_smul' _ _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩

@[simp]
lemma linearEquivTuple_apply (z : QuadraticAlgebra R a b) :
    (linearEquivTuple a b) z = ![z.re, z.im] := rfl

@[simp]
lemma linearEquivTuple_symm_apply (x : Fin 2 → R) :
    (linearEquivTuple a b).symm x = ⟨x 0, x 1⟩ := rfl

/-- `QuadraticAlgebra R a b` has a basis over `R` given by `1` and `i` -/
noncomputable def basis : Module.Basis (Fin 2) R (QuadraticAlgebra R a b) :=
  .ofEquivFun <| linearEquivTuple a b

@[simp]
theorem basis_repr_apply (x : QuadraticAlgebra R a b) :
    (basis a b).repr x = ![x.re, x.im] := rfl

instance : Module.Finite R (QuadraticAlgebra R a b) := .of_basis (basis a b)

instance : Module.Free R (QuadraticAlgebra R a b) := .of_basis (basis a b)

theorem rank_eq_two [StrongRankCondition R] : Module.rank R (QuadraticAlgebra R a b) = 2 := by
  simp [rank_eq_card_basis (basis a b)]

theorem finrank_eq_two [StrongRankCondition R] :
    Module.finrank R (QuadraticAlgebra R a b) = 2 := by
  simp [Module.finrank, rank_eq_two]

end Semiring

section CommSemiring
variable [CommSemiring R]

instance instCommSemiring : CommSemiring (QuadraticAlgebra R a b) where
  mul_assoc _ _ _ := by ext <;> simpa using by ring
  mul_comm _ _ := by ext <;> simpa using by ring

instance [CommSemiring S] [CommSemiring R] [Algebra S R] :
    Algebra S (QuadraticAlgebra R a b) where
  algebraMap.toFun s := .C (algebraMap S R s)
  algebraMap.map_one' := by ext <;> simp
  algebraMap.map_mul' x y:= by ext <;> simp
  algebraMap.map_zero' := by ext <;> simp
  algebraMap.map_add' x y:= by ext <;> simp
  commutes' s z := by ext <;> simp [Algebra.commutes]
  smul_def' s x := by ext <;> simp [Algebra.smul_def]

theorem algebraMap_eq (r : R) : algebraMap R (QuadraticAlgebra R a b) r = ⟨r, 0⟩ := rfl

theorem algebraMap_injective : (algebraMap R (QuadraticAlgebra R a b) : _ → _).Injective :=
  fun _ _ ↦ by simp [algebraMap_eq]

@[simp]
theorem algebraMap_inj {x y : R} :
    algebraMap R (QuadraticAlgebra R a b) x = algebraMap _ _ y ↔ x = y :=
  algebraMap_injective.eq_iff

@[simp]
theorem algebraMap_re : (algebraMap R (QuadraticAlgebra R a b) r).re = r := rfl

@[simp]
theorem algebraMap_im : (algebraMap R (QuadraticAlgebra R a b) r).im = 0 := rfl

instance [Zero S] [SMulWithZero S R] [NoZeroSMulDivisors S R] :
    NoZeroSMulDivisors S (QuadraticAlgebra R a b) :=
  ⟨by simp [QuadraticAlgebra.ext_iff, or_and_left]⟩

@[simp]
theorem C_pow (n : ℕ) (r : R) : (.C (r ^ n : R) : QuadraticAlgebra R a b) = (.C r) ^ n :=
  (algebraMap R (QuadraticAlgebra R a b)).map_pow r n

@[deprecated (since := "2025-12-15")] alias coe_pow := C_pow

theorem mul_C_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (x * .C r : QuadraticAlgebra R a b) = r • x := by
  rw [mul_comm, C_mul_eq_smul r x]

@[deprecated (since := "2025-12-15")] alias mul_coe_eq_smul := mul_C_eq_smul

@[simp]
theorem C_eq_algebraMap : QuadraticAlgebra.C = (algebraMap R (QuadraticAlgebra R a b)) := rfl

@[deprecated (since := "2025-12-15")] alias coe_algebraMap := C_eq_algebraMap

theorem smul_C (r1 r2 : R) :
    r1 • (.C r2 : QuadraticAlgebra R a b) = .C (r1 * r2) := by rw [C_mul, C_mul_eq_smul]

@[deprecated (since := "2025-12-15")] alias smul_coe := smul_C

theorem algebraMap_dvd_iff {r : R} {z : QuadraticAlgebra R a b} :
    (algebraMap R (QuadraticAlgebra R a b) r) ∣ z ↔ r ∣ z.re ∧ r ∣ z.im := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [dvd_mul_right, ← C_eq_algebraMap]
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    simp [QuadraticAlgebra.ext_iff, hr, hi, ← C_eq_algebraMap]

@[deprecated (since := "2025-12-15")] alias coe_dvd_iff := algebraMap_dvd_iff

@[simp]
theorem algebraMap_dvd_iff_dvd {z w : R} :
    algebraMap R (QuadraticAlgebra R a b) z ∣ algebraMap R (QuadraticAlgebra R a b) w ↔ z ∣ w := by
  rw [algebraMap_dvd_iff]
  constructor
  · rintro ⟨hx, -⟩
    simpa using hx
  · simp [← C_eq_algebraMap]

@[deprecated (since := "2025-12-15")] alias coe_dvd_iff_dvd := algebraMap_dvd_iff_dvd

end CommSemiring

section CommRing

variable [CommRing R]

instance instCommRing : CommRing (QuadraticAlgebra R a b) where

instance [CharZero R] : CharZero (QuadraticAlgebra R a b) where
  cast_injective m n := by
    simp [QuadraticAlgebra.ext_iff]

@[simp]
theorem zsmul_val (n : ℤ) (x y : R) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

end CommRing

end QuadraticAlgebra
