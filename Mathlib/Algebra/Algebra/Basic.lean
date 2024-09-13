/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Int.CharZero

/-!
# Further basic results about `Algebra`.

This file could usefully be split further.
-/

universe u v w u₁ v₁

namespace Algebra

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

section Semiring

variable [CommSemiring R] [CommSemiring S]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

section PUnit

instance _root_.PUnit.algebra : Algebra R PUnit.{v + 1} where
  toFun _ := PUnit.unit
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ _ := rfl
  smul_def' _ _ := rfl

@[simp]
theorem algebraMap_pUnit (r : R) : algebraMap R PUnit r = PUnit.unit :=
  rfl

end PUnit

section ULift

instance _root_.ULift.algebra : Algebra R (ULift A) :=
  { ULift.module',
    (ULift.ringEquiv : ULift A ≃+* A).symm.toRingHom.comp (algebraMap R A) with
    toFun := fun r => ULift.up (algebraMap R A r)
    commutes' := fun r x => ULift.down_injective <| Algebra.commutes r x.down
    smul_def' := fun r x => ULift.down_injective <| Algebra.smul_def' r x.down }

theorem _root_.ULift.algebraMap_eq (r : R) :
    algebraMap R (ULift A) r = ULift.up (algebraMap R A r) :=
  rfl

@[simp]
theorem _root_.ULift.down_algebraMap (r : R) : (algebraMap R (ULift A) r).down = algebraMap R A r :=
  rfl

end ULift

/-- Algebra over a subsemiring. This builds upon `Subsemiring.module`. -/
instance ofSubsemiring (S : Subsemiring R) : Algebra S A where
  toRingHom := (algebraMap R A).comp S.subtype
  smul := (· • ·)
  commutes' r x := Algebra.commutes (r : R) x
  smul_def' r x := Algebra.smul_def (r : R) x

theorem algebraMap_ofSubsemiring (S : Subsemiring R) :
    (algebraMap S R : S →+* R) = Subsemiring.subtype S :=
  rfl

theorem coe_algebraMap_ofSubsemiring (S : Subsemiring R) : (algebraMap S R : S → R) = Subtype.val :=
  rfl

theorem algebraMap_ofSubsemiring_apply (S : Subsemiring R) (x : S) : algebraMap S R x = x :=
  rfl

/-- Algebra over a subring. This builds upon `Subring.module`. -/
instance ofSubring {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subring R) :
    Algebra S A where -- Porting note: don't use `toSubsemiring` because of a timeout
  toRingHom := (algebraMap R A).comp S.subtype
  smul := (· • ·)
  commutes' r x := Algebra.commutes (r : R) x
  smul_def' r x := Algebra.smul_def (r : R) x

theorem algebraMap_ofSubring {R : Type*} [CommRing R] (S : Subring R) :
    (algebraMap S R : S →+* R) = Subring.subtype S :=
  rfl

theorem coe_algebraMap_ofSubring {R : Type*} [CommRing R] (S : Subring R) :
    (algebraMap S R : S → R) = Subtype.val :=
  rfl

theorem algebraMap_ofSubring_apply {R : Type*} [CommRing R] (S : Subring R) (x : S) :
    algebraMap S R x = x :=
  rfl

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
def algebraMapSubmonoid (S : Type*) [Semiring S] [Algebra R S] (M : Submonoid R) : Submonoid S :=
  M.map (algebraMap R S)

theorem mem_algebraMapSubmonoid_of_mem {S : Type*} [Semiring S] [Algebra R S] {M : Submonoid R}
    (x : M) : algebraMap R S x ∈ algebraMapSubmonoid S M :=
  Set.mem_image_of_mem (algebraMap R S) x.2

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem mul_sub_algebraMap_commutes [Ring A] [Algebra R A] (x : A) (r : R) :
    x * (x - algebraMap R A r) = (x - algebraMap R A r) * x := by rw [mul_sub, ← commutes, sub_mul]

theorem mul_sub_algebraMap_pow_commutes [Ring A] [Algebra R A] (x : A) (r : R) (n : ℕ) :
    x * (x - algebraMap R A r) ^ n = (x - algebraMap R A r) ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, mul_sub_algebraMap_commutes, mul_assoc, ih, ← mul_assoc]

end CommSemiring

section Ring

variable [CommRing R]
variable (R)

/-- A `Semiring` that is an `Algebra` over a commutative ring carries a natural `Ring` structure.
See note [reducible non-instances]. -/
abbrev semiringToRing [Semiring A] [Algebra R A] : Ring A :=
  { __ := (inferInstance : Semiring A)
    __ := Module.addCommMonoidToAddCommGroup R
    intCast := fun z => algebraMap R A z
    intCast_ofNat := fun z => by simp only [Int.cast_natCast, map_natCast]
    intCast_negSucc := fun z => by simp }

end Ring

end Algebra

open scoped Algebra

namespace Module

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommSemiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
variable [SMulCommClass S R M] [SMul R S] [IsScalarTower R S M]

instance End.instAlgebra : Algebra R (Module.End S M) :=
  Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm

-- to prove this is a special case of the above
example : Algebra R (Module.End R M) := End.instAlgebra _ _ _

theorem algebraMap_end_eq_smul_id (a : R) : algebraMap R (End S M) a = a • LinearMap.id :=
  rfl

@[simp]
theorem algebraMap_end_apply (a : R) (m : M) : algebraMap R (End S M) a m = a • m :=
  rfl

@[simp]
theorem ker_algebraMap_end (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V] (a : K)
    (ha : a ≠ 0) : LinearMap.ker ((algebraMap K (End K V)) a) = ⊥ :=
  LinearMap.ker_smul _ _ ha

section

variable {R M}

theorem End_algebraMap_isUnit_inv_apply_eq_iff {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    (↑(h.unit⁻¹) : Module.End S M) m = m' ↔ m = x • m' :=
  { mp := fun H => ((congr_arg h.unit H).symm.trans (End_isUnit_apply_inv_apply_of_isUnit h _)).symm
    mpr := fun H =>
      H.symm ▸ by
        apply_fun ⇑h.unit.val using ((Module.End_isUnit_iff _).mp h).injective
        erw [End_isUnit_apply_inv_apply_of_isUnit]
        rfl }

theorem End_algebraMap_isUnit_inv_apply_eq_iff' {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    m' = (↑h.unit⁻¹ : Module.End S M) m ↔ m = x • m' :=
  { mp := fun H => ((congr_arg h.unit H).trans (End_isUnit_apply_inv_apply_of_isUnit h _)).symm
    mpr := fun H =>
      H.symm ▸ by
        apply_fun (↑h.unit : M → M) using ((Module.End_isUnit_iff _).mp h).injective
        erw [End_isUnit_apply_inv_apply_of_isUnit]
        rfl }

end

end Module

namespace LinearMap

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/-- An alternate statement of `LinearMap.map_smul` for when `algebraMap` is more convenient to
work with than `•`. -/
theorem map_algebraMap_mul (f : A →ₗ[R] B) (a : A) (r : R) :
    f (algebraMap R A r * a) = algebraMap R B r * f a := by
  rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul]

theorem map_mul_algebraMap (f : A →ₗ[R] B) (a : A) (r : R) :
    f (a * algebraMap R A r) = f a * algebraMap R B r := by
  rw [← Algebra.commutes, ← Algebra.commutes, map_algebraMap_mul]

end LinearMap

section Nat

variable {R : Type*} [Semiring R]

-- Lower the priority so that `Algebra.id` is picked most of the time when working with
-- `ℕ`-algebras.
-- TODO: is this still needed?
/-- Semiring ⥤ ℕ-Alg -/
instance (priority := 99) Semiring.toNatAlgebra : Algebra ℕ R where
  commutes' := Nat.cast_commute
  smul_def' _ _ := nsmul_eq_mul _ _
  toRingHom := Nat.castRingHom R

instance nat_algebra_subsingleton : Subsingleton (Algebra ℕ R) :=
  ⟨fun P Q => by ext; simp⟩

end Nat

section Int

variable (R : Type*) [Ring R]

-- Lower the priority so that `Algebra.id` is picked most of the time when working with
-- `ℤ`-algebras.
-- TODO: is this still needed?
/-- Ring ⥤ ℤ-Alg -/
instance (priority := 99) Ring.toIntAlgebra : Algebra ℤ R where
  commutes' := Int.cast_commute
  smul_def' _ _ := zsmul_eq_mul _ _
  toRingHom := Int.castRingHom R

/-- A special case of `eq_intCast'` that happens to be true definitionally -/
@[simp]
theorem algebraMap_int_eq : algebraMap ℤ R = Int.castRingHom R :=
  rfl

variable {R}

instance int_algebra_subsingleton : Subsingleton (Algebra ℤ R) :=
  ⟨fun P Q => Algebra.algebra_ext P Q <| RingHom.congr_fun <| Subsingleton.elim _ _⟩

end Int

namespace NoZeroSMulDivisors

variable {R A : Type*}

open Algebra

/-- If `algebraMap R A` is injective and `A` has no zero divisors,
`R`-multiples in `A` are zero only if one of the factors is zero.

Cannot be an instance because there is no `Injective (algebraMap R A)` typeclass.
-/
theorem of_algebraMap_injective [CommSemiring R] [Semiring A] [Algebra R A] [NoZeroDivisors A]
    (h : Function.Injective (algebraMap R A)) : NoZeroSMulDivisors R A :=
  ⟨fun hcx => (mul_eq_zero.mp ((smul_def _ _).symm.trans hcx)).imp_left
    (map_eq_zero_iff (algebraMap R A) h).mp⟩

variable (R A)

theorem algebraMap_injective [CommRing R] [Ring A] [Nontrivial A] [Algebra R A]
    [NoZeroSMulDivisors R A] : Function.Injective (algebraMap R A) := by
  simpa only [algebraMap_eq_smul_one'] using smul_left_injective R one_ne_zero

@[simp]
lemma algebraMap_eq_zero_iff [CommRing R] [Ring A] [Nontrivial A] [Algebra R A]
    [NoZeroSMulDivisors R A] {r : R} : algebraMap R A r = 0 ↔ r = 0 :=
  map_eq_zero_iff _ <| algebraMap_injective R A

@[simp]
lemma algebraMap_eq_one_iff [CommRing R] [Ring A] [Nontrivial A] [Algebra R A]
    [NoZeroSMulDivisors R A] {r : R} : algebraMap R A r = 1 ↔ r = 1 :=
  map_eq_one_iff _ <| algebraMap_injective R A

theorem _root_.NeZero.of_noZeroSMulDivisors (n : ℕ) [CommRing R] [NeZero (n : R)] [Ring A]
    [Nontrivial A] [Algebra R A] [NoZeroSMulDivisors R A] : NeZero (n : A) :=
  NeZero.nat_of_injective <| NoZeroSMulDivisors.algebraMap_injective R A

variable {R A}

theorem iff_algebraMap_injective [CommRing R] [Ring A] [IsDomain A] [Algebra R A] :
    NoZeroSMulDivisors R A ↔ Function.Injective (algebraMap R A) :=
  ⟨@NoZeroSMulDivisors.algebraMap_injective R A _ _ _ _, NoZeroSMulDivisors.of_algebraMap_injective⟩

-- see note [lower instance priority]
instance (priority := 100) CharZero.noZeroSMulDivisors_nat [Semiring R] [NoZeroDivisors R]
    [CharZero R] : NoZeroSMulDivisors ℕ R :=
  NoZeroSMulDivisors.of_algebraMap_injective <| (algebraMap ℕ R).injective_nat

-- see note [lower instance priority]
instance (priority := 100) CharZero.noZeroSMulDivisors_int [Ring R] [NoZeroDivisors R]
    [CharZero R] : NoZeroSMulDivisors ℤ R :=
  NoZeroSMulDivisors.of_algebraMap_injective <| (algebraMap ℤ R).injective_int

section Field

variable [Field R] [Semiring A] [Algebra R A]

-- see note [lower instance priority]
instance (priority := 100) Algebra.noZeroSMulDivisors [Nontrivial A] [NoZeroDivisors A] :
    NoZeroSMulDivisors R A :=
  NoZeroSMulDivisors.of_algebraMap_injective (algebraMap R A).injective

end Field

end NoZeroSMulDivisors

section IsScalarTower

variable {R : Type*} [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
variable {N : Type*} [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A N]

theorem algebra_compatible_smul (r : R) (m : M) : r • m = (algebraMap R A) r • m := by
  rw [← one_smul A m, ← smul_assoc, Algebra.smul_def, mul_one, one_smul]

@[simp]
theorem algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • m = r • m :=
  (algebra_compatible_smul A r m).symm

theorem NoZeroSMulDivisors.trans (R A M : Type*) [CommRing R] [Ring A] [IsDomain A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [NoZeroSMulDivisors R A]
    [NoZeroSMulDivisors A M] : NoZeroSMulDivisors R M := by
  refine ⟨fun {r m} h => ?_⟩
  rw [algebra_compatible_smul A r m] at h
  rcases smul_eq_zero.1 h with H | H
  · have : Function.Injective (algebraMap R A) :=
      NoZeroSMulDivisors.iff_algebraMap_injective.1 inferInstance
    left
    exact (injective_iff_map_eq_zero _).1 this _ H
  · right
    exact H

variable {A}

-- see Note [lower instance priority]
-- priority manually adjusted in #11980, as it is a very common path
instance (priority := 120) IsScalarTower.to_smulCommClass : SMulCommClass R A M :=
  ⟨fun r a m => by
    rw [algebra_compatible_smul A r (a • m), smul_smul, Algebra.commutes, mul_smul, ←
      algebra_compatible_smul]⟩

-- see Note [lower instance priority]
-- priority manually adjusted in #11980, as it is a very common path
instance (priority := 110) IsScalarTower.to_smulCommClass' : SMulCommClass A R M :=
  SMulCommClass.symm _ _ _

-- see Note [lower instance priority]
instance (priority := 200) Algebra.to_smulCommClass {R A} [CommSemiring R] [Semiring A]
    [Algebra R A] : SMulCommClass R A A :=
  IsScalarTower.to_smulCommClass

theorem smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
  smul_comm _ _ _

namespace LinearMap

variable (R)

-- Porting note (#11215): TODO: generalize to `CompatibleSMul`
/-- `A`-linearly coerce an `R`-linear map from `M` to `A` to a function, given an algebra `A` over
a commutative semiring `R` and `M` a module over `R`. -/
def ltoFun (R : Type u) (M : Type v) (A : Type w) [CommSemiring R] [AddCommMonoid M] [Module R M]
    [CommSemiring A] [Algebra R A] : (M →ₗ[R] A) →ₗ[A] M → A where
  toFun f := f.toFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LinearMap

end IsScalarTower

/-! TODO: The following lemmas no longer involve `Algebra` at all, and could be moved closer
to `Algebra/Module/Submodule.lean`. Currently this is tricky because `ker`, `range`, `⊤`, and `⊥`
are all defined in `LinearAlgebra/Basic.lean`. -/

section Module

variable (R : Type*) {S M N : Type*} [Semiring R] [Semiring S] [SMul R S]
variable [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

@[simp]
theorem LinearMap.ker_restrictScalars (f : M →ₗ[S] N) :
    LinearMap.ker (f.restrictScalars R) = f.ker.restrictScalars R :=
  rfl

end Module

example {R A} [CommSemiring R] [Semiring A] [Module R A] [SMulCommClass R A A]
    [IsScalarTower R A A] : Algebra R A :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

section invertibility

variable {R A B : Type*}
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- If there is a linear map `f : A →ₗ[R] B` that preserves `1`, then `algebraMap R B r` is
invertible when `algebraMap R A r` is. -/
abbrev Invertible.algebraMapOfInvertibleAlgebraMap (f : A →ₗ[R] B) (hf : f 1 = 1) {r : R}
    (h : Invertible (algebraMap R A r)) : Invertible (algebraMap R B r) where
  invOf := f ⅟(algebraMap R A r)
  invOf_mul_self := by rw [← Algebra.commutes, ← Algebra.smul_def, ← map_smul, Algebra.smul_def,
    mul_invOf_self, hf]
  mul_invOf_self := by rw [← Algebra.smul_def, ← map_smul, Algebra.smul_def, mul_invOf_self, hf]

/-- If there is a linear map `f : A →ₗ[R] B` that preserves `1`, then `algebraMap R B r` is
a unit when `algebraMap R A r` is. -/
lemma IsUnit.algebraMap_of_algebraMap (f : A →ₗ[R] B) (hf : f 1 = 1) {r : R}
    (h : IsUnit (algebraMap R A r)) : IsUnit (algebraMap R B r) :=
  let ⟨i⟩ := nonempty_invertible h
  letI := Invertible.algebraMapOfInvertibleAlgebraMap f hf i
  isUnit_of_invertible _

end invertibility

section algebraMap

variable {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E] (b : F →ₗ[F] E)

/-- If `E` is an `F`-algebra, and there exists an injective `F`-linear map from `F` to `E`,
then the algebra map from `F` to `E` is also injective. -/
theorem injective_algebraMap_of_linearMap (hb : Function.Injective b) :
    Function.Injective (algebraMap F E) := fun x y e ↦ hb <| by
  rw [← mul_one x, ← mul_one y, ← smul_eq_mul, ← smul_eq_mul,
    map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, e]

/-- If `E` is an `F`-algebra, and there exists a surjective `F`-linear map from `F` to `E`,
then the algebra map from `F` to `E` is also surjective. -/
theorem surjective_algebraMap_of_linearMap (hb : Function.Surjective b) :
    Function.Surjective (algebraMap F E) := fun x ↦ by
  obtain ⟨x, rfl⟩ := hb x
  obtain ⟨y, hy⟩ := hb (b 1 * b 1)
  refine ⟨x * y, ?_⟩
  obtain ⟨z, hz⟩ := hb 1
  apply_fun (x • z • ·) at hy
  rwa [← map_smul, smul_eq_mul, mul_comm, ← smul_mul_assoc, ← map_smul _ z, smul_eq_mul, mul_one,
    ← smul_eq_mul, map_smul, hz, one_mul, ← map_smul, smul_eq_mul, mul_one, smul_smul,
    ← Algebra.algebraMap_eq_smul_one] at hy

/-- If `E` is an `F`-algebra, and there exists a bijective `F`-linear map from `F` to `E`,
then the algebra map from `F` to `E` is also bijective.

NOTE: The same result can also be obtained if there are two `F`-linear maps from `F` to `E`,
one is injective, the other one is surjective. In this case, use
`injective_algebraMap_of_linearMap` and `surjective_algebraMap_of_linearMap` separately. -/
theorem bijective_algebraMap_of_linearMap (hb : Function.Bijective b) :
    Function.Bijective (algebraMap F E) :=
  ⟨injective_algebraMap_of_linearMap b hb.1, surjective_algebraMap_of_linearMap b hb.2⟩

/-- If `E` is an `F`-algebra, there exists an `F`-linear isomorphism from `F` to `E` (namely,
`E` is a free `F`-module of rank one), then the algebra map from `F` to `E` is bijective. -/
theorem bijective_algebraMap_of_linearEquiv (b : F ≃ₗ[F] E) :
    Function.Bijective (algebraMap F E) :=
  bijective_algebraMap_of_linearMap _ b.bijective

end algebraMap

section surjective

variable {R S} [CommSemiring R] [Semiring S] [Algebra R S]
variable {M N} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S M] [IsScalarTower R S M]
variable [Module R N] [Module S N] [IsScalarTower R S N]

/-- If `R →+* S` is surjective, then `S`-linear maps between modules are exactly `R`-linear maps. -/
def LinearMap.extendScalarsOfSurjectiveEquiv (h : Function.Surjective (algebraMap R S)) :
    (M →ₗ[R] N) ≃ₗ[R] (M →ₗ[S] N) where
  toFun f := { __ := f, map_smul' := fun r x ↦ by obtain ⟨r, rfl⟩ := h r; simp }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f.restrictScalars S
  left_inv f := rfl
  right_inv f := rfl

/-- If `R →+* S` is surjective, then `R`-linear maps are also `S`-linear. -/
abbrev LinearMap.extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S))
    (l : M →ₗ[R] N) : M →ₗ[S] N :=
  extendScalarsOfSurjectiveEquiv h l

/-- If `R →+* S` is surjective, then `R`-linear isomorphisms are also `S`-linear. -/
def LinearEquiv.extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S))
    (f : M ≃ₗ[R] N) : M ≃ₗ[S] N where
  __ := f
  map_smul' r x := by obtain ⟨r, rfl⟩ := h r; simp

variable (h : Function.Surjective (algebraMap R S))

@[simp]
lemma LinearMap.extendScalarsOfSurjective_apply (l : M →ₗ[R] N) (x) :
    l.extendScalarsOfSurjective h x = l x := rfl

@[simp]
lemma LinearEquiv.extendScalarsOfSurjective_apply (f : M ≃ₗ[R] N) (x) :
    f.extendScalarsOfSurjective h x = f x := rfl

@[simp]
lemma LinearEquiv.extendScalarsOfSurjective_symm (f : M ≃ₗ[R] N) :
    (f.extendScalarsOfSurjective h).symm = f.symm.extendScalarsOfSurjective h := rfl

end surjective
