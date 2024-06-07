/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Bichang Lei
-/
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Ideal.LocalRing

/-!
# Extension of Valuation

In this file, we define the typeclass for valuation extensions and prove basic facts about
extension of valuations. Let `A` be an `R` algebra, equipped with valuation `vA` and `vR`
respectively. Here, extension of valuation means that the pullback of valuation `vA` to `R` is
equivalent to the valuation `vR` on `R`. We only require equivalence, not equality of valuations here.

Note that we do not require the ring map from `R` to `A` to be injective. It holds automatically
when `R` is a division ring and `A` is nontrivial.

## Main Definition

* `IsValExtension vR vA` : The valuation `vA` on `A` is an extension of the valuation `vR` on `R`.

## References

* [Bourbaki, Nicolas. *Commutative algebra*] Chapter VI §3, Valuations.
* <https://en.wikipedia.org/wiki/Valuation_(algebra)#Extension_of_valuations>

## Tags
Valuation, Extension of Valuation

-/
open Valuation

/--
The class `IsValExtension R A` states that the valuation of `A` is an extension of the valuation
on `R`. More precisely, the valuation on `R` is equivlent to the comap of the valuation on `A`.
-/
class IsValExtension {R A ΓR ΓA : Type*} [CommRing R] [Ring A]
  [LinearOrderedCommMonoidWithZero ΓR] [LinearOrderedCommMonoidWithZero ΓA]
  [Algebra R A] (vR : Valuation R ΓR) (vA : Valuation A ΓA) : Prop where
  /-- The valuation on `R` is equivlent to the comap of the valuation on `A` -/
  val_isEquiv_comap : vR.IsEquiv <| vA.comap (algebraMap R A)

namespace IsValExtension

section CoeLemma

variable {R A ΓR ΓA: Type*} [CommRing R] [Ring A]
    [LinearOrderedCommMonoidWithZero ΓR] [LinearOrderedCommMonoidWithZero ΓA]
    [Algebra R A] (vR : Valuation R ΓR) (vA : Valuation A ΓA) [IsValExtension vR vA]

-- @[simp] does not work because `vR` cannot be inferred from `R`.
theorem val_map_le_iff (x y : R) : vA (algebraMap R A x) ≤ vA (algebraMap R A y) ↔ vR x ≤ vR y :=
  (IsEquiv.val_le val_isEquiv_comap).symm

theorem val_map_lt_iff (x y : R) : vA (algebraMap R A x) < vA (algebraMap R A y) ↔ vR x < vR y :=
  (IsEquiv.val_lt val_isEquiv_comap).symm

theorem val_map_eq_iff (x y : R) : vA (algebraMap R A x) = vA (algebraMap R A y) ↔ vR x = vR y :=
  (IsEquiv.val_eq val_isEquiv_comap).symm

theorem val_map_le_one_iff (x : R) : vA (algebraMap R A x) ≤ 1 ↔ vR x ≤ 1 :=
  (IsEquiv.val_le_one val_isEquiv_comap).symm

theorem val_map_lt_one_iff (x : R) : vA (algebraMap R A x) < 1 ↔ vR x < 1 :=
  (IsEquiv.val_lt_one val_isEquiv_comap).symm

theorem val_map_eq_one_iff (x : R) : vA (algebraMap R A x) = 1 ↔ vR x = 1 :=
  (IsEquiv.val_eq_one val_isEquiv_comap).symm

instance id : IsValExtension vR vR where
  val_isEquiv_comap := by
    simp only [Algebra.id.map_eq_id, comap_id]
    rfl

end CoeLemma

section mk'

/--
When `K` is a field, if the preimage of the valuation integers of `A` equals to the valuation
integers of `K`, then the valuation on `A` is an extension of valuation on `K`.
-/
theorem ofIntegerComap {K A ΓK ΓA : Type*} [Field K] [Ring A]
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra K A] (vK : Valuation K ΓK) (vA : Valuation A ΓA)
    (h : vA.integer.comap (algebraMap K A) = vK.integer) : IsValExtension vK vA where
  val_isEquiv_comap := by
    rw [isEquiv_iff_val_le_one]
    intro x
    rw [← Valuation.mem_integer_iff, ← Valuation.mem_integer_iff]
    rw [← h]
    rfl

end mk'

section integer

variable {R A ΓR ΓA : Type*} [CommRing R] [Ring A]
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
    [Algebra R A] {vR : Valuation R ΓR} {vA : Valuation A ΓA} [IsValExtension vR vA]

instance integerAlgebra : Algebra vR.integer vA.integer where
    smul r a := {
      val := r • a,
      property := by
        rw [Valuation.mem_integer_iff,
          show r • ↑a = algebraMap R A r * a by exact (Algebra.smul_def r (a : A))]
        norm_num
        apply mul_le_one'
        · rw [val_map_le_one_iff vR]
          exact r.2
        · exact a.2
    }
    toFun r := {
      val := algebraMap R A r,
      property := by
        simp only [Valuation.mem_integer_iff]
        rw [val_map_le_one_iff vR]
        exact r.2
    }
    map_one' := by
      ext
      simp
    map_mul' _ _ := by
      ext
      simp
    map_zero' := by
      ext
      simp
    map_add' _ _ := by
      ext
      simp
    commutes' _ _ := by
      ext
      exact Algebra.commutes _ _
    smul_def' _ _ := by
      ext
      exact Algebra.smul_def _ _

@[simp, norm_cast]
theorem coe_algebraMap_integer (r : vR.integer) :
    ((algebraMap vR.integer vA.integer) r : A) = (algebraMap R A) (r : R) := by
  rfl

instance instIsScalarTowerInteger : IsScalarTower vR.integer vA.integer A where
  smul_assoc x y z := by
    simp only [Algebra.smul_def]
    exact mul_assoc _ _ _

theorem integerAlgebra_injective {K A ΓK ΓA : Type*} [Field K] [Ring A] [Nontrivial A]
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓA]
    [Algebra K A] (vK : Valuation K ΓK) (vA : Valuation A ΓA) [IsValExtension vK vA] : Function.Injective (algebraMap vK.integer vA.integer) := by
  intro x y h
  simp only [Subtype.ext_iff, coe_algebraMap_integer] at h
  ext
  apply RingHom.injective (algebraMap K A) h

instance instIsLocalRingHomValuationInteger {K L ΓK ΓL : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    [Algebra K L] {vK : Valuation K ΓK} {vL : Valuation L ΓL} [IsValExtension vK vL] :
    IsLocalRingHom (algebraMap vK.integer vL.integer) where
  map_nonunit r hr := by
    by_cases h : r = 0
    · simp [h] at hr
    · apply Valuation.Integers.isUnit_of_one (v := vK)
      · exact Valuation.integer.integers (v := vK)
      · simp only [isUnit_iff_ne_zero, ne_eq]
        exact Subtype.ext_iff.not.mp h
      · apply Valuation.Integers.one_of_isUnit (Valuation.integer.integers (v := vL)) at hr
        change vL (((algebraMap vK.integer vL.integer) r) : L) = 1 at hr
        norm_cast at hr
        rw [val_map_eq_one_iff vK] at hr
        exact hr

end integer

end IsValExtension
