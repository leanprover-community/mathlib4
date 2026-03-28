/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
module

public import Mathlib.Algebra.Order.Group.Cone
public import Mathlib.Algebra.Ring.Subsemiring.Order

/-!
# Construct ordered rings from rings with a specified positive cone.

We demonstrate the equivalence between order structures on a ring `R` and *positive cones*:
subsemirings `S` of `R` such that `S ∩ -S = 0`.

-/

@[expose] public section

variable (R : Type*) [Ring R]

theorem Subsemiring.nonneg.isPointed [PartialOrder R] [IsOrderedRing R] :
    (Subsemiring.nonneg R).IsPointed := AddSubmonoid.nonneg.isPointed R

theorem Subsemiring.nonneg.isSpanning [LinearOrder R] [IsOrderedRing R] :
    (Subsemiring.nonneg R).IsSpanning := AddSubmonoid.nonneg.isSpanning R

variable {R} {S : Subsemiring R} (hS : S.IsPointed)

theorem IsOrderedRing.mkOfSubsemiring :
    letI _ := PartialOrder.mkOfAddSubmonoid hS
    IsOrderedRing R :=
  letI _ := PartialOrder.mkOfAddSubmonoid hS
  haveI := IsOrderedAddMonoid.mkOfAddSubmonoid hS
  haveI : ZeroLEOneClass R := ⟨by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ S by simpa using Subsemiring.mul_mem _ xnn ynn

/-- `RingConeClass S R` says that `S` is a type of cones in `R`. -/
@[deprecated "Unbundled to `AddSubmonoid.IsPointed`" (since := "2026-03-28")]
class RingConeClass (S : Type*) (R : outParam Type*) [Ring R] [SetLike S R] : Prop
    extends AddGroupConeClass S R, SubsemiringClass S R

/-- A (positive) cone in a ring is a subsemiring that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the ring into a partially ordered ring. -/
@[deprecated "Unbundled to `AddSubmonoid.IsPointed`" (since := "2026-03-28")]
structure RingCone (R : Type*) [Ring R] extends Subsemiring R, AddGroupCone R

/-- Interpret a cone in a ring as a cone in the underlying additive group. -/
add_decl_doc RingCone.toAddGroupCone

@[deprecated "no replacement" (since := "2026-03-28")]
instance RingCone.instSetLike (R : Type*) [Ring R] : SetLike (RingCone R) R where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[deprecated "no replacement" (since := "2026-03-28")]
instance (R : Type*) [Ring R] : PartialOrder (RingCone R) := .ofSetLike (RingCone R) R

@[deprecated "no replacement" (since := "2026-03-28")]
instance RingCone.instRingConeClass (R : Type*) [Ring R] :
    RingConeClass (RingCone R) R where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

@[simp, deprecated "no replacement" (since := "2026-03-28")]
theorem RingCone.mem_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) {x : R} :
    x ∈ mk toSubsemiring eq_zero_of_mem_of_neg_mem ↔ x ∈ toSubsemiring := .rfl

@[simp, deprecated "no replacement" (since := "2026-03-28")]
theorem RingCone.coe_set_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) :
    (mk toSubsemiring eq_zero_of_mem_of_neg_mem : Set R) = toSubsemiring := rfl

namespace RingCone

variable {T : Type*} [Ring T] [PartialOrder T] [IsOrderedRing T] {a : T}

variable (T) in
/-- Construct a cone from the set of non-negative elements of a partially ordered ring. -/
@[deprecated Subsemiring.nonneg.isPointed (since := "2026-03-28")]
def nonneg : RingCone T where
  __ := Subsemiring.nonneg T
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm

@[simp, deprecated "no replacement" (since := "2026-03-28")]
lemma nonneg_toSubsemiring : (nonneg T).toSubsemiring = .nonneg T := rfl

@[simp, deprecated "no replacement" (since := "2026-03-28")]
lemma nonneg_toAddGroupCone : (nonneg T).toAddGroupCone = .nonneg T := rfl

@[simp, deprecated "no replacement" (since := "2026-03-28")]
lemma mem_nonneg : a ∈ nonneg T ↔ 0 ≤ a := Iff.rfl

@[simp, deprecated "no replacement" (since := "2026-03-28")]
lemma coe_nonneg : nonneg T = {x : T | 0 ≤ x} := rfl

@[deprecated Subsemiring.nonneg.isSpanning (since := "2026-03-28")]
instance nonneg.hasMemOrNegMem {T : Type*} [Ring T] [LinearOrder T] [IsOrderedRing T] :
    HasMemOrNegMem (nonneg T) where
  mem_or_neg_mem := mem_or_neg_mem (AddGroupCone.nonneg T)

end RingCone

variable {S R : Type*} [Ring R] [SetLike S R] (C : S)

/-- Construct a partially ordered ring by designating a cone in a ring. -/
@[deprecated IsOrderedRing.mkOfSubsemiring (since := "2026-03-28")]
lemma IsOrderedRing.mkOfCone [RingConeClass S R] :
    letI _ : PartialOrder R := .mkOfAddGroupCone C
    IsOrderedRing R :=
  letI _ : PartialOrder R := .mkOfAddGroupCone C
  haveI : IsOrderedAddMonoid R := .mkOfCone C
  haveI : ZeroLEOneClass R := ⟨show _ ∈ C by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ C by simpa using mul_mem xnn ynn
