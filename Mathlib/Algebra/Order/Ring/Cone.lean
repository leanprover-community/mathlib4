/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
module

public import Mathlib.Algebra.Order.Group.Cone
public import Mathlib.Algebra.Ring.Subsemiring.Order

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Construct ordered rings from rings with a specified positive cone.

We demonstrate the equivalence between order structures on a ring `R` and *positive cones*:
subsemirings `S` of `R` such that `S ∩ -S = 0`.
-/

@[expose] public section

variable (R : Type*) [Ring R]

protected theorem Subsemiring.IsPointed.nonneg [PartialOrder R] [IsOrderedRing R] :
    (Subsemiring.nonneg R).IsPointed := AddSubmonoid.IsPointed.nonneg R

protected theorem Subsemiring.IsSpanning.nonneg [LinearOrder R] [IsOrderedRing R] :
    (Subsemiring.nonneg R).IsSpanning := AddSubmonoid.IsSpanning.nonneg R

variable {R} {S : Subsemiring R} (hS : S.IsPointed)

theorem IsOrderedRing.ofSubsemiring :
    letI _ := PartialOrder.ofAddSubmonoid hS
    IsOrderedRing R :=
  letI _ := PartialOrder.ofAddSubmonoid hS
  haveI := IsOrderedAddMonoid.ofAddSubmonoid hS
  haveI : ZeroLEOneClass R := ⟨by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ S by simpa using Subsemiring.mul_mem _ xnn ynn

namespace Ring

variable (R) in
/-- Equivalence between subsemirings with zero support in a ring `R`
    and partially ordered ring structures on `R`. -/
noncomputable def isPointedPartialOrderEquiv :
    Equiv {C : Subsemiring R // C.IsPointed}
          {_o : PartialOrder R // IsOrderedRing R} where
  toFun := fun ⟨_, hC⟩ ↦ ⟨.ofAddSubmonoid hC, .ofSubsemiring _⟩
  invFun := fun ⟨_, _⟩ ↦ ⟨.nonneg R, .nonneg _⟩
  left_inv := fun ⟨_, _⟩ ↦ by ext; simp
  right_inv := fun ⟨_, _⟩ ↦ by ext; simp +instances

@[simp]
theorem isPointedPartialOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsPointed) :
    isPointedPartialOrderEquiv R ⟨C, h⟩ = PartialOrder.ofAddSubmonoid h := rfl

@[simp]
theorem isPointedPartialOrderEquiv_symm_apply (o : PartialOrder R) (h : IsOrderedRing R) :
    (isPointedPartialOrderEquiv R).symm ⟨o, h⟩ = Subsemiring.nonneg R := rfl

variable (R) in
open Classical in
/-- Equivalence between maximal subsemirings with zero support in a ring `R`
    and linearly ordered ring structures on `R`. -/
noncomputable def isPointedLinearOrderEquiv :
    Equiv {C : Subsemiring R // C.IsPointed ∧ C.IsSpanning}
          {_o : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨C, hC⟩ ↦ ⟨.ofAddSubmonoid hC.1 hC.2, .ofSubsemiring _⟩
  invFun := fun ⟨_, _⟩ ↦ ⟨.nonneg R, .nonneg _, .nonneg _⟩
  left_inv := fun ⟨_, _, _⟩ ↦ by ext; simp
  right_inv := fun ⟨_, _⟩ ↦ by ext; simp

open Classical in
@[simp]
theorem isPointedLinearOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsPointed ∧ C.IsSpanning) :
    isPointedLinearOrderEquiv R ⟨C, h⟩ = LinearOrder.ofAddSubmonoid h.1 h.2 := rfl

@[simp]
theorem isPointedLinearOrderEquiv_symm_apply (o : LinearOrder R) (h : IsOrderedRing R) :
    (isPointedLinearOrderEquiv R).symm ⟨o, h⟩ = Subsemiring.nonneg R := rfl

end Ring

/- Deprecated -/

/-- `RingConeClass S R` says that `S` is a type of cones in `R`. -/
@[deprecated AddSubmonoid.IsPointed +typeChanged (since := "2026-10-28")]
class RingConeClass (S : Type*) (R : outParam Type*) [Ring R] [SetLike S R] : Prop
    extends AddGroupConeClass S R, SubsemiringClass S R

/-- A (positive) cone in a ring is a subsemiring that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the ring into a partially ordered ring. -/
@[deprecated AddSubmonoid.IsPointed +typeChanged (since := "2026-10-28")]
structure RingCone (R : Type*) [Ring R] extends Subsemiring R, AddGroupCone R

/-- Interpret a cone in a ring as a cone in the underlying additive group. -/
add_decl_doc RingCone.toAddGroupCone

@[deprecated "no replacement" (since := "2026-10-28")]
instance RingCone.instSetLike (R : Type*) [Ring R] : SetLike (RingCone R) R where
  coe C := C.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[deprecated "no replacement" (since := "2026-10-28")]
instance (R : Type*) [Ring R] : PartialOrder (RingCone R) := .ofSetLike (RingCone R)

@[deprecated "no replacement" (since := "2026-10-28")]
instance RingCone.instRingConeClass (R : Type*) [Ring R] :
    RingConeClass (RingCone R) R where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

@[simp, deprecated "no replacement" (since := "2026-10-28")]
theorem RingCone.mem_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) {x : R} :
    x ∈ mk toSubsemiring eq_zero_of_mem_of_neg_mem ↔ x ∈ toSubsemiring := .rfl

@[simp, deprecated "no replacement" (since := "2026-10-28")]
theorem RingCone.coe_set_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) :
    (mk toSubsemiring eq_zero_of_mem_of_neg_mem : Set R) = toSubsemiring := rfl

namespace RingCone

variable {T : Type*} [Ring T] [PartialOrder T] [IsOrderedRing T] {a : T}

variable (T) in
/-- Construct a cone from the set of non-negative elements of a partially ordered ring. -/
@[deprecated Subsemiring.IsPointed.nonneg +typeChanged (since := "2026-10-28")]
def nonneg : RingCone T where
  __ := Subsemiring.nonneg T
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm

@[simp, deprecated "no replacement" (since := "2026-10-28")]
lemma nonneg_toSubsemiring : (nonneg T).toSubsemiring = .nonneg T := rfl

@[simp, deprecated "no replacement" (since := "2026-10-28")]
lemma nonneg_toAddGroupCone : (nonneg T).toAddGroupCone = .nonneg T := rfl

@[simp, deprecated "no replacement" (since := "2026-10-28")]
lemma mem_nonneg : a ∈ nonneg T ↔ 0 ≤ a := Iff.rfl

@[simp, deprecated "no replacement" (since := "2026-10-28")]
lemma coe_nonneg : nonneg T = {x : T | 0 ≤ x} := rfl

@[deprecated Subsemiring.IsSpanning.nonneg +typeChanged (since := "2026-10-28")]
instance nonneg.hasMemOrNegMem {T : Type*} [Ring T] [LinearOrder T] [IsOrderedRing T] :
    HasMemOrNegMem (nonneg T) where
  mem_or_neg_mem := mem_or_neg_mem (AddGroupCone.nonneg T)

end RingCone

variable {S R : Type*} [Ring R] [SetLike S R] (C : S)

/-- Construct a partially ordered ring by designating a cone in a ring. -/
@[deprecated IsOrderedRing.ofSubsemiring +typeChanged (since := "2026-10-28")]
lemma IsOrderedRing.mkOfCone [RingConeClass S R] :
    letI _ : PartialOrder R := .mkOfAddGroupCone C
    IsOrderedRing R :=
  letI _ : PartialOrder R := .mkOfAddGroupCone C
  haveI : IsOrderedAddMonoid R := .mkOfCone C
  haveI : ZeroLEOneClass R := ⟨show _ ∈ C by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ C by simpa using mul_mem xnn ynn
