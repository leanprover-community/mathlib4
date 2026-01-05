/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.InjSurj
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FastInstance

/-!
# `Order`ed instances for `SubsemiringClass` and `Subsemiring`.
-/

@[expose] public section

namespace SubsemiringClass
variable {R S : Type*} [SetLike S R] (s : S)

/-- A subsemiring of an ordered semiring is an ordered semiring. -/
instance toIsOrderedRing [Semiring R] [PartialOrder R] [IsOrderedRing R] [SubsemiringClass S R] :
    IsOrderedRing s :=
  Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

/-- A subsemiring of a strict ordered semiring is a strict ordered semiring. -/
instance toIsStrictOrderedRing [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [SubsemiringClass S R] : IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

end SubsemiringClass

namespace Subsemiring

variable {R : Type*}

/-- A subsemiring of an ordered semiring is an ordered semiring. -/
instance toIsOrderedRing [Semiring R] [PartialOrder R] [IsOrderedRing R] (s : Subsemiring R) :
    IsOrderedRing s :=
  SubsemiringClass.toIsOrderedRing _

/-- A subsemiring of a strict ordered semiring is a strict ordered semiring. -/
instance toIsStrictOrderedRing [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    (s : Subsemiring R) : IsStrictOrderedRing s :=
  SubsemiringClass.toIsStrictOrderedRing _

section nonneg

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

variable (R) in
/-- The set of nonnegative elements in an ordered semiring, as a subsemiring. -/
@[simps]
def nonneg : Subsemiring R where
  __ := AddSubmonoid.nonneg R
  mul_mem' := mul_nonneg
  one_mem' := zero_le_one

@[simp] lemma mem_nonneg {x : R} : x ∈ nonneg R ↔ 0 ≤ x := .rfl

variable (R) in
@[simp]
theorem nonneg_toAddSubmonoid : (nonneg R).toAddSubmonoid = AddSubmonoid.nonneg R := rfl

end nonneg

end Subsemiring
