current imports:
public import Mathlib.Algebra.Ring.Submonoid.Pointwise
**public import Mathlib.Algebra.DirectSum.Basic**
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Ring.Submonoid.Pointwise
public import Mathlib.Order.CompletePartialOrder


DirectSum.coeAddMonoidHom_of
DirectSum.sigmaCurry
DirectSum.equivCongrLeft
: Mathlib.Algebra.DirectSum.Basic

----

AddSubmonoidClass
: **Mathlib.Algebra.Group.Submonoid.Defs**

IsConcreteLE
: Mathlib.Data.SetLike.Basic
```lean
/-- A class to indicate that the canonical injection between `A` and `Set B` is order-preserving.

An instance of this class is automatically available on any partial order defined as
`PartialOrder.ofSetLike`.
-/
class IsConcreteLE (A : Type*) (B : outParam Type*) [SetLike A B] [LE A] where
  /-- The coercion from a `SetLike` type preserves the ordering. -/
  protected coe_subset_coe' {S T : A} : SetLike.coe S ⊆ SetLike.coe T ↔ S ≤ T

/-- The partial order induced from a `SetLike` instance by inclusion.

A partial order defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteLE`.
-/
@[reducible] def PartialOrder.ofSetLike (A B : Type*) [SetLike A B] : PartialOrder A where
  __ := LE.ofSetLike A B
  __ := PartialOrder.lift (SetLike.coe : A → Set B) SetLike.coe_injective

instance : letI := PartialOrder.ofSetLike A B; IsConcreteLE A B :=
  letI := PartialOrder.ofSetLike A B; { coe_subset_coe' := Iff.rfl }

```
