/-
Copyright (c) 2026 Sabrina Jewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sabrina Jewson
-/
module

public import Mathlib.Order.Defs.LinearOrder

/-!
# Converting Std order typeclasses into Mathlib ones

This file provides factories for creating Mathlib order typeclasses (`PartialOrder`, `LinearOrder`)
from Std ones.

When all instances are present, the factories may be used without arguments:

```lean
instance : LinearOrder X := .ofStd X
```

Otherwise, it may be necessary to provide some instances manually:

```lean
instance : LinearOrder X := .ofStd X
  { lawfulOrderOrd := sorry }
```

When existing instances of typeclasses exist, they will be preferred; otherwise, they will be
generated automatically.
-/

@[expose] public section

/-- Arguments for `Preorder.ofStd`; see that function for details. -/
structure Preorder.OfStdArgs (α : Type*) where
  le : LE α := by
    first
    | infer_instance
    | exact LE.ofOrd _
    | fail "failed to infer `LE` instance; \
            make sure you have an `LE` or `Ord` instance"
  lt :
      let := le
      LT α := by
    extract_lets
    first
    | infer_instance
    | exact ⟨fun a b ↦ a ≤ b ∧ ¬b ≤ a⟩
  lawfulOrderLT :
      let := le; let := lt
      Std.LawfulOrderLT α := by
    extract_lets
    first
    | exact ⟨fun _ _ ↦ _root_.Iff.rfl⟩
    | infer_instance
  isPreorder :
      let := le
      Std.IsPreorder α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.Std.IsLinearPreorder.of_ord.toIsPreorder
    | fail "failed to infer `Std.IsPreorder` instance; \
            make sure you have an `Std.IsPreorder` instance \
            or `Std.LawfulOrderOrd` and `Std.TransOrd` instances"

/-- Create a `Preorder` from a type satisfying `Std.IsPreorder`.

If an `LE` instance exists, either an `Std.IsPreorder` instance must exist, or there must be an
`Ord` instance together with `Std.LawfulOrderOrd` and `Std.TransOrd` instances.

If no `LE` instance exists, it can be generated from `Ord` and `Std.TransOrd` instances.

If an `LT` instance exists, an `Std.LawfulOrderLT` instance must exist also; otherwise, a suitable
`LT` instance will be generated. -/
@[implicit_reducible]
def Preorder.ofStd (α : Type*) (args : OfStdArgs α := by exact {}) : Preorder α where
  toLE := args.le
  toLT := args.lt
  le_refl := args.isPreorder.le_refl
  le_trans := args.isPreorder.le_trans
  lt_iff_le_not_ge := args.lawfulOrderLT.lt_iff

/-- Arguments for `PartialOrder.ofStd`; see that function for details. -/
structure PartialOrder.OfStdArgs (α : Type*) extends toPreorderArgs : Preorder.OfStdArgs α where
  isPartialOrder :
      let := le
      Std.IsPartialOrder α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.Std.IsLinearOrder.of_ord.toIsPartialOrder
    | fail "failed to infer `Std.IsPartialOrder` instance; \
            make sure you have an `Std.IsPartialOrder` instance \
            or `LawfulOrderOrd`, `LawfulEqOrd` and `TransOrd` instances"

/-- Create a `PartialOrder` from a type satisfying `Std.IsPartialOrder`.

If an `LE` instance exists, either an `Std.IsPartialOrder` instance must exist, or there must be an
`Ord` instance together with `Std.LawfulOrderOrd`, `Std.LawfulEqOrd`, and `Std.TransOrd` instances.

If no `LE` instance exists, it can be generated from `Ord`, `Std.LawfulEqOrd`, and `Std.TransOrd`
instances.

If an `LT` instance exists, an `Std.LawfulOrderLT` instance must exist also; otherwise, a suitable
`LT` instance will be generated. -/
@[implicit_reducible]
def PartialOrder.ofStd (α : Type*) (args : OfStdArgs α := by exact {}) : PartialOrder α where
  toPreorder := .ofStd α args.toPreorderArgs
  le_antisymm := args.isPartialOrder.le_antisymm

/- Although Batteries provides that `compareOfLessAndEq` satisfies `LawfulLECmp`, there is
unfortunately no link between that and `LawfulOrderCmp` even though they are essentially the same
thing. -/
theorem Std.LawfulOrderCmp.compareOfLessAndEq (α : Type*)
    [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [DecidableEq α] [DecidableLT α] :
    LawfulOrderCmp (fun a b : α ↦ compareOfLessAndEq a b) :=
  let : Ord α := ⟨fun a b : α ↦ _root_.compareOfLessAndEq a b⟩
  { isLE_compare _ _ :=
      have : DecidableLE α := fun _ _ ↦ Classical.propDecidable _
      isLE_compareOfLessAndEq Std.le_antisymm Std.not_le (fun _ _ ↦ Std.le_total)
    isGE_compare _ _ :=
      have : DecidableLE α := fun _ _ ↦ Classical.propDecidable _
      isGE_compareOfLessAndEq Std.le_antisymm Std.not_le (fun _ _ ↦ Std.le_total) }

/-- Arguments for `LinearOrder.ofStd`; see that function for details. -/
structure LinearOrder.OfStdArgs (α : Type*) extends
    toPartialOrderArgs : PartialOrder.OfStdArgs α where
  isLinearOrder :
      let := le
      Std.IsLinearOrder α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.Std.IsLinearOrder.of_ord
    | fail "failed to infer `Std.IsLinearOrder` instance; \
            make sure you have an `Std.IsLinearOrder` instance \
            or `LawfulOrderOrd`, `LawfulEqOrd` and `TransOrd` instances"
  decidableLE : DecidableLE α := by
    first
    | infer_instance
    | exact _root_.DecidableLE.ofOrd _
    | fail "failed to infer `DecidableLE` instance; \
            make sure you have a `DecidableLE` instance \
            or a `LawfulOrderOrd` instance"
  decidableEq :
      let := toPartialOrderArgs; let := decidableLE
      DecidableEq α := by
    extract_lets _ toPartialOrderArgs
    first
    | infer_instance
    | exact @_root_.decidableEqOfDecidableLE _ (.ofStd _ toPartialOrderArgs) _
  decidableLT :
      let := toPreorderArgs; let := decidableLE
      DecidableLT α := by
    extract_lets _ toPreorderArgs
    first
    | infer_instance
    | exact @_root_.decidableLTOfDecidableLE _ (.ofStd _ toPreorderArgs) _
  min :
      let := le; let := decidableLE
      Min α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.Min.leftLeaningOfLE _
  max :
      let := le; let := decidableLE
      Max α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.Max.leftLeaningOfLE _
  lawfulOrderLeftLeaningMin : Std.LawfulOrderLeftLeaningMin α := by infer_instance
  lawfulOrderLeftLeaningMax : Std.LawfulOrderLeftLeaningMax α := by infer_instance
  ord :
      let := lt; let := decidableEq; let := decidableLT
      Ord α := by
    extract_lets
    first
    | infer_instance
    | exact ⟨fun a b ↦ _root_.compareOfLessAndEq a b⟩
  lawfulOrderOrd :
      let := le; let := lt; let := lawfulOrderLT; let := isLinearOrder
      let := decidableEq; let := decidableLT
      Std.LawfulOrderOrd α := by
    extract_lets
    first
    | exact _root_.Std.LawfulOrderCmp.compareOfLessAndEq _
    | infer_instance

/-- Create a `LinearOrder` from a type satisfying `Std.IsLinearOrder`.

If an `LE` instance exists, either an `Std.IsLinearOrder` instance must exist, or there must be an
`Ord` instance together with `Std.LawfulOrderOrd`, `Std.LawfulEqOrd`, and `Std.TransOrd` instances.

If no `LE` instance exists, it can be generated from `Ord`, `Std.LawfulEqOrd`, and `Std.TransOrd`
instances.

If an `LT` instance exists, an `Std.LawfulOrderLT` instance must exist also; otherwise, a suitable
`LT` instance will be generated.

If a `DecidableLE` instance exists, it will be used. Otherwise, it can be generated from an `Ord`
instance.

If `DecidableEq` and `DecidableLT` instances exist, they will be used. Otherwise, they will be
generated from the `DecidableLE` instance.

If `Min` and `Max` instances exist, they will be used, in which case the user must provide
`Std.LawfulOrderLeftLeaningMin` or `Std.LawfulOrderLeftLeaningMax` respectively. Otherwise, they
will be generated.

If an `Ord` instance exists, it will be used, in which case the user must provide an
`Std.LawfulOrderOrd` instance. Otherwise, it will be generated. -/
@[implicit_reducible]
def LinearOrder.ofStd (α : Type*) (args : OfStdArgs α := by exact {}) : LinearOrder α :=
  let := args.le
  let := args.lt
  have := args.lawfulOrderLT
  have := args.isLinearOrder
  let := args.decidableLE
  have := args.lawfulOrderLeftLeaningMin
  have := args.lawfulOrderLeftLeaningMax
  { toPartialOrder := .ofStd _ args.toPartialOrderArgs
    le_total := args.isLinearOrder.le_total
    toDecidableLE := args.decidableLE
    toDecidableEq := args.decidableEq
    toDecidableLT := args.decidableLT
    toMin := args.min
    toMax := args.max
    min_def _ _ := Std.min_eq_if
    max_def a b := by
      rw [Std.max_eq_if]
      split
      · split
        · exact Std.le_antisymm ‹_› ‹_›
        · rfl
      case _ h => rw [if_pos (Std.le_of_lt (Std.not_le.mp h))]
    toOrd := args.ord
    compare_eq_compareOfLessAndEq a b := by
      let := args.ord
      have := args.lawfulOrderOrd
      rw [compareOfLessAndEq]
      split_ifs
      case _ => rwa [Std.compare_eq_lt]
      case _ => rwa [Std.compare_eq_iff_eq]
      case _ h h' =>
        exact Std.compare_eq_gt.mpr <| Std.lt_of_le_of_ne (Std.not_lt.mp h) (Ne.symm h') }
