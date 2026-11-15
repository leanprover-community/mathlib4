/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Closure under binary products

In this file, we introduce the closure of a property of objects under
binary (co)products.

-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C]

/-- All objects that are binary products of objects in `P`. -/
abbrev binaryProductsClosure (P : ObjectProperty C) : ObjectProperty C :=
  P.limitClosure (Discrete WalkingPair)

lemma binaryProductsClosure_le_iff [HasTerminal C] {P Q : ObjectProperty C}
    [Q.IsClosedUnderBinaryProducts] [Q.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] :
    P.binaryProductsClosure ≤ Q ↔ P ≤ Q := by
  refine ⟨fun h ↦ (P.le_limitsClosure _).trans h, fun h ↦ ?_⟩
  let : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryProducts.closedUnderIsomorphisms Q
  exact limitsClosure_le h

/-- All objects that are binary coproducts of objects in `P`. -/
abbrev binaryCoproductsClosure (P : ObjectProperty C) : ObjectProperty C :=
  P.colimitClosure (Discrete WalkingPair)

lemma binaryCoproductsClosure_le_iff [HasInitial C] {P Q : ObjectProperty C}
    [Q.IsClosedUnderBinaryCoproducts] [Q.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] :
    P.binaryCoproductsClosure ≤ Q ↔ P ≤ Q := by
  refine ⟨fun h ↦ (P.le_colimitsClosure _).trans h, fun h ↦ ?_⟩
  let : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms Q
  exact colimitsClosure_le h

end CategoryTheory.ObjectProperty
