/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Topology.Bornology.Hom

#align_import topology.category.Born from "leanprover-community/mathlib"@"2143571557740bf69d0631339deea0d0e479df54"

/-!
# The category of bornologies

This defines `Born`, the category of bornologies.
-/


universe u

open CategoryTheory

/-- The category of bornologies. -/
def Born :=
  Bundled Bornology
set_option linter.uppercaseLean3 false in
#align Born Born

namespace Born

instance (priority := 10000) : CoeSort Born (Type*) :=
  Bundled.coeSort

instance (priority := 10000) (X : Born) : Bornology X :=
  X.str

/-- Construct a bundled `Born` from a `Bornology`. -/
def of (α : Type*) [Bornology α] : Born :=
  Bundled.of α
set_option linter.uppercaseLean3 false in
#align Born.of Born.of

instance (priority := 10000) : Inhabited Born :=
  ⟨of PUnit⟩

instance (priority := 10000) : BundledHom @LocallyBoundedMap where
  id := @LocallyBoundedMap.id
  comp := @LocallyBoundedMap.comp
  hom_ext _ _ := DFunLike.coe_injective

instance (priority := 10000) : LargeCategory.{u} Born :=
  BundledHom.category LocallyBoundedMap

instance (priority := 10000) : ConcreteCategory Born :=
  BundledHom.concreteCategory LocallyBoundedMap

end Born
