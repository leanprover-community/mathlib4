/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.category.Born
! leanprover-community/mathlib commit 2143571557740bf69d0631339deea0d0e479df54
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.Topology.Bornology.Hom

/-!
# The category of bornologies

This defines `Born`, the category of bornologies.
-/


universe u

open CategoryTheory

/-- The category of bornologies. -/
def Born :=
  Bundled Bornology
#align Born Born

namespace Born

instance : CoeSort Born (Type _) :=
  Bundled.hasCoeToSort

instance (X : Born) : Bornology X :=
  X.str

/-- Construct a bundled `Born` from a `bornology`. -/
def of (α : Type _) [Bornology α] : Born :=
  Bundled.of α
#align Born.of Born.of

instance : Inhabited Born :=
  ⟨of PUnit⟩

instance : BundledHom @LocallyBoundedMap
    where
  toFun _ _ _ _ := coeFn
  id := @LocallyBoundedMap.id
  comp := @LocallyBoundedMap.comp
  hom_ext X Y _ _ := FunLike.coe_injective

instance : LargeCategory.{u} Born :=
  BundledHom.category LocallyBoundedMap

instance : ConcreteCategory Born :=
  BundledHom.concreteCategory LocallyBoundedMap

end Born

