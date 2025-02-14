/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.Frm
import Mathlib.Topology.Category.CompHaus.Frm

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/


universe u

open CategoryTheory Opposite Order TopologicalSpace


/-- The category of locales. -/
def Locale :=
  Frmᵒᵖ deriving LargeCategory

namespace Locale

instance : CoeSort Locale Type* :=
  ⟨fun X => X.unop⟩

instance (X : Locale) : Frame X :=
  X.unop.str

/-- Construct a bundled `Locale` from a `Frame`. -/
def of (α : Type*) [Frame α] : Locale :=
  op <| Frm.of α

@[simp]
theorem coe_of (α : Type*) [Frame α] : ↥(of α) = α :=
  rfl

instance : Inhabited Locale :=
  ⟨of PUnit⟩

end Locale

/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
@[simps!]
def topToLocale : TopCat ⥤ Locale :=
  topCatOpToFrm.rightOp

-- Note, `CompHaus` is too strong. We only need `T0Space`.
instance CompHausToLocale.faithful : (compHausToTop ⋙ topToLocale.{u}).Faithful :=
  ⟨fun h => by
    dsimp at h
    exact ConcreteCategory.ext (Opens.comap_injective (congr_arg Frm.Hom.hom
      (Quiver.Hom.op_inj h)))⟩
