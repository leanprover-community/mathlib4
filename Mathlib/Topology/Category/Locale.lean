/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.FrmCat

#align_import topology.category.Locale from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/


universe u

open CategoryTheory Opposite Order TopologicalSpace

set_option linter.uppercaseLean3 false

/-- The category of locales. -/
def Locale :=
  FrmCatᵒᵖ deriving LargeCategory
#align Locale Locale

namespace Locale

instance : CoeSort Locale (Type*) :=
  ⟨fun X => X.unop⟩

instance (X : Locale) : Frame X :=
  X.unop.str

/-- Construct a bundled `Locale` from a `Frame`. -/
def of (α : Type*) [Frame α] : Locale :=
  op <| FrmCat.of α
#align Locale.of Locale.of

@[simp]
theorem coe_of (α : Type*) [Frame α] : ↥(of α) = α :=
  rfl
#align Locale.coe_of Locale.coe_of

instance : Inhabited Locale :=
  ⟨of PUnit⟩

end Locale

/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
@[simps!]
def topToLocale : TopCat ⥤ Locale :=
  topCatOpToFrameCat.rightOp
#align Top_to_Locale topToLocale

-- Note, `CompHaus` is too strong. We only need `T0Space`.
instance CompHausToLocale.faithful : Faithful (compHausToTop ⋙ topToLocale.{u}) :=
  ⟨fun h => by
    dsimp at h
    -- ⊢ a₁✝ = a₂✝
    exact Opens.comap_injective (Quiver.Hom.op_inj h)⟩
    -- 🎉 no goals
#align CompHaus_to_Locale.faithful CompHausToLocale.faithful
