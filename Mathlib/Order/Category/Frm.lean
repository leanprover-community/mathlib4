/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.Lat
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Sets.Opens

#align_import order.category.Frm from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of frames

This file defines `Frm`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/


universe u

open CategoryTheory Opposite Order TopologicalSpace

set_option linter.uppercaseLean3 false -- `Frm`

/-- The category of frames. -/
def Frm :=
  Bundled Frame
#align Frm Frm

namespace Frm

instance : CoeSort Frm Type* :=
  Bundled.coeSort

instance (X : Frm) : Frame X :=
  X.str

/-- Construct a bundled `Frm` from a `Frame`. -/
def of (α : Type*) [Frame α] : Frm :=
  Bundled.of α
#align Frm.of Frm.of

@[simp]
theorem coe_of (α : Type*) [Frame α] : ↥(of α) = α := rfl
#align Frm.coe_of Frm.coe_of

instance : Inhabited Frm :=
  ⟨of PUnit⟩

/-- An abbreviation of `FrameHom` that assumes `Frame` instead of the weaker `CompleteLattice`.
Necessary for the category theory machinery. -/
abbrev Hom (α β : Type*) [Frame α] [Frame β] : Type _ :=
  FrameHom α β
#align Frm.hom Frm.Hom

instance bundledHom : BundledHom Hom where
  toFun {α β} _ _ := ((↑) : FrameHom α β → α → β)
  id {α} _ := FrameHom.id α
  comp _ _ _ := FrameHom.comp
  hom_ext _ _ := DFunLike.coe_injective
#align Frm.bundled_hom Frm.bundledHom

-- Porting note: Originally `deriving instance LargeCategory, ConcreteCategory for Frm`
-- see https://github.com/leanprover-community/mathlib4/issues/5020
deriving instance LargeCategory, Category for Frm

instance : ConcreteCategory Frm := by
  unfold Frm
  infer_instance

instance hasForgetToLat : HasForget₂ Frm Lat where
  forget₂ :=
    { obj := fun X => ⟨X, _⟩
      map := fun {X Y} => FrameHom.toLatticeHom }
#align Frm.has_forget_to_Lat Frm.hasForgetToLat

/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Frm.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : FrameHom _ _)
  inv := (e.symm : FrameHom _ _)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
#align Frm.iso.mk Frm.Iso.mk

end Frm

/-- The forgetful functor from `TopCatᵒᵖ` to `Frm`. -/
@[simps]
def topCatOpToFrm : TopCatᵒᵖ ⥤ Frm where
  obj X := Frm.of (Opens (unop X : TopCat))
  map f := Opens.comap <| Quiver.Hom.unop f
  map_id X := Opens.comap_id
#align Top_op_to_Frame topCatOpToFrm

-- Note, `CompHaus` is too strong. We only need `T0Space`.
instance CompHausOpToFrame.faithful : (compHausToTop.op ⋙ topCatOpToFrm.{u}).Faithful :=
  ⟨fun h => Quiver.Hom.unop_inj <| Opens.comap_injective h⟩
#align CompHaus_op_to_Frame.faithful CompHausOpToFrame.faithful
