/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.Frm
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.Category.LatCat
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Sets.Opens

/-!
# The category of frames

This file defines `FrmCat`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/


universe u

open CategoryTheory Opposite Order TopologicalSpace

set_option linter.uppercaseLean3 false -- `Frm`

/-- The category of frames. -/
def FrmCat :=
  Bundled Frame
#align Frm FrmCat

namespace FrmCat

instance : CoeSort FrmCat (Type _) :=
  Bundled.coeSort

instance (X : FrmCat) : Frame X :=
  X.str

/-- Construct a bundled `FrmCat` from a `Frame`. -/
def of (α : Type _) [Frame α] : FrmCat :=
  Bundled.of α
#align Frm.of FrmCat.of

@[simp]
theorem coe_of (α : Type _) [Frame α] : ↥(of α) = α := rfl
#align Frm.coe_of FrmCat.coe_of

instance : Inhabited FrmCat :=
  ⟨of PUnit⟩

/-- An abbreviation of `FrameHom` that assumes `Frame` instead of the weaker `completeLattice`.
Necessary for the category theory machinery. -/
abbrev Hom (α β : Type _) [Frame α] [Frame β] : Type _ :=
  FrameHom α β
#align Frm.hom FrmCat.Hom

instance bundledHom : BundledHom Hom where
  toFun {α β} _ _ := ((↑) : FrameHom α β → α → β)
  id {α} _ := FrameHom.id α
  comp _ _ _ := FrameHom.comp
  hom_ext _ _ := FunLike.coe_injective
#align Frm.bundled_hom FrmCat.bundledHom

-- Porting note: Originally `deriving instance LargeCategory, ConcreteCategory for FrmCat`
-- see https://github.com/leanprover-community/mathlib4/issues/5020
deriving instance LargeCategory, Category for FrmCat

instance : ConcreteCategory FrmCat := by
  unfold FrmCat
  infer_instance

instance hasForgetToLat : HasForget₂ FrmCat LatCat where
  forget₂ :=
    { obj := fun X => ⟨X, _⟩
      map := fun {X Y} => FrameHom.toLatticeHom }
#align Frm.has_forget_to_Lat FrmCat.hasForgetToLat

/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : FrmCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : FrameHom _ _)
  inv := (e.symm : FrameHom _ _)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
#align Frm.iso.mk FrmCat.Iso.mk

end FrmCat

/-- The forgetful functor from `TopCatᵒᵖ` to `FrmCat`. -/
@[simps]
def topCatOpToFrameCat : TopCatᵒᵖ ⥤ FrmCat where
  obj X := FrmCat.of (Opens (unop X : TopCat))
  map f := Opens.comap <| Quiver.Hom.unop f
  map_id X := Opens.comap_id
#align Top_op_to_Frame topCatOpToFrameCat

-- Note, `CompHaus` is too strong. We only need `T0Space`.
instance CompHausOpToFrame.faithful : Faithful (compHausToTop.op ⋙ topCatOpToFrameCat.{u}) :=
  ⟨fun h => Quiver.Hom.unop_inj <| Opens.comap_injective h⟩
#align CompHaus_op_to_Frame.faithful CompHausOpToFrame.faithful
