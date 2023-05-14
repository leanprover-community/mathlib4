/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.Frm
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.Lat
import Mathbin.Order.Hom.CompleteLattice
import Mathbin.Topology.Category.CompHaus.Basic
import Mathbin.Topology.Sets.Opens

/-!
# The category of frames

This file defines `Frm`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/


universe u

open CategoryTheory Opposite Order TopologicalSpace

/-- The category of frames. -/
def Frm :=
  Bundled Frame
#align Frm Frm

namespace Frm

instance : CoeSort Frm (Type _) :=
  Bundled.hasCoeToSort

instance (X : Frm) : Frame X :=
  X.str

/-- Construct a bundled `Frm` from a `frame`. -/
def of (α : Type _) [Frame α] : Frm :=
  Bundled.of α
#align Frm.of Frm.of

@[simp]
theorem coe_of (α : Type _) [Frame α] : ↥(of α) = α :=
  rfl
#align Frm.coe_of Frm.coe_of

instance : Inhabited Frm :=
  ⟨of PUnit⟩

/-- An abbreviation of `frame_hom` that assumes `frame` instead of the weaker `complete_lattice`.
Necessary for the category theory machinery. -/
abbrev Hom (α β : Type _) [Frame α] [Frame β] : Type _ :=
  FrameHom α β
#align Frm.hom Frm.Hom

instance bundledHom : BundledHom Hom :=
  ⟨fun α β [Frame α] [Frame β] => (coeFn : FrameHom α β → α → β), fun α [Frame α] => FrameHom.id α,
    fun α β γ [Frame α] [Frame β] [Frame γ] => FrameHom.comp, fun α β [Frame α] [Frame β] =>
    FunLike.coe_injective⟩
#align Frm.bundled_hom Frm.bundledHom

deriving instance LargeCategory, ConcreteCategory for Frm

instance hasForgetToLat : HasForget₂ Frm LatCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => FrameHom.toLatticeHom }
#align Frm.has_forget_to_Lat Frm.hasForgetToLat

/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Frm.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align Frm.iso.mk Frm.Iso.mk

end Frm

/-- The forgetful functor from `Topᵒᵖ` to `Frm`. -/
@[simps]
def topOpToFrame : TopCatᵒᵖ ⥤ Frm
    where
  obj X := Frm.of (Opens (unop X : TopCat))
  map X Y f := Opens.comap <| Quiver.Hom.unop f
  map_id' X := Opens.comap_id
#align Top_op_to_Frame topOpToFrame

-- Note, `CompHaus` is too strong. We only need `t0_space`.
instance CompHausOpToFrame.faithful : Faithful (compHausToTop.op ⋙ topOpToFrame.{u}) :=
  ⟨fun X Y f g h => Quiver.Hom.unop_inj <| Opens.comap_injective h⟩
#align CompHaus_op_to_Frame.faithful CompHausOpToFrame.faithful

