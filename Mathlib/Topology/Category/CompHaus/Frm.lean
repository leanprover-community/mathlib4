/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

import Mathlib.Order.Category.Frm
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Sets.Opens

/-! The forgetful functor from `TopCatᵒᵖ` to `Frm`. -/

universe u

open TopologicalSpace Opposite CategoryTheory

/-- The forgetful functor from `TopCatᵒᵖ` to `Frm`. -/
@[simps]
def topCatOpToFrm : TopCatᵒᵖ ⥤ Frm where
  obj X := Frm.of (Opens (unop X : TopCat))
  map f := Frm.ofHom <| Opens.comap <| (Quiver.Hom.unop f).hom

-- Note, `CompHaus` is too strong. We only need `T0Space`.
instance CompHausOpToFrame.faithful : (compHausToTop.op ⋙ topCatOpToFrm.{u}).Faithful :=
  ⟨fun {X _ _ _} h =>  Quiver.Hom.unop_inj <| ConcreteCategory.ext <|
    Opens.comap_injective (β := (unop X).toTop) <| FrameHom.ext <|
      CategoryTheory.congr_fun h⟩
