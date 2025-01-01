/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read, Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Opposites

/-!
# Opposite adjunctions

This file contains constructions to relate adjunctions of functors to adjunctions of their
opposites.

## Tags
adjunction, opposite, uniqueness
-/


open CategoryTheory

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [CategoryTheory universes].
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Adjunction

attribute [local simp] homEquiv_unit homEquiv_counit

/-- If `G.op` is adjoint to `F.op` then `F` is adjoint to `G`. -/
@[simps]
def unop (F : C ⥤ D) (G : D ⥤ C) (h : G.op ⊣ F.op) : F ⊣ G where
  unit := NatTrans.unop h.counit
  counit := NatTrans.unop h.unit
  left_triangle_components _ := Quiver.Hom.op_inj (h.right_triangle_components _)
  right_triangle_components _ := Quiver.Hom.op_inj (h.left_triangle_components _)

@[deprecated (since := "2025-01-01")] alias adjointOfOpAdjointOp := unop

/-- If `G` is adjoint to `F.op` then `F` is adjoint to `G.unop`. -/
@[deprecated "Use Adjunction.unop instead." (since := "2025-01-01")]
def adjointUnopOfAdjointOp (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F.op) : F ⊣ G.unop :=
  unop F G.unop (h.ofNatIsoLeft G.opUnopIso.symm)

/-- If `G.op` is adjoint to `F` then `F.unop` is adjoint to `G`. -/
@[deprecated "Use Adjunction.unop instead." (since := "2025-01-01")]
def unopAdjointOfOpAdjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G.op ⊣ F) : F.unop ⊣ G :=
  unop _ _ (h.ofNatIsoRight F.opUnopIso.symm)

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
@[deprecated "Use Adjunction.unop instead." (since := "2025-01-01")]
def unopAdjointUnopOfAdjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F) : F.unop ⊣ G.unop :=
  unop F.unop G.unop (h.ofNatIsoRight F.opUnopIso.symm)

/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
@[simps! unit_app counit_app]
def op (F : C ⥤ D) (G : D ⥤ C) (h : G ⊣ F) : F.op ⊣ G.op where
  unit := NatTrans.op h.counit
  counit := NatTrans.op h.unit
  left_triangle_components _ := Quiver.Hom.unop_inj (by simp)
  right_triangle_components _ := Quiver.Hom.unop_inj (by simp)

@[deprecated (since := "2025-01-01")] alias opAdjointOpOfAdjoint := op

/-- If `G` is adjoint to `F.unop` then `F` is adjoint to `G.op`. -/
@[deprecated "Use Adjunction.op instead." (since := "2025-01-01")]
def adjointOpOfAdjointUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G ⊣ F.unop) : F ⊣ G.op :=
  (op F.unop _ h).ofNatIsoLeft F.opUnopIso

/-- If `G.unop` is adjoint to `F` then `F.op` is adjoint to `G`. -/
@[deprecated "Use Adjunction.op instead." (since := "2025-01-01")]
def opAdjointOfUnopAdjoint (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F) : F.op ⊣ G :=
  (op _ G.unop h).ofNatIsoRight G.opUnopIso

/-- If `G.unop` is adjoint to `F.unop` then `F` is adjoint to `G`. -/
@[deprecated "Use Adjunction.op instead." (since := "2025-01-01")]
def adjointOfUnopAdjointUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F.unop) : F ⊣ G :=
  (op _ _ h).ofNatIsoRight G.opUnopIso

/-- If `F` and `F'` are both adjoint to `G`, there is a natural isomorphism
`F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda`.
We use this in combination with `fullyFaithfulCancelRight` to show left adjoints are unique.
-/
def leftAdjointsCoyonedaEquiv {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda :=
  NatIso.ofComponents fun X =>
    NatIso.ofComponents fun Y =>
      ((adj1.homEquiv X.unop Y).trans (adj2.homEquiv X.unop Y).symm).toIso

/-- Given two adjunctions, if the right adjoints are naturally isomorphic, then so are the left
adjoints.

Note: it is generally better to use `Adjunction.natIsoEquiv`, see the file `Adjunction.Unique`.
The reason this definition still exists is that apparently `CategoryTheory.extendAlongYonedaYoneda`
uses its definitional properties (TODO: figure out a way to avoid this).
-/
def natIsoOfRightAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (r : G ≅ G') : F ≅ F' :=
  NatIso.removeOp ((Coyoneda.fullyFaithful.whiskeringRight _).isoEquiv.symm
    (leftAdjointsCoyonedaEquiv adj2 (adj1.ofNatIsoRight r)))

/-- Given two adjunctions, if the left adjoints are naturally isomorphic, then so are the right
adjoints.

Note: it is generally better to use `Adjunction.natIsoEquiv`, see the file `Adjunction.Unique`.
-/
def natIsoOfLeftAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (l : F ≅ F') : G ≅ G' :=
  NatIso.removeOp (natIsoOfRightAdjointNatIso (op _ F' adj2)
    (op _ _ adj1) (NatIso.op l))

end CategoryTheory.Adjunction
