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

-- morphism levels before object levels. See note [category theory universes].
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Adjunction

attribute [local simp] homEquiv_unit homEquiv_counit

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
@[simps]
def unop {F : Cᵒᵖ ⥤ Dᵒᵖ} {G : Dᵒᵖ ⥤ Cᵒᵖ} (h : G ⊣ F) : F.unop ⊣ G.unop where
  unit := NatTrans.unop h.counit
  counit := NatTrans.unop h.unit
  left_triangle_components _ := Quiver.Hom.op_inj (h.right_triangle_components _)
  right_triangle_components _ := Quiver.Hom.op_inj (h.left_triangle_components _)

/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
@[simps]
def op {F : C ⥤ D} {G : D ⥤ C} (h : G ⊣ F) : F.op ⊣ G.op where
  unit := NatTrans.op h.counit
  counit := NatTrans.op h.unit
  left_triangle_components _ := Quiver.Hom.unop_inj (by simp)
  right_triangle_components _ := Quiver.Hom.unop_inj (by simp)

/-- If `F` is adjoint to `G.leftOp` then `G` is adjoint to `F.leftOp`. -/
@[simps]
def leftOp {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp) : G ⊣ F.leftOp where
  unit := NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components X.unop).unop)

/-- If `F.rightOp` is adjoint to `G` then `G.rightOp` is adjoint to `F`. -/
@[simps]
def rightOp {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G) : G.rightOp ⊣ F where
  unit := NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components X.unop).unop)

lemma leftOp_eq {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp) :
    a.leftOp = (opOpEquivalence D).symm.toAdjunction.comp a.op := by
  ext X; simp [Equivalence.unit]

lemma rightOp_eq {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G) :
    a.rightOp = (opOpEquivalence D).symm.toAdjunction.comp a.op := by
  ext X; simp [Equivalence.unit]

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
  NatIso.removeOp (natIsoOfRightAdjointNatIso (op adj2) (op adj1) (NatIso.op l))

end Adjunction

namespace Functor

instance IsLeftAdjoint.op {F : C ⥤ D} [F.IsLeftAdjoint] : F.op.IsRightAdjoint :=
  ⟨F.rightAdjoint.op, ⟨.op <| .ofIsLeftAdjoint _⟩⟩

instance IsRightAdjoint.op {F : C ⥤ D} [F.IsRightAdjoint] : F.op.IsLeftAdjoint :=
  ⟨F.leftAdjoint.op, ⟨.op <| .ofIsRightAdjoint _⟩⟩

instance IsLeftAdjoint.leftOp {F : C ⥤ Dᵒᵖ} [F.IsLeftAdjoint] : F.leftOp.IsRightAdjoint :=
  ⟨F.rightAdjoint.rightOp, ⟨.leftOp <| .ofIsLeftAdjoint _⟩⟩

-- TODO: Do we need to introduce `Adjunction.leftUnop`?
instance IsRightAdjoint.leftOp {F : C ⥤ Dᵒᵖ} [F.IsRightAdjoint] : F.leftOp.IsLeftAdjoint :=
  inferInstanceAs (F.op ⋙ (opOpEquivalence D).functor).IsLeftAdjoint

-- TODO: Do we need to introduce `Adjunction.rightUnop`?
instance IsLeftAdjoint.rightOp {F : Cᵒᵖ ⥤ D} [F.IsLeftAdjoint] : F.rightOp.IsRightAdjoint :=
  inferInstanceAs ((opOpEquivalence C).inverse ⋙ F.op).IsRightAdjoint

instance IsRightAdjoint.rightOp {F : Cᵒᵖ ⥤ D} [F.IsRightAdjoint] : F.rightOp.IsLeftAdjoint :=
  ⟨F.leftAdjoint.leftOp, ⟨.rightOp <| .ofIsRightAdjoint _⟩⟩

end Functor
end CategoryTheory
