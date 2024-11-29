/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Preservation of Kan extensions

We define preservation of Kan extensions and show that pointwise Kan extensions preserve
representable functors.
-/

universe v₁ v₂ v₃ v₄ u u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category Limits

namespace Functor

section

variable {C D H I : Type*} [Category C] [Category D] [Category H] [Category I]

/-- Whisker a left extension by a functor `G : H ⥤ I`. -/
@[simps!]
def LeftExtension.postcomp₂ {L : C ⥤ D} {F : C ⥤ H} (G : H ⥤ I) :
    LeftExtension L F ⥤ LeftExtension L (F ⋙ G) :=
  StructuredArrow.map₂ (F := (whiskeringRight _ _ _).obj G) (G := (whiskeringRight _ _ _).obj G)
    (𝟙 _) (𝟙 _)

/-- Whisker a right extension by a functor `G : H ⥤ I`. -/
@[simps!]
def RightExtension.postcomp₂ {L : C ⥤ D} {F : C ⥤ H} (G : H ⥤ I) :
    RightExtension L F ⥤ RightExtension L (F ⋙ G) :=
  CostructuredArrow.map₂ (F := (whiskeringRight _ _ _).obj G) (G := (whiskeringRight _ _ _).obj G)
    (𝟙 _) (𝟙 _)

/-- We say that `G` preserves left Kan extensions of `F` along `L` if whiskering a left extension
of `F` along `L` by `G` preserves universality. -/
class PreservesLeftKanExtension (L : C ⥤ D) (F : C ⥤ H) (G : H ⥤ I) : Prop where
  preserves : ∀ {E : LeftExtension L F},
    E.IsUniversal → Nonempty ((LeftExtension.postcomp₂ G).obj E).IsUniversal

/-- If `G` preserves left Kan extensions, then `LeftExtension.postcomp₂ G` preserves
universality. -/
noncomputable def LeftExtension.isUniversalOfPreserves {L : C ⥤ D} {F : C ⥤ H} (G : H ⥤ I)
    [PreservesLeftKanExtension L F G] {E : LeftExtension L F} (hE : E.IsUniversal) :
    ((LeftExtension.postcomp₂ G).obj E).IsUniversal :=
  PreservesLeftKanExtension.preserves hE |>.some

/-- We say that `G` preserves right Kan extensions of `F` along `L` if whiskering a right extension
of `F` along `L` by `G` preserves universality. -/
class PreservesRightKanExtension (L : C ⥤ D) (F : C ⥤ H) (G : H ⥤ I) : Prop where
  preserves : ∀ {E : RightExtension L F},
    E.IsUniversal → Nonempty ((RightExtension.postcomp₂ G).obj E).IsUniversal

/-- If `G` preserves right Kan extensions, then `RightExtension.postcomp₂ G` preserves
universality. -/
noncomputable def RightExtension.isUniversalOfPreserves {L : C ⥤ D} {F : C ⥤ H} (G : H ⥤ I)
    [PreservesRightKanExtension L F G] {E : RightExtension L F} (hE : E.IsUniversal) :
    ((RightExtension.postcomp₂ G).obj E).IsUniversal :=
  PreservesRightKanExtension.preserves hE |>.some

attribute [local instance] preservesColimit_rightOp

instance (L : C ⥤ D) (F : C ⥤ H) (F' : H ⥤ I) [Full F'] [Faithful F'] :
    PreservesLeftKanExtension L F F' := sorry

instance (L : C ⥤ D) (F : C ⥤ H) (F' : H ⥤ I) [Full F'] [Faithful F'] :
    PreservesRightKanExtension L F F' := sorry

instance (L : C ⥤ D) (F : C ⥤ H) [HasPointwiseLeftKanExtension L F] (h : H) :
    PreservesLeftKanExtension L F (yoneda.obj h).rightOp where
  preserves {E} hE := by
    refine ⟨LeftExtension.IsPointwiseLeftKanExtension.isUniversal fun d => ?_⟩
    let isPointwise : E.IsPointwiseLeftKanExtension :=
      isPointwiseLeftKanExtensionOfHasLeftKanExtension hE
    let isColimit := isColimitOfPreserves (yoneda.obj h).rightOp (isPointwise d)
    exact IsColimit.ofIsoColimit isColimit (Cocones.ext (Iso.refl _))

instance (L : C ⥤ D) (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (h : Hᵒᵖ) :
    PreservesRightKanExtension L F (coyoneda.obj h) where
  preserves {E} hE := by
    refine ⟨RightExtension.IsPointwiseRightKanExtension.isUniversal fun d => ?_⟩
    let isPointwise : E.IsPointwiseRightKanExtension :=
      isPointwiseRightKanExtensionOfHasRightKanExtension hE
    let isLimit := isLimitOfPreserves (coyoneda.obj h) (isPointwise d)
    exact IsLimit.ofIsoLimit isLimit (Cones.ext (Iso.refl _))

def rightOpping : (Cᵒᵖ ⥤ D)ᵒᵖ ⥤ (C ⥤ Dᵒᵖ) where
  obj F := F.unop.rightOp
  map {F G} η :=
    { app := fun X => Quiver.Hom.op (η.unop.app (Opposite.op X))
      naturality := sorry }

end

-- variable {C D H I : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} H] [Category.{u} I]
variable {C : Type u₁} {D : Type u₂} {H : Type u₃} {I : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H] [Category.{v₄} I]

-- These universes would force all categories to be locally small in my example...

noncomputable def goalEquiv (L : C ⥤ D) (F : C ⥤ H) (E : LeftExtension L F)
    (hE : E.IsPointwiseLeftKanExtension)
    (h : H) [PreservesLeftKanExtension L F (yoneda.obj h).rightOp] (d : D) :
    (E.right.obj d ⟶ h) ≃
      (L.op ⋙ (yoneda.obj d) ⋙ uliftFunctor.{v₃} ⟶ F.op ⋙ (yoneda.obj h) ⋙ uliftFunctor.{v₂}) := by
  let h₀ : ((LeftExtension.postcomp₂ (yoneda.obj h).rightOp).obj E).IsUniversal :=
    LeftExtension.isUniversalOfPreserves (yoneda.obj h).rightOp hE.isUniversal
  let q : (L.op ⋙ E.right.op) ⋙ yoneda.obj h ⟶ F.op ⋙ yoneda.obj h :=
    whiskerRight (NatTrans.op E.hom) (yoneda.obj h)
  let h₁ : ((LeftExtension.postcomp₂ (yoneda.obj h).rightOp).obj E).op.IsUniversal :=
    LeftExtension.isUniversal_op h₀
  let h₂ : ((RightExtension.postcomp₂ ((opOpEquivalence _).functor)).obj
    ((LeftExtension.postcomp₂ (yoneda.obj h).rightOp).obj E).op).IsUniversal :=
    RightExtension.isUniversalOfPreserves _ h₁
  let hx : (Functor.op E.right ⋙ yoneda.obj h).IsRightKanExtension q :=
    ⟨⟨h₂⟩⟩
  let hx' : (Functor.op E.right ⋙ yoneda.obj h ⋙ uliftFunctor.{v₂}).IsRightKanExtension (whiskerRight q uliftFunctor.{v₂}) :=
    sorry
  let r' := homEquivOfIsRightKanExtension (Functor.op E.right ⋙ yoneda.obj h ⋙ uliftFunctor.{v₂}) (whiskerRight q uliftFunctor.{v₂}) (yoneda.obj d ⋙ uliftFunctor.{v₃})
  let r'' := (yonedaEquiv.symm.trans r')
  exact r''

noncomputable def goalIso (L : C ⥤ D) (F : C ⥤ H) (E : LeftExtension L F)
    (hE : E.IsPointwiseLeftKanExtension) (h : H)
    [PreservesLeftKanExtension L F (yoneda.obj h).rightOp] :
    E.right.op ⋙ yoneda.obj h ⋙ uliftFunctor.{u₁} ≅ yoneda.op ⋙ ((whiskeringLeft _ _ _).obj L.op).op ⋙
      yoneda.obj (F.op ⋙ yoneda.obj h) :=
  NatIso.ofComponents (fun d => Equiv.toIso (Equiv.ulift.trans <| goalEquiv L F E hE h d.unop)) sorry


end Functor

end CategoryTheory
