/-
Copyright (c) 2020 Kim Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Preserving products

Constructions to relate the notions of preserving products and reflecting products
to concrete fans.

In particular, we show that `piComparison G f` is an isomorphism iff `G` preserves
the limit of `f`.
-/


noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable {J : Type w} (f : J → C)

/-- The image of a fan by a functor. -/
@[simps!]
def Fan.map (c : Fan f) : Fan (G.obj ∘ f) :=
  Fan.mk (G.obj c.pt) (fun j => G.map (c.proj j))

def Fan.isLimitMapCongr (H : C ⥤ D) (i : G ≅ H) (c : Fan f) :
    IsLimit (c.map G) ≃ IsLimit (c.map H) :=
  Fan.isLimitCongr _ _ (i.app c.pt) (fun _ => i.app _) (fun _ => (i.hom.naturality _).symm)

/-- The map (as a cone) of a fan is limit iff the map (as a fan) is limit. -/
def Fan.isLimitMapConeEquiv (c : Fan f) : IsLimit (G.mapCone c) ≃ IsLimit (c.map G) :=
  (IsLimit.postcomposeHomEquiv Discrete.natIsoFunctor _).symm.trans <| IsLimit.equivIsoLimit <|
    Cones.ext (Iso.refl _) (by aesop_cat)

/-- The map of a fan is a limit iff the fan consisting of the mapped morphisms is a limit. This
essentially lets us commute `Fan.mk` with `Functor.mapCone`.
-/
def isLimitMapConeFanMkEquiv {P : C} (g : ∀ j, P ⟶ f j) :
    IsLimit (Functor.mapCone G (Fan.mk P g)) ≃
      IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j)) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  · refine Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  refine Cones.ext (Iso.refl _) fun j =>
      by dsimp; cases j; simp

/-- The property of preserving products expressed in terms of fans. -/
def isLimitFanMkObjOfIsLimit [PreservesLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ g)) :
    IsLimit (Fan.mk (G.obj P) fun j => G.map (g j) : Fan fun j => G.obj (f j)) :=
  isLimitMapConeFanMkEquiv _ _ _ (PreservesLimit.preserves t)

def isLimitFanMapOfIsLimit [PreservesLimit (Discrete.functor f) G] (c : Fan f)
    (hc : IsLimit c) : IsLimit (c.map G) :=
  Fan.isLimitMapConeEquiv _ _ _ (PreservesLimit.preserves hc)

/-- The property of reflecting products expressed in terms of fans. -/
def isLimitOfIsLimitFanMkObj [ReflectsLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j))) :
    IsLimit (Fan.mk P g) :=
  ReflectsLimit.reflects ((isLimitMapConeFanMkEquiv _ _ _).symm t)

section

variable [HasProduct f]

/--
If `G` preserves products and `C` has them, then the fan constructed of the mapped projection of a
product is a limit.
-/
def isLimitOfHasProductOfPreservesLimit [PreservesLimit (Discrete.functor f) G] :
    IsLimit (Fan.mk _ fun j : J => G.map (Pi.π f j) : Fan fun j => G.obj (f j)) :=
  isLimitFanMkObjOfIsLimit G f _ (productIsProduct _)

variable [HasProduct fun j : J => G.obj (f j)]

/-- If `pi_comparison G f` is an isomorphism, then `G` preserves the limit of `f`. -/
def PreservesProduct.ofIsoComparison [i : IsIso (piComparison G f)] :
    PreservesLimit (Discrete.functor f) G := by
  apply preservesLimitOfPreservesLimitCone (productIsProduct f)
  apply (isLimitMapConeFanMkEquiv _ _ _).symm _
  refine @IsLimit.ofPointIso _ _ _ _ _ _ _
    (limit.isLimit (Discrete.functor fun j : J => G.obj (f j))) ?_
  apply i

variable [PreservesLimit (Discrete.functor f) G]

/--
If `G` preserves limits, we have an isomorphism from the image of a product to the product of the
images.
-/
def PreservesProduct.iso : G.obj (∏ᶜ f) ≅ ∏ᶜ fun j => G.obj (f j) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasProductOfPreservesLimit G f) (limit.isLimit _)

@[simp]
theorem PreservesProduct.iso_hom : (PreservesProduct.iso G f).hom = piComparison G f :=
  rfl

instance : IsIso (piComparison G f) := by
  rw [← PreservesProduct.iso_hom]
  infer_instance

/-- A fan in `C` is limit iff it is after the application of `coyoneda.obj X` for all `X : Cᵒᵖ`. -/
def Fan.isLimitCoyonedaEquiv (c : Fan f) :
    IsLimit c ≃ ∀ (X : Cᵒᵖ), IsLimit (c.map (coyoneda.obj X)) :=
  (Cone.isLimitCoyonedaEquiv c).trans
    (Equiv.piCongrRight (fun X => c.isLimitMapConeEquiv (coyoneda.obj X)))

end

/-- The image of a cofan by a functor. -/
@[simps!]
def Cofan.map (c : Cofan f) : Cofan (G.obj ∘ f) :=
  Cofan.mk (G.obj c.pt) (fun j => G.map (c.inj j))

/-- The map (as a cocone) of a cofan is colimit iff the map (as a cofan) is colimit. -/
def Cofan.isColimitMapCoconeEquiv (c : Cofan f) : IsColimit (G.mapCocone c) ≃ IsColimit (c.map G) :=
  (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm.trans <|
    IsColimit.equivIsoColimit <| Cocones.ext (Iso.refl _) (by aesop_cat)

/-- The map of a cofan is a colimit iff the cofan consisting of the mapped morphisms is a colimit.
This essentially lets us commute `Cofan.mk` with `Functor.mapCocone`.
-/
def isColimitMapCoconeCofanMkEquiv {P : C} (g : ∀ j, f j ⟶ P) :
    IsColimit (Functor.mapCocone G (Cofan.mk P g)) ≃
      IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j)) := by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  · refine Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  refine Cocones.ext (Iso.refl _) fun j => by dsimp; cases j; simp

/-- The property of preserving coproducts expressed in terms of cofans. -/
def isColimitCofanMkObjOfIsColimit [PreservesColimit (Discrete.functor f) G] {P : C}
    (g : ∀ j, f j ⟶ P) (t : IsColimit (Cofan.mk _ g)) :
    IsColimit (Cofan.mk (G.obj P) fun j => G.map (g j) : Cofan fun j => G.obj (f j)) :=
  isColimitMapCoconeCofanMkEquiv _ _ _ (PreservesColimit.preserves t)

def isColimitCofanMapOfIsColimit [PreservesColimit (Discrete.functor f) G] (c : Cofan f)
    (hc : IsColimit c) : IsColimit (c.map G) :=
  Cofan.isColimitMapCoconeEquiv _ _ _ (PreservesColimit.preserves hc)

/-- The property of reflecting coproducts expressed in terms of cofans. -/
def isColimitOfIsColimitCofanMkObj [ReflectsColimit (Discrete.functor f) G] {P : C}
    (g : ∀ j, f j ⟶ P)
    (t : IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j))) :
    IsColimit (Cofan.mk P g) :=
  ReflectsColimit.reflects ((isColimitMapCoconeCofanMkEquiv _ _ _).symm t)

section

variable [HasCoproduct f]

/-- If `G` preserves coproducts and `C` has them,
then the cofan constructed of the mapped inclusion of a coproduct is a colimit.
-/
def isColimitOfHasCoproductOfPreservesColimit [PreservesColimit (Discrete.functor f) G] :
    IsColimit (Cofan.mk _ fun j : J => G.map (Sigma.ι f j) : Cofan fun j => G.obj (f j)) :=
  isColimitCofanMkObjOfIsColimit G f _ (coproductIsCoproduct _)

variable [HasCoproduct fun j : J => G.obj (f j)]

/-- If `sigma_comparison G f` is an isomorphism, then `G` preserves the colimit of `f`. -/
def PreservesCoproduct.ofIsoComparison [i : IsIso (sigmaComparison G f)] :
    PreservesColimit (Discrete.functor f) G := by
  apply preservesColimitOfPreservesColimitCocone (coproductIsCoproduct f)
  apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
  refine @IsColimit.ofPointIso _ _ _ _ _ _ _
    (colimit.isColimit (Discrete.functor fun j : J => G.obj (f j))) ?_
  apply i

variable [PreservesColimit (Discrete.functor f) G]

/-- If `G` preserves colimits,
we have an isomorphism from the image of a coproduct to the coproduct of the images.
-/
def PreservesCoproduct.iso : G.obj (∐ f) ≅ ∐ fun j => G.obj (f j) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCoproductOfPreservesColimit G f)
    (colimit.isColimit _)

@[simp]
theorem PreservesCoproduct.inv_hom : (PreservesCoproduct.iso G f).inv = sigmaComparison G f := rfl

instance : IsIso (sigmaComparison G f) := by
  rw [← PreservesCoproduct.inv_hom]
  infer_instance

end

section

/-- Implementation detail of `Cofan.isColimitYonedaEquiv`. -/
@[simps!]
private def oppositeInverseCompFunctorOp : (Discrete.opposite J).inverse ⋙ (Discrete.functor f).op ≅
    Discrete.functor (fun j => Opposite.op (f j)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by rintro ⟨j₁⟩ ⟨j₂⟩ ⟨⟨⟨⟩⟩⟩; simp)

/-- A cofan in `C` is colimit iff it becomes limit after the application of `yoneda.obj X` for
all `X : C`. -/
def Cofan.isColimitYonedaEquiv (c : Cofan f) :
    IsColimit c ≃ ∀ (X : C), IsLimit ((Cofan.op c).map (yoneda.obj X)) :=
  (Limits.Cocone.isColimitYonedaEquiv c).trans <| Equiv.piCongrRight fun X =>
    (IsLimit.whiskerEquivalenceEquiv (Discrete.opposite _).symm).trans
      (Equiv.trans
        ((IsLimit.postcomposeHomEquiv
          (isoWhiskerRight (oppositeInverseCompFunctorOp f) (yoneda.obj X)) _).symm.trans
            (IsLimit.equivIsoLimit (by exact Cones.ext (Iso.refl _) (by aesop_cat))))
        (c.op.isLimitMapConeEquiv (yoneda.obj X)))

end

end CategoryTheory.Limits
