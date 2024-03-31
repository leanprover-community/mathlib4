import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Internal.Preadditive

namespace CategoryTheory

open Category Limits ZeroObject

lemma Limits.hasZeroObject_of_additive_functor {C D : Type _} [Category C] [Category D]
    (F : C ⥤ D) [Preadditive C] [Preadditive D] [F.Additive] [HasZeroObject C] :
    HasZeroObject D :=
  ⟨⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩⟩

namespace Localization

variable {C D E : Type _} [Category C] [Category D] [Category E]

/-section

variable
  [HasFiniteProducts C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [HasFiniteProducts D]
  [PreservesFiniteProducts L]

noncomputable irreducible_def preadditive [Preadditive C] : Preadditive D := by
  have : PreservesLimitsOfShape (Discrete WalkingPair) L := PreservesFiniteProducts.preserves _
  have : PreservesLimitsOfShape (Discrete PEmpty) L := PreservesFiniteProducts.preserves _
  have : PreservesLimit (Functor.empty C) L := PreservesLimitsOfShape.preservesLimit
  let G := Preadditive.toInternalAddCommGroupCatFunctor C ⋙ L.mapInternalAddCommGroupCat
  have e : G ⋙ Internal.objFunctor _ _ ≅ L := Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ L.mapInternalAddCommGroupCatCompObjFunctorIso ≪≫
    (Functor.associator _ _ _ ).symm ≪≫
    isoWhiskerRight (Preadditive.toInternalAddCommGroupCatFunctor_comp_objFunctor C) _ ≪≫
    L.leftUnitor
  have hG : W.IsInvertedBy G := fun X Y f hf => by
    suffices IsIso ((Internal.objFunctor AddCommGroupCat D).map (G.map f)) from
      isIso_of_reflects_iso _ (Internal.objFunctor AddCommGroupCat D)
    exact (NatIso.isIso_map_iff e f).2 (Localization.inverts L W f hf)
  exact Preadditive.ofInternalAddCommGroupCat (Localization.lift G hG L)
    (Localization.liftNatIso L W (G ⋙ Internal.objFunctor AddCommGroupCat D) L _ _ e)


variable [Preadditive C]

section

variable [HasFiniteProducts W.Localization] [PreservesFiniteProducts W.Q]

noncomputable instance : Preadditive W.Localization := preadditive W.Q W

noncomputable instance : W.Q.Additive := Functor.additive_of_preserves_finite_products

end

section

variable [W.HasLocalization] [HasFiniteProducts W.Localization'] [PreservesFiniteProducts W.Q']

noncomputable instance : Preadditive W.Localization' := preadditive W.Q' W

noncomputable instance : W.Q'.Additive := Functor.additive_of_preserves_finite_products _

end

end-/

section

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

lemma liftNatTrans_zero (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    [HasZeroMorphisms E] :
    liftNatTrans L W F₁ F₂ F₁' F₂' 0 = 0 :=
  natTrans_ext L W _ _ (fun X => by simp)

variable [Preadditive E]

lemma liftNatTrans_add (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ τ' : F₁ ⟶ F₂) :
    liftNatTrans L W F₁ F₂ F₁' F₂' (τ + τ') =
      liftNatTrans L W F₁ F₂ F₁' F₂' τ + liftNatTrans L W F₁ F₂ F₁' F₂' τ' :=
  natTrans_ext L W _ _ (fun X => by simp)

end

section
-- should be moved

variable (J : Type _)

noncomputable def preservesLimitsOfShapeDiscreteOfComp (F : C ⥤ D) (G : D ⥤ E) [EssSurj F]
    [PreservesLimitsOfShape (Discrete J) F] [HasLimitsOfShape (Discrete J) C]
    [PreservesLimitsOfShape (Discrete J) (F ⋙ G)] :
    PreservesLimitsOfShape (Discrete J) G where
  preservesLimit {K} := by
    let U : J → C := fun j => F.objPreimage (K.obj ⟨j⟩)
    let e : Discrete.functor U ⋙ F ≅ K := Discrete.natIso (fun _ => F.objObjPreimageIso _)
    have : PreservesLimit (Discrete.functor U ⋙ F) G := by
      let c := Limits.getLimitCone (Discrete.functor U)
      exact preservesLimitOfPreservesLimitCone (isLimitOfPreserves F c.2) (isLimitOfPreserves (F ⋙ G) c.2)
    exact preservesLimitOfIsoDiagram G e

lemma preservesFiniteProductsOfComp (F : C ⥤ D) (G : D ⥤ E) [EssSurj F] [HasFiniteProducts C]
    [PreservesFiniteProducts F] [PreservesFiniteProducts (F ⋙ G)] :
    PreservesFiniteProducts G where
  preserves J _ := by
    have : PreservesLimitsOfShape (Discrete J) F := PreservesFiniteProducts.preserves _
    have : PreservesLimitsOfShape (Discrete J) (F ⋙ G)  := PreservesFiniteProducts.preserves _
    exact preservesLimitsOfShapeDiscreteOfComp J F G

end

/-section

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasFiniteProducts C] [HasFiniteProducts D] [HasFiniteProducts E]
  [L.Additive] [PreservesFiniteProducts L]

lemma functor_additive_iff (F : C ⥤ E) (G : D ⥤ E) [Lifting L W F G] :
    F.Additive ↔ G.Additive := by
  constructor
  · intro
    have : EssSurj L := Localization.essSurj L W
    have : PreservesFiniteProducts (L ⋙ G) := by
      constructor
      intro J _
      have : PreservesLimitsOfShape (Discrete J) F := PreservesFiniteProducts.preserves _
      exact preservesLimitsOfShapeOfNatIso (Lifting.iso L W F G).symm
    have : PreservesFiniteProducts G := preservesFiniteProductsOfComp L G
    exact Functor.additive_of_preserves_finite_products G
  · intro
    exact Functor.additive_of_iso (Lifting.iso L W F G)

end-/

end Localization

end CategoryTheory
