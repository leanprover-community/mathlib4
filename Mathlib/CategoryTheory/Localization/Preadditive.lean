import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Internal.Preadditive

namespace CategoryTheory

open Category Limits ZeroObject

lemma Limits.hasZeroObject_of_additive_functor {C D : Type _} [Category C] [Category D]
    (F : C ⥤ D) [Preadditive C] [Preadditive D] [F.Additive] [HasZeroObject C] :
    HasZeroObject D :=
  ⟨⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩⟩

namespace Localization

variable {C D : Type _} [Category C] [Category D] [HasFiniteProducts C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [HasFiniteProducts D]
  [PreservesFiniteProducts L]

lemma preadditive [Preadditive C] : Preadditive D := by
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


variable [Preadditive C] [HasFiniteProducts W.Localization]
  [PreservesFiniteProducts W.Q]

noncomputable instance : Preadditive W.Localization := preadditive W.Q W

noncomputable instance : W.Q.Additive := Functor.additive_of_preserves_finite_products _

end Localization

end CategoryTheory
