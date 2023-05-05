import Mathlib.CategoryTheory.Limits.HasLimitsConstAdj
import Mathlib.CategoryTheory.Localization.Pi
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.Equivalence

namespace CategoryTheory

open Category Limits

universe v u v' u'

@[simps]
def piEquivalenceFunctorDiscrete (J : Type u') (C : Type u) [Category.{v} C] :
    (∀ (_ : J), C) ≌ (Discrete J ⥤ C) where
  functor :=
    { obj := fun F => Discrete.functor F
      map := fun f => Discrete.natTrans (fun j => f j.as) }
  inverse :=
    { obj := fun F j => F.obj ⟨j⟩
      map := fun f j => f.app ⟨j⟩ }
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun F => (NatIso.ofComponents (fun j => Iso.refl _)
    (by
      rintro ⟨x⟩ ⟨y⟩ f
      obtain rfl : x = y := Discrete.eq_of_hom f
      obtain rfl : f = 𝟙 _ := by cases f ; rfl
      dsimp
      simp))) (by aesop_cat)

namespace Localization

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W]

instance whiskeringRightDiscrete_isLocalization (J : Type) [Finite J] [W.ContainsIdentities]:
    ((whiskeringRight (Discrete J) C D).obj L).IsLocalization (W.functorCategory _) := by
  let E := piEquivalenceFunctorDiscrete J C
  let E' := piEquivalenceFunctorDiscrete J D
  let L₂ := (whiskeringRight (Discrete J) C D).obj L
  let L₁ := Functor.pi (fun (_ : J) => L)
  let W₁ := MorphismProperty.pi (fun (_ : J) => W)
  let W₂ := MorphismProperty.functorCategory W (Discrete J)
  have : CatCommSq L₁ E.functor L₂ E'.functor :=
    ⟨(Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ E'.counitIso.symm ≪≫
      Functor.associator _ _ _≪≫ isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (by exact Iso.refl _) _) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight E.unitIso.symm L₁) _ ≪≫ isoWhiskerRight L₁.leftUnitor _⟩
  refine' Functor.IsLocalization.of_equivalences L₁ W₁ L₂ W₂ E E' _ _
  . intro X Y f hf
    exact MorphismProperty.subset_isoClosure _ _ (fun ⟨j⟩ => hf j)
  . intro X Y f hf
    have : ∀ (j : Discrete J), IsIso ((L₂.map f).app j) :=
      fun j => Localization.inverts L W _ (hf j)
    apply NatIso.isIso_of_isIso_app

lemma hasProductsOfShape (J : Type) [Finite J] [W.ContainsIdentities]
    [HasProductsOfShape J C] (hW : W.IsStableUnderProductsOfShape J) :
    HasProductsOfShape J D := by
  let G : C ⥤ _ := Functor.const (Discrete J)
  let F : ((Discrete J) ⥤ C) ⥤ C := lim
  let adj : G ⊣ F := constLimAdj
  let L' := (whiskeringRight (Discrete J) C D).obj L
  let G' : D ⥤ _ := Functor.const (Discrete J)
  let W' := W.functorCategory (Discrete J)
  have hF : W'.IsInvertedBy (F ⋙ L) := fun X Y f hf =>
    Localization.inverts L W (F.map f) (hW.lim_map f hf)
  let F' := Localization.lift (F ⋙ L) hF L'
  have : CatCommSq L G L' G' := ⟨NatIso.ofComponents (fun X =>
    NatIso.ofComponents (fun j => Iso.refl _) (by aesop_cat)) (by aesop_cat)⟩
  have : CatCommSq L' F L F' := ⟨(Localization.fac _ _ _).symm⟩
  exact hasLimitsOfShape_of_const_adjunction (adj.localization L W L' W' G' F')

lemma hasFiniteProducts [W.ContainsIdentities] [HasFiniteProducts C]
    [W.IsStableUnderFiniteProducts] : HasFiniteProducts D :=
  ⟨fun _ => hasProductsOfShape L W _
    (MorphismProperty.IsStableUnderFiniteProducts.isStableUnderProductsOfShape W _)⟩

instance [W.ContainsIdentities] [HasFiniteProducts C] [W.IsStableUnderFiniteProducts] :
    HasFiniteProducts (W.Localization) := hasFiniteProducts W.Q W

end Localization

end CategoryTheory
