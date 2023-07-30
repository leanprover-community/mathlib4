import Mathlib.CategoryTheory.Limits.HasLimitsConstAdj
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Localization.Pi
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.Equivalence
import Mathlib.CategoryTheory.Localization.HasLocalization

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
  have : CatCommSq E.functor L₁ L₂ E'.functor :=
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


namespace FiniteProductsAux

variable (C)
variable (J : Type) [Finite J] [W.ContainsIdentities]
  [HasProductsOfShape J C] (hW : W.IsStableUnderProductsOfShape J)

def G : C ⥤ (Discrete J ⥤ C) := Functor.const (Discrete J)
noncomputable def F : ((Discrete J) ⥤ C) ⥤ C := lim
noncomputable def adj : G C J ⊣ F C J := constLimAdj
variable {C}
def L' : (Discrete J ⥤ C) ⥤ (Discrete J ⥤ D) := (whiskeringRight (Discrete J) C D).obj L
variable (D)
def G' : D ⥤ (Discrete J ⥤ D) := Functor.const (Discrete J)
def W' := W.functorCategory (Discrete J)
variable {D}
lemma hF : (W' W J).IsInvertedBy (F C J ⋙ L) := fun _ _ f hf =>
  Localization.inverts L W ((F C J).map f) (hW.lim_map f hf)
instance : (L' L J).IsLocalization (W' W J) := by
  dsimp [L', W']
  infer_instance
variable {J}
noncomputable def F' : (Discrete J ⥤ D) ⥤ D :=
  Localization.lift (F C J ⋙ L) (hF L W J hW) (L' L J)
@[simp] instance : CatCommSq (G C J) L (L' L J) (G' D J) := ⟨(Functor.compConstIso _ _).symm⟩
noncomputable instance : CatCommSq (F C J) (L' L J) L (F' L W hW) :=
  ⟨(Localization.fac _ _ _).symm⟩
noncomputable def adj' : G' D J ⊣ F' L W hW := (adj C J).localization L W (L' L J) (W' W J) _ _

lemma isIso_limitComparisonOfConstAdjunction :
  IsIso (limitComparisonOfConstAdjunction (adj C J) (adj' L W hW) L) := by
  have : ∀ (X : Discrete J ⥤ C),
    IsIso ((limitComparisonOfConstAdjunction (adj C J) (adj' L W hW) L).app X) := by
      intro X
      simp only [limitComparisonOfConstAdjunction, Functor.comp_obj, whiskeringRight_obj_obj,
        Adjunction.natTransHomEquiv_apply_app, whiskeringRight_obj_map, adj',
        Adjunction.localization_unit_app, assoc]
      dsimp [CatCommSq.iso]
      simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]
      erw [← NatTrans.naturality, ← L.map_comp_assoc, Adjunction.right_triangle_components]
      infer_instance
  exact NatIso.isIso_of_isIso_app _

end FiniteProductsAux

lemma hasProductsOfShape (J : Type) [Finite J] [W.ContainsIdentities] [HasProductsOfShape J C]
    (hW : W.IsStableUnderProductsOfShape J):
  HasProductsOfShape J D := hasLimitsOfShape_of_const_adjunction (FiniteProductsAux.adj' L W hW)

lemma hasFiniteProducts [W.ContainsIdentities] [HasFiniteProducts C]
    [W.IsStableUnderFiniteProducts] : HasFiniteProducts D :=
  ⟨fun _ => hasProductsOfShape L W _
    (MorphismProperty.IsStableUnderFiniteProducts.isStableUnderProductsOfShape W _)⟩

noncomputable def preservesProductsOfShape (J : Type) [Finite J] [W.ContainsIdentities]
    [HasProductsOfShape J C] (hW : W.IsStableUnderProductsOfShape J) :
    PreservesLimitsOfShape (Discrete J) L := by
  have := FiniteProductsAux.isIso_limitComparisonOfConstAdjunction L W hW
  exact preservesLimitsOfShape_of_const_adjunction (FiniteProductsAux.adj C J)
    (FiniteProductsAux.adj' L W hW) L

noncomputable def preservesFiniteProducts [W.ContainsIdentities]
    [HasFiniteProducts C] [W.IsStableUnderFiniteProducts] :
    PreservesFiniteProducts L := ⟨by
  intro J hJ
  exact preservesProductsOfShape L W J
    (MorphismProperty.IsStableUnderFiniteProducts.isStableUnderProductsOfShape W _)⟩

instance [W.ContainsIdentities] [HasFiniteProducts C] [W.IsStableUnderFiniteProducts] :
    HasFiniteProducts (W.Localization) := hasFiniteProducts W.Q W

noncomputable instance [W.ContainsIdentities] [HasFiniteProducts C]
    [W.IsStableUnderFiniteProducts] : PreservesFiniteProducts W.Q := preservesFiniteProducts W.Q W

section

variable [W.HasLocalization]

instance [W.ContainsIdentities] [HasFiniteProducts C] [W.IsStableUnderFiniteProducts] :
    HasFiniteProducts (W.Localization') := hasFiniteProducts W.Q' W

noncomputable instance [W.ContainsIdentities] [HasFiniteProducts C]
    [W.IsStableUnderFiniteProducts] : PreservesFiniteProducts W.Q' := preservesFiniteProducts W.Q' W

end

end Localization

end CategoryTheory
