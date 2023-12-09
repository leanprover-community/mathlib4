import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.HasSheafify

namespace CategoryTheory

open CategoryTheory.Limits Opposite

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable (D : Type w) [Category.{max v u} D]

variable [ConcreteCategory.{max v u} D]

variable [PreservesLimits (forget D)]

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]

variable [ReflectsIsomorphisms (forget D)]

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

instance hasSheafifyOfPlusPlus : HasWeakSheafify J D where
  isRightAdjoint := ⟨inferInstance⟩

-- instance : HasWeakSheafify J TypeMax.{v, u} := inferInstance
  -- @hasSheafifyOfPlusPlus C _ J TypeMax.{v, u} _ _ _ _ _
  --   (fun _ ↦ (inferInstance : Limits.PreservesColimitsOfShape _ (𝟭 _))) _

/--
The functor `plusPlusSheaf`, doing the plus construction twice, is isomorphic to any choice of
sheafification functor (by uniqueness of left adjoints).
-/
noncomputable
def presheafToSheafIsoPlusPlus : plusPlusSheaf J D ≅ presheafToSheaf J D :=
  Adjunction.leftAdjointUniq (plusPlusAdjunction J D) (sheafificationAdjunction J D)

-- porting note: added to ease the port of CategoryTheory.Sites.LeftExact
-- in mathlib, this was `by refl`, but here it would timeout
/--
"Sheafification" as an endofunctor of the presheaf category is isomorphic to sheafification
followed by inclusion.
-/
@[simps! hom_app inv_app]
noncomputable
def GrothendieckTopology.sheafificationIsoPresheafToSheafCompSheafToPreasheaf :
    J.sheafification D ≅ presheafToSheaf J D ⋙ sheafToPresheaf J D :=
  (NatIso.ofComponents fun P => Iso.refl _) ≪≫
    isoWhiskerRight (presheafToSheafIsoPlusPlus J D) (sheafToPresheaf J D)

end CategoryTheory
