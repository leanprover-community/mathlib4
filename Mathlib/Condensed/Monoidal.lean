import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Condensed.Light.Module
import Mathlib.Condensed.Module
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib

universe u

open CategoryTheory MonoidalCategory MonoidalClosed MonoidalClosed.FunctorCategory Condensed
  Enriched.FunctorCategory EnrichedCategory EnrichedOrdinaryCategory Limits Monoidal

attribute [local instance] Sheaf.monoidalCategory

section

variable {C A : Type*} [Category C] [Category A] (J : GrothendieckTopology C)
    [MonoidalCategory A]
    -- [(J.W (A := A)).IsMonoidal] -- braidedCategoryOfFullyFaithful

-- def braidedCategory [BraidedCategory A] [MonoidalClosed A] [HasWeakSheafify J A]
--     [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
--     [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]  :
--     BraidedCategory (Sheaf J A) :=
--   braidedCategoryOfFullyFaithful (sheafToPresheaf J A)

noncomputable def monoidalClosed [SymmetricCategory A] [MonoidalClosed A] [HasWeakSheafify J A]
    [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
    [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂] :
    MonoidalClosed (Sheaf J A) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)

-- instance : SymmetricCategory (Sheaf J A) where
--   braiding := sorry
--   braiding_naturality_right := sorry
--   braiding_naturality_left := sorry
--   hexagon_forward := sorry
--   hexagon_reverse := sorry
--   symmetry := sorry

end

section

variable {R : Type (u + 1)} [CommRing R]

noncomputable instance : MonoidalCategory (CondensedMod R) :=
  Sheaf.monoidalCategory _ _

noncomputable instance : MonoidalClosed (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat R)) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)

noncomputable instance : MonoidalClosed (CondensedMod R) :=
  inferInstanceAs (MonoidalClosed (Sheaf _ _))

end

section

variable {R : Type u} [CommRing R]

#synth BraidedCategory (ModuleCat.{u} R)

#synth MonoidalClosed (ModuleCat.{u} R)

instance : ∀ (F₁ F₂ : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat R),
  HasEnrichedHom (ModuleCat R) F₁ F₂ := sorry

instance : ∀ (F₁ F₂ : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat R),
    HasFunctorEnrichedHom (ModuleCat R) F₁ F₂ := sorry

#check (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R)

instance : HasLimitsOfSize.{u, u} (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R) := inferInstance

variable (F₁ F₂ : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat R) (j : LightProfinite.{u}ᵒᵖ)

#check (multicospanIndexEnd (diagram (ModuleCat R) (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂))).multicospan

#check (multicospanIndexEnd (diagram (ModuleCat.{u} R) (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂))).fstTo

instance : EssentiallySmall.{u} (WalkingMulticospan
    (multicospanIndexEnd (diagram (ModuleCat.{u} R) (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂))).fstTo
    (multicospanIndexEnd (diagram (ModuleCat.{u} R) (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂))).sndTo) := sorry

-- instance : ((coherentTopology LightProfinite).W (A := ModuleCat.{u} R)).IsMonoidal :=
--   haveI : ∀ (F₁ F₂ : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat R),
--     HasEnrichedHom (ModuleCat R) F₁ F₂ := sorry
--   haveI : ∀ (F₁ F₂ : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat R),
--     HasFunctorEnrichedHom (ModuleCat R) F₁ F₂ := sorry
--   GrothendieckTopology.W.monoidal

noncomputable instance : MonoidalCategory (LightCondMod R) :=
    Sheaf.monoidalCategory _ _

end

section

variable (C D : Type*) [Category C] [Category D] (e : C ≌ D)
    [MonoidalCategory C]

example : MonoidalCategory D := by exact Monoidal.transport e

noncomputable example [MonoidalClosed C] [SymmetricCategory C] :
      letI : MonoidalCategory D := Monoidal.transport e
      haveI : e.functor.Monoidal := inferInstanceAs (equivalenceTransported e).functor.Monoidal
      MonoidalClosed D :=
    letI : MonoidalCategory D := Monoidal.transport e
    haveI : e.functor.Monoidal := inferInstanceAs (equivalenceTransported e).functor.Monoidal
    Monoidal.Reflective.monoidalClosed e.toAdjunction

example [SymmetricCategory C] :
    letI : MonoidalCategory D := Monoidal.transport e
    SymmetricCategory D := by sorry

end
#min_imports
