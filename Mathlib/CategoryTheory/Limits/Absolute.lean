import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Whiskering

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category

namespace Limits

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
  {F : J ⥤ C} (c : Cocone F)

structure IsAbsoluteColimit extends IsColimit c where
  isColimitMapCoconeYoneda : IsColimit ((yoneda ⋙
    (whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{u₁}).mapCocone c)

instance : Subsingleton (IsAbsoluteColimit c) :=
  ⟨fun ⟨_, _⟩ ⟨_, _⟩ => by simp⟩

namespace IsAbsoluteColimit

variable {c} (hc : IsAbsoluteColimit c) {D : Type u₃} [Category.{v₃} D]

/-def isColimitMapCocone (G : C ⥤ D) : IsColimit (G.mapCocone c) := by
  have := hc
  sorry

def isAbsoluteColimitMapCocone (G : C ⥤ D) : IsAbsoluteColimit (G.mapCocone c) where
  toIsColimit := hc.isColimitMapCocone G
  isColimitMapCoconeYoneda := hc.isColimitMapCocone (G ⋙ yoneda ⋙
      (whiskeringRight Dᵒᵖ _ _).obj uliftFunctor)

def preservesColimit (G : C ⥤ D) : PreservesColimit F G :=
  preservesColimitOfPreservesColimitCocone hc.toIsColimit (hc.isColimitMapCocone G)-/

def ofIso (hc : IsAbsoluteColimit c) {c' : Cocone F} (e : c ≅ c') :
    IsAbsoluteColimit c' where
  toIsColimit := IsColimit.ofIsoColimit hc.toIsColimit e
  isColimitMapCoconeYoneda :=
    IsColimit.ofIsoColimit hc.isColimitMapCoconeYoneda
      ((Cocones.functoriality F _).mapIso e)

def equivOfIso {c' : Cocone F} (e : c ≅ c') :
    IsAbsoluteColimit c ≃ IsAbsoluteColimit c' where
  toFun h := ofIso h e
  invFun h := ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end IsAbsoluteColimit

end Limits

end CategoryTheory
