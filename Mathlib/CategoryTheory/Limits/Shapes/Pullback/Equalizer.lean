/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Equalizers as pullbacks of products

Also see `CategoryTheory.Limits.Constructions.Equalizers` for very similar results.

-/

universe v u

open CategoryTheory.Category

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y Z : C} (f g : X ⟶ Y)

/-- If `e` is an equalizer of `f g : X ⟶ Y`, then `e` is also the pullback of the diagonal map
`Y ⟶ Y ⨯ Y` along `⟨f, g⟩ : X ⟶ Y ⨯ Y`. -/
lemma isPullback_equalizer_prod' [HasBinaryProduct Y Y] (e : Fork f g) (h : IsLimit e) :
    IsPullback e.ι (e.ι ≫ f) (prod.lift f g) (diag Y) := by
  refine ⟨⟨by ext <;> simp [e.condition]⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · exact fun s ↦ h.lift (Fork.ofι s.fst (eq_of_lift_eq_diag (s.condition)))
  · exact fun s ↦ Fork.IsLimit.lift_ι h
  · exact fun s ↦ by simpa using congr($s.condition ≫ prod.fst)
  · exact fun _ _ hm _ ↦ Fork.IsLimit.hom_ext h (Eq.symm (Fork.IsLimit.lift_ι h) ▸ hm)

/-- The equalizer of `f g : X ⟶ Y` is the pullback of the diagonal map `Y ⟶ Y ⨯ Y`
along the map `⟨f, g⟩ : X ⟶ Y ⨯ Y`. -/
lemma isPullback_equalizer_prod [HasEqualizer f g] [HasBinaryProduct Y Y] :
    IsPullback (equalizer.ι f g) (equalizer.ι f g ≫ f) (prod.lift f g) (diag Y) :=
  isPullback_equalizer_prod' f g (equalizer.fork f g) (equalizerIsEqualizer' f g)

/-- If `e` is an coequalizer of `f g : X ⟶ Y`, then `e` is also the pushout of the codiagonal map
`X + X ⟶ X` along `⟨f, g⟩ : X + X ⟶ Y`. -/
lemma isPushout_coequalizer_coprod' [HasBinaryCoproduct X X] (e : Cofork f g) (h : IsColimit e) :
    IsPushout (coprod.desc f g) (codiag X) e.π (f ≫ e.π) := by
  refine ⟨⟨by ext <;> simp [e.condition]⟩, ⟨PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · exact fun s ↦ h.desc (Cofork.ofπ s.inl (eq_of_desc_eq_codiag (s.condition)))
  · exact fun s ↦ Cofork.IsColimit.π_desc h
  · exact fun s ↦ by simpa using congr(coprod.inl ≫ $s.condition)
  · exact fun _ _ hm _ ↦ Cofork.IsColimit.hom_ext h (Eq.symm (Cofork.IsColimit.π_desc h) ▸ hm)

/-- The coequalizer of `f g : X ⟶ Y` is the pushout of the diagonal map `X ⨿ X ⟶ X`
along the map `(f, g) : X ⨿ X ⟶ Y`. -/
lemma isPushout_coequalizer_coprod [HasCoequalizer f g] [HasBinaryCoproduct X X] :
    IsPushout (coprod.desc f g) (codiag X)
      (coequalizer.π f g) (f ≫ coequalizer.π f g) :=
  isPushout_coequalizer_coprod' f g (coequalizer.cofork f g) (coequalizerIsCoequalizer' f g)

end CategoryTheory.Limits
