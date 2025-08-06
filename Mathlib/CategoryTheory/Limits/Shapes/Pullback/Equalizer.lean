/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic


/-!
# Equalizers as pullbacks of products

Also see `CategoryTheory.Limits.Constructions.Equalizers` for very similar results.

-/

universe v u

open CategoryTheory.Category CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y Z : C}

/-- If `e` is an equalizer of `f g : X ⟶ Y`, then `e` is also the pullback of the diagonal map
`Y ⟶ Y ⨯ Y` along `⟨f, g⟩ : X ⟶ Y ⨯ Y`. Fully explicit version with binary fans and forks -/
lemma isPullback_equalizer_prod_exp {p : BinaryFan Y Y} (hp : IsLimit p)
      (f g : X ⟶ Y) (e : Fork f g) (he : IsLimit e) :
    IsPullback e.ι (e.ι ≫ f)
      (hp.lift (BinaryFan.mk f g)) (hp.lift (BinaryFan.mk (𝟙 Y) (𝟙 Y))) := by
  refine
    ⟨ ⟨ BinaryFan.IsLimit.hom_ext hp (by simp) (by simp[e.condition]) ⟩,
      ⟨ PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_ ⟩ ⟩
  · exact fun s ↦ he.lift (Fork.ofι s.fst (eq_of_lift_eq_diag p hp (s.condition)))
  · exact fun s ↦ Fork.IsLimit.lift_ι he
  · exact fun s ↦ by simpa using congr($s.condition ≫ p.fst)
  · exact fun _ _ hm _ ↦ Fork.IsLimit.hom_ext he (Eq.symm (Fork.IsLimit.lift_ι he) ▸ hm)

/-- The equalizer of `f g : X ⟶ Y` is the pullback of the diagonal map `Y ⟶ Y ⨯ Y`
  along the map `⟨f, g⟩ : X ⟶ Y ⨯ Y`. Version with implicit products and equalizers. -/
lemma isPullback_equalizer_prod (f g : X ⟶ Y) [HasEqualizer f g] [HasBinaryProduct Y Y] :
      IsPullback (equalizer.ι f g) (equalizer.ι f g ≫ f) (prod.lift f g) (diag Y) :=
    isPullback_equalizer_prod_exp _ f g (equalizer.fork f g) (equalizerIsEqualizer' f g)

/-- If `e` is an coequalizer of `f g : X ⟶ Y`, then `e` is also the pushout of the codiagonal map
`X + X ⟶ X` along `⟨f, g⟩ : X + X ⟶ Y`. Fully explicit version with binary cofans and coforks. -/
lemma isPushout_coequalizer_coprod_exp {p : BinaryCofan X X} (hp : IsColimit p)
  (f g : X ⟶ Y) (e : Cofork f g) (h : IsColimit e) :
    IsPushout (hp.desc (BinaryCofan.mk f g)) (hp.desc (BinaryCofan.mk (𝟙 X) (𝟙 X)))
      e.π (f ≫ e.π) := by
  refine
    ⟨ ⟨ BinaryCofan.IsColimit.hom_ext hp (by simp) (by simp[e.condition]) ⟩,
      ⟨ PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_ ⟩ ⟩
  · exact fun s ↦ h.desc (Cofork.ofπ s.inl (eq_of_desc_eq_codiag p hp (s.condition)))
  · exact fun s ↦ Cofork.IsColimit.π_desc h
  · exact fun s ↦ by simpa using congr(p.inl ≫ $s.condition)
  · exact fun _ _ hm _ ↦ Cofork.IsColimit.hom_ext h (Eq.symm (Cofork.IsColimit.π_desc h) ▸ hm)

/-- The coequalizer of `f g : X ⟶ Y` is the pushout of the diagonal map `X ⨿ X ⟶ X`
along the map `(f, g) : X ⨿ X ⟶ Y`. Version with implicit coproducts and coequalizers -/
lemma isPushout_coequalizer_coprod (f g : X ⟶ Y) [HasCoequalizer f g] [HasBinaryCoproduct X X] :
    IsPushout (coprod.desc f g) (codiag X)
      (coequalizer.π f g) (f ≫ coequalizer.π f g) :=
  isPushout_coequalizer_coprod_exp _ f g (coequalizer.cofork f g) (coequalizerIsCoequalizer' f g)

end CategoryTheory.Limits
