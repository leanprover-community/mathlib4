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

lemma factor_through_diag [HasBinaryProduct Z Z] {e : X ⟶ Y} {f g : Y ⟶ Z} {h : X ⟶ Z}
    (eq : e ≫ prod.lift f g = h ≫ diag Z) : e ≫ f = e ≫ g :=
  by calc
    e ≫ f = h     := by simpa using congr($eq ≫ prod.fst)
    _     = e ≫ g := by simpa using congr($eq.symm ≫ prod.snd)

/-- If `E` is an equalizer of `f g : X ⟶ Y`, then `E` is also the pullback of the diagonal map
`Y ⟶ Y × Y` along `⟨f, g⟩ : X ⟶ Y × Y`. -/
lemma isPullback_equalizer_prod' [HasBinaryProduct Y Y] (e : Fork f g) (h : IsLimit e) :
    IsPullback e.ι (e.ι ≫ f) (prod.lift f g) (diag _) := by
  refine ⟨⟨by ext <;> simp [e.condition]⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · exact fun s ↦ h.lift (Fork.ofι s.fst (factor_through_diag (s.condition)))
  · exact fun s ↦ Fork.IsLimit.lift_ι h
  · exact fun s ↦ by simpa using congr($s.condition ≫ prod.fst)
  · exact fun _ _ hm _ ↦ Fork.IsLimit.hom_ext h (Eq.symm (Fork.IsLimit.lift_ι h) ▸ hm)

/-- The equalizer of `f g : X ⟶ Y` is the pullback of the diagonal map `Y ⟶ Y × Y`
along the map `⟨f, g⟩ : X ⟶ Y × Y`. -/
lemma isPullback_equalizer_prod [HasEqualizer f g] [HasBinaryProduct Y Y] :
    IsPullback (equalizer.ι f g) (equalizer.ι f g ≫ f) (prod.lift f g) (diag _) :=
  isPullback_equalizer_prod' f g (equalizer.fork f g) (equalizerIsEqualizer' f g)

end CategoryTheory.Limits
