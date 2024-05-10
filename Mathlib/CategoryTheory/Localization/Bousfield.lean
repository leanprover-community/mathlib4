/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Bousfield localization

Given a predicate `P : C → Prop` on the objects of a category `C`,
we define `Localization.LeftBousfield.W P : MorphismProperty C`
as the class of morphisms `f : X ⟶ Y` such that for any `Z : C`
such that `P Z`, the precomposition with `f` induces a bijection
`(Y ⟶ Z) ≃ (X ⟶ Z)`.

(This construction is part of left Bousfield localization
in the context of model categories.)

## References

* https://ncatlab.org/nlab/show/left+Bousfield+localization+of+model+categories

-/

namespace CategoryTheory

open Category

namespace Localization

variable {C D : Type*} [Category C] [Category D]

namespace LeftBousfield

variable (P : C → Prop)

/-- Given a functor `P : C → Prop`, this is the class of morphisms `f : X ⟶ Y`
such that for all `Z : C` such that `P Z`, the precomposition with `f` induces
a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`. -/
def W : MorphismProperty C := fun _ _ f =>
  ∀ Z, P Z → Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)

instance : (W P).IsMultiplicative where
  id_mem X Z _ := by
    simp [id_comp]
    exact Function.bijective_id
  comp_mem f g hf hg Z hZ := by
    simpa using Function.Bijective.comp (hf Z hZ) (hg Z hZ)

instance : (W P).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff _ (hg Z hZ)]
    simpa using hfg Z hZ
  of_precomp f g hf hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff' (hf Z hZ)]
    simpa using hfg Z hZ

lemma W_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : W P f := fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_epi f]
  · intro g
    exact ⟨inv f ≫ g, by simp⟩

lemma W_iff_isIso {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) :
    W P f ↔ IsIso f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hX).2 (𝟙 X)
    exact ⟨g, hg, (hf _ hY).1 (by simp only [reassoc_of% hg, comp_id])⟩
  · apply W_of_isIso

end LeftBousfield

end Localization

end CategoryTheory
