/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Bousfield localization

Given a predicate `P : C → Prop` on the objects of a category `C`,
we define `Localization.LeftBousfield.W P : MorphismProperty C`
as the class of morphisms `f : X ⟶ Y` such that for any `Z : C`
such that `P Z`, the precomposition with `f` induces a bijection
`(Y ⟶ Z) ≃ (X ⟶ Z)`.

(This construction is part of left Bousfield localization
in the context of model categories.)

When `G ⊣ F` is an adjunction with `F : C ⥤ D` fully faithful, then
`G : D ⥤ C` is a localization functor for the class `W (· ∈ Set.range F.obj)`,
which then identifies to the inverse image by `G` of the class of
isomorphisms in `C`.

## References

* https://ncatlab.org/nlab/show/left+Bousfield+localization+of+model+categories

-/

namespace CategoryTheory

open Category

namespace Localization

variable {C D : Type*} [Category C] [Category D]

namespace LeftBousfield

section

variable (P : C → Prop)

/-- Given a predicate `P : C → Prop`, this is the class of morphisms `f : X ⟶ Y`
such that for all `Z : C` such that `P Z`, the precomposition with `f` induces
a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`. -/
def W : MorphismProperty C := fun _ _ f =>
  ∀ Z, P Z → Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)

lemma W_isoClosure : W (isoClosure P) = W P := by
  ext X Y f
  constructor
  · intro hf Z hZ
    exact hf _ (le_isoClosure _ _ hZ)
  · rintro hf Z ⟨Z', hZ', ⟨e⟩⟩
    constructor
    · intro g₁ g₂ eq
      rw [← cancel_mono e.hom]
      apply (hf _ hZ').1
      simp only [reassoc_of% eq]
    · intro g
      obtain ⟨a, h⟩ := (hf _ hZ').2 (g ≫ e.hom)
      exact ⟨a ≫ e.inv, by simp only [reassoc_of% h, e.hom_inv_id, comp_id]⟩

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

end

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) [F.Full] [F.Faithful]

lemma W_adj_unit_app (X : D) : W (· ∈ Set.range F.obj) (adj.unit.app X) := by
  rintro _ ⟨Y, rfl⟩
  convert ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.trans
    (adj.homEquiv X Y)).bijective using 1
  aesop

lemma W_iff_isIso_map {X Y : D} (f : X ⟶ Y) :
    W (· ∈ Set.range F.obj) f ↔ IsIso (G.map f) := by
  rw [← MorphismProperty.postcomp_iff _ _ _ (W_adj_unit_app adj Y)]
  erw [adj.unit.naturality f]
  rw [MorphismProperty.precomp_iff _ _ _ (W_adj_unit_app adj X),
    W_iff_isIso _ _ ⟨_, rfl⟩ ⟨_, rfl⟩]
  constructor
  · intro h
    dsimp at h
    exact isIso_of_fully_faithful F (G.map f)
  · intro
    rw [Functor.comp_map]
    infer_instance

lemma W_eq_inverseImage_isomorphisms :
    W (· ∈ Set.range F.obj) = (MorphismProperty.isomorphisms _).inverseImage G := by
  ext P₁ P₂ f
  rw [W_iff_isIso_map adj]
  rfl

lemma isLocalization : G.IsLocalization (W (· ∈ Set.range F.obj)) := by
  rw [W_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization

end

end LeftBousfield

end Localization

end CategoryTheory
