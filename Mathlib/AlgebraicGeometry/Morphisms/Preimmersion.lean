/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.RingTheory.LocalProperties

/-!

# Preimmersions of schemes

A morphism of schemes `f : X ⟶ Y` is a preimmersion if the underlying map of topological spaces
is an embedding and the induced morphisms of stalks are all surjective. This is not a concept seen
in the literature but it is useful for generalizing results on immersions to other maps including
`Spec 𝒪_{X, x} ⟶ X` and inclusions of fibers `κ(x) ×ₓ Y ⟶ Y`.

## TODO

* Show preimmersions are local at the target.
* Show preimmersions are stable under pullback.
* Show that `Spec f` is a preimmersion for `f : R ⟶ S` if every `s : S` is of the form `f a / f b`.

-/

universe v u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ Y` is a preimmersion if the underlying map of
topological spaces is an embedding and the induced morphisms of stalks are all surjective. -/
class IsPreimmersion {X Y : Scheme} (f : X ⟶ Y) : Prop where
  base_embedding : Embedding f.1.base
  surj_on_stalks : ∀ x, Function.Surjective (PresheafedSpace.stalkMap f.1 x)

lemma Scheme.Hom.embedding {X Y : Scheme} (f : Hom X Y) [IsPreimmersion f] : Embedding f.1.base :=
  IsPreimmersion.base_embedding

lemma Scheme.Hom.stalkMap_surjective {X Y : Scheme} (f : Hom X Y) [IsPreimmersion f] (x) :
    Function.Surjective (PresheafedSpace.stalkMap f.1 x) :=
  IsPreimmersion.surj_on_stalks x

namespace IsPreimmersion

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : IsPreimmersion f where
  base_embedding := f.openEmbedding.toEmbedding
  surj_on_stalks _ := (ConcreteCategory.bijective_of_isIso _).2

instance : MorphismProperty.IsMultiplicative @IsPreimmersion where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨hg.base_embedding.comp hf.base_embedding, fun x ↦ ?_⟩
    erw [PresheafedSpace.stalkMap.comp]
    exact (hf.surj_on_stalks x).comp (hg.surj_on_stalks (f.1.1 x))

instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion f]
    [IsPreimmersion g] : IsPreimmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

instance respectsIso : MorphismProperty.RespectsIso @IsPreimmersion := by
  constructor <;> intro X Y Z e f hf <;> infer_instance

attribute [local instance] ConcreteCategory.instFunLike in
open _root_.TopCat.Presheaf in
lemma SheafedSpace.hom_stalk_ext {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C]
    [Limits.HasColimits C] [Limits.PreservesFilteredColimits (forget C)]
    [Limits.HasLimits C] [Limits.PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]
    {X Y : SheafedSpace C} (f g : X ⟶ Y) (h : f.base = g.base)
    (h' : ∀ x, PresheafedSpace.stalkMap f x =
      Y.presheaf.stalkSpecializes (specializes_of_eq $ by rw [h]) ≫ PresheafedSpace.stalkMap g x) :
    f = g := by
  obtain ⟨f, fc⟩ := f
  obtain ⟨g, gc⟩ := g
  obtain rfl : f = g := h
  congr
  ext U s
  apply section_ext X.sheaf
  intro x
  show X.presheaf.germ x _ = X.presheaf.germ x _
  erw [← PresheafedSpace.stalkMap_germ_apply ⟨f, fc⟩, ← PresheafedSpace.stalkMap_germ_apply ⟨f, gc⟩,
    h']
  simp

lemma SheafedSpace.mono_of_base_injective_of_stalk_epi {C : Type u} [Category.{v} C]
    [ConcreteCategory.{v} C] [Limits.HasColimits C]
    [Limits.PreservesFilteredColimits (forget C)]
    [Limits.HasLimits C] [Limits.PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]
    {X Y : SheafedSpace C}
    (f : X ⟶ Y)
    (h₁ : Function.Injective f.base)
    (h₂ : ∀ x, Epi (PresheafedSpace.stalkMap f x)) : Mono f := by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun x ↦ h₁ congr(($e).base x)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun x ↦ ?_
  rw [← cancel_epi (PresheafedSpace.stalkMap f (g x)), TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  rw [← PresheafedSpace.stalkMap.comp ⟨g, gc⟩ f, ← PresheafedSpace.stalkMap.comp ⟨g, hc⟩ f]
  congr 1

instance (priority := 900) {X Y} (f : X ⟶ Y) [IsPreimmersion f] : Mono f := by
  refine (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).mono_of_mono_map ?_
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact f.embedding.inj
  · exact fun x ↦ ConcreteCategory.epi_of_surjective _ (f.stalkMap_surjective x)

theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g]
    [IsPreimmersion (f ≫ g)] : IsPreimmersion f where
  base_embedding := by
    have h := (f ≫ g).embedding
    rwa [← g.embedding.of_comp_iff]
  surj_on_stalks x := by
    have h := (f ≫ g).stalkMap_surjective x
    erw [Scheme.comp_val, PresheafedSpace.stalkMap.comp] at h
    exact Function.Surjective.of_comp h

theorem comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g] :
    IsPreimmersion (f ≫ g) ↔ IsPreimmersion f :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

end IsPreimmersion

end AlgebraicGeometry
