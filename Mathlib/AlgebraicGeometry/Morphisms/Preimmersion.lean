/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.RingHom.Surjective

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

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ Y` is a preimmersion if the underlying map of
topological spaces is an embedding and the induced morphisms of stalks are all surjective. -/
@[mk_iff]
class IsPreimmersion {X Y : Scheme} (f : X ⟶ Y) : Prop where
  base_embedding : IsEmbedding f.base
  surj_on_stalks : ∀ x, Function.Surjective (f.stalkMap x)

lemma Scheme.Hom.isEmbedding {X Y : Scheme} (f : Hom X Y) [IsPreimmersion f] : Embedding f.base :=
  IsPreimmersion.base_embedding

lemma Scheme.Hom.stalkMap_surjective {X Y : Scheme} (f : Hom X Y) [IsPreimmersion f] (x) :
    Function.Surjective (f.stalkMap x) :=
  IsPreimmersion.surj_on_stalks x

lemma isPreimmersion_eq_inf :
    @IsPreimmersion = topologically IsEmbedding ⊓ stalkwise (Function.Surjective ·) := by
  ext
  rw [isPreimmersion_iff]
  rfl

/-- Being surjective on stalks is local at the target. -/
instance isSurjectiveOnStalks_isLocalAtTarget : IsLocalAtTarget
    (stalkwise (Function.Surjective ·)) :=
  stalkwiseIsLocalAtTarget_of_respectsIso RingHom.surjective_respectsIso

namespace IsPreimmersion

instance : IsLocalAtTarget @IsPreimmersion :=
  isPreimmersion_eq_inf ▸ inferInstance

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : IsPreimmersion f where
  base_embedding := f.isOpenEmbedding.isEmbedding
  surj_on_stalks _ := (ConcreteCategory.bijective_of_isIso _).2

instance : MorphismProperty.IsMultiplicative @IsPreimmersion where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨hg.base_embedding.comp hf.base_embedding, fun x ↦ ?_⟩
    rw [Scheme.stalkMap_comp]
    exact (hf.surj_on_stalks x).comp (hg.surj_on_stalks (f.base x))

instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion f]
    [IsPreimmersion g] : IsPreimmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

instance (priority := 900) {X Y} (f : X ⟶ Y) [IsPreimmersion f] : Mono f := by
  refine (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).mono_of_mono_map ?_
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact f.isEmbedding.inj
  · exact fun x ↦ ConcreteCategory.epi_of_surjective _ (f.stalkMap_surjective x)

theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g]
    [IsPreimmersion (f ≫ g)] : IsPreimmersion f where
  base_embedding := by
    have h := (f ≫ g).isEmbedding
    rwa [← g.isEmbedding.of_comp_iff]
  surj_on_stalks x := by
    have h := (f ≫ g).stalkMap_surjective x
    rw [Scheme.stalkMap_comp] at h
    exact Function.Surjective.of_comp h

theorem comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g] :
    IsPreimmersion (f ≫ g) ↔ IsPreimmersion f :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

end IsPreimmersion

end AlgebraicGeometry
