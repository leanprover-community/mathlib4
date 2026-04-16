/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Families of functors which jointly reflect isomorphisms

Let `Fᵢ : C ⥤ Dᵢ` be a family of functors. The family is said to jointly reflect
isomorphisms (resp. monomorphisms, resp. epimorphisms) if every `f : X ⟶ Y`
in `C` for which `Fᵢ.map f` is an isomorphism (resp. monomorphism, resp. epimorphism)
for all `i` is an isomorphism.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {I : Type*} {D : I → Type*} [∀ i, Category (D i)]

/-- A family of functors jointly reflects isomorphisms if for every morphism `f : X ⟶ Y`
such that the image of `f` under all `F i` is an isomorphism, then `f` is an isomorphism. -/
structure JointlyReflectIsomorphisms (F : ∀ i, C ⥤ D i) : Prop where
  isIso {X Y : C} (f : X ⟶ Y) [∀ i, IsIso ((F i).map f)] : IsIso f

/-- A family of functors jointly reflects monomorphisms if for every morphism `f : X ⟶ Y`
such that the image of `f` under all `F i` is an monomorphism, then `f` is an monomorphism. -/
structure JointlyReflectMonomorphisms (F : ∀ i, C ⥤ D i) : Prop where
  mono {X Y : C} (f : X ⟶ Y) [∀ i, Mono ((F i).map f)] : Mono f

/-- A family of functors jointly reflects epimorphisms if for every morphism `f : X ⟶ Y`
such that the image of `f` under all `F i` is an epimorphism, then `f` is an epimorphism. -/
structure JointlyReflectEpimorphisms (F : ∀ i, C ⥤ D i) : Prop where
  epi {X Y : C} (f : X ⟶ Y) [∀ i, Epi ((F i).map f)] : Epi f

/-- A family of functors is jointly faithful if whenever two morphisms `f : X ⟶ Y`
and `g : X ⟶ Y` become equal after applying all functors `F i`, then `f = g`. -/
structure JointlyFaithful (F : ∀ i, C ⥤ D i) : Prop where
  map_injective {X Y : C} {f g : X ⟶ Y} (h : ∀ i, (F i).map f = (F i).map g) : f = g

variable {F : ∀ i, C ⥤ D i}

lemma JointlyFaithful.of_jointly_reflects_isIso_of_mono [HasEqualizers C]
    [∀ i, PreservesLimitsOfShape WalkingParallelPair (F i)]
    (hF : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [Mono f],
      (∀ i, IsIso ((F i).map f)) → IsIso f) :
    JointlyFaithful F where
  map_injective {X Y} f g hfg :=
    have :=
      hF (equalizer.ι f g) (fun i ↦ by
        let hc := isLimitForkMapOfIsLimit (F i) _ (equalizerIsEqualizer f g)
        obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hc (𝟙 _) (by simpa using hfg i)
        exact ⟨l, Fork.IsLimit.hom_ext hc (by cat_disch), by cat_disch⟩)
    eq_of_epi_equalizer

namespace JointlyReflectIsomorphisms

variable (h : JointlyReflectIsomorphisms F)

include h

lemma isIso_iff {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i, IsIso ((F i).map f) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦ h.isIso f⟩

lemma mono {X Y : C} (f : X ⟶ Y) [hf : ∀ i, Mono ((F i).map f)]
    [∀ i, PreservesLimit (cospan f f) (F i)] [HasPullback f f] :
    Mono f := by
  have hc := pullbackIsPullback f f
  rw [mono_iff_isIso_fst hc, h.isIso_iff]
  intro i
  exact (mono_iff_isIso_fst ((isLimitMapConePullbackConeEquiv (F i) pullback.condition).1
    (isLimitOfPreserves (F i) hc))).1 (hf i)

lemma jointlyReflectMonomorphisms [∀ i, PreservesLimitsOfShape WalkingCospan (F i)]
    [HasPullbacks C] :
    JointlyReflectMonomorphisms F where
  mono f _ := h.mono f

lemma epi {X Y : C} (f : X ⟶ Y) [hf : ∀ i, Epi ((F i).map f)]
    [∀ i, PreservesColimit (span f f) (F i)] [HasPushout f f] : Epi f := by
  have hc := pushoutIsPushout f f
  rw [epi_iff_isIso_inl hc, h.isIso_iff]
  intro i
  exact (epi_iff_isIso_inl ((isColimitMapCoconePushoutCoconeEquiv (F i) pushout.condition).1
    (isColimitOfPreserves (F i) hc))).1 (hf i)

lemma jointlyReflectEpimorphisms [∀ i, PreservesColimitsOfShape WalkingSpan (F i)]
    [HasPushouts C] :
    JointlyReflectEpimorphisms F where
  epi f _ := h.epi f

lemma jointlyFaithful [∀ i, PreservesLimitsOfShape WalkingParallelPair (F i)] [HasEqualizers C] :
    JointlyFaithful F :=
  .of_jointly_reflects_isIso_of_mono (fun _ _ _ _ _ ↦ h.isIso _)

end JointlyReflectIsomorphisms

lemma JointlyReflectMonomorphisms.mono_iff (h : JointlyReflectMonomorphisms F)
    [∀ i, (F i).PreservesMonomorphisms] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ i, Mono ((F i).map f) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦ h.mono f⟩

lemma JointlyReflectEpimorphisms.epi_iff (h : JointlyReflectEpimorphisms F)
    [∀ i, (F i).PreservesEpimorphisms] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ ∀ i, Epi ((F i).map f) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦ h.epi f⟩

namespace JointlyFaithful

lemma jointlyReflectMonomorphisms (h : JointlyFaithful F) :
    JointlyReflectMonomorphisms F where
  mono {X Y} f _ := ⟨fun {Z} g₁ g₂ hg ↦ h.map_injective (fun i ↦ by
    simp only [← cancel_mono ((F i).map f), ← Functor.map_comp, hg])⟩

lemma jointlyReflectEpimorphisms (h : JointlyFaithful F) :
    JointlyReflectEpimorphisms F where
  epi {X Y} f _ := ⟨fun {Z} g₁ g₂ hg ↦ h.map_injective (fun i ↦ by
    simp only [← cancel_epi ((F i).map f), ← Functor.map_comp, hg])⟩

lemma jointlyReflectsIsomorphisms [Balanced C] (h : JointlyFaithful F) :
    JointlyReflectIsomorphisms F where
  isIso f _ :=
    have := h.jointlyReflectMonomorphisms.mono f
    have := h.jointlyReflectEpimorphisms.epi f
    Balanced.isIso_of_mono_of_epi f

end JointlyFaithful

end CategoryTheory
