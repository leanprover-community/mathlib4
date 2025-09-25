/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
import Mathlib.CategoryTheory.EffectiveEpi.RegularEpi
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!

# Effective epimorphisms in the category of types

We prove that effective epimorphisms in the category of types are precisely surjective functions.
-/

namespace CategoryTheory.Limits.Types

universe u

open Limits Function

section CoequalizerPullbackCone

variable {X Y : Type u} {f : X ⟶ Y}

variable (f) in
/-- The canonical function from the `Function.Coequalizer` of the two pullbackCone projections
of `f : X ⟶ Y` along itself to `Y`. -/
def fromCoequalizerPullbackCone :
    Function.Coequalizer (Types.pullbackCone f f).fst (Types.pullbackCone f f).snd ⟶ Y :=
  Function.Coequalizer.desc _ _ f (funext fun p => p.2)

variable (f) in
/-- `fromCoequalizerPullbackCone f` is always injective. -/
lemma injective_fromCoequalizerPullbackCone : Injective (fromCoequalizerPullbackCone f) := by
  intro z₁ z₂ h
  rw [← Quot.out_eq z₁, ← Quot.out_eq z₂]
  have h' : f (Quot.out z₁) = f (Quot.out z₂) := by
    rwa [← Coequalizer.desc_mk _ _ f _ _, ← Coequalizer.desc_mk _ _ f _ _,
      Coequalizer.mk, Coequalizer.mk, Quot.out_eq, Quot.out_eq]
  exact Quot.sound (Coequalizer.Rel.intro (Subtype.mk (Prod.mk _ _) h'))

/-- If `f : X ⟶ Y` is surjective, so is `fromCoequalizerPullbackCone f`. -/
lemma surjective_fromCoequalizerPullbackCone (hf : Surjective f) :
    Surjective (fromCoequalizerPullbackCone f) := by
  intro y
  obtain ⟨x, _⟩ := hf y
  exact ⟨Quot.mk _ x, by simpa⟩

/-- If `f : X ⟶ Y` is surjective, then `fromCoequalizerPullbackCone f` is bijective. -/
lemma bijective_fromCoequalizerPullbackCone (hf : Surjective f) :
    Bijective (fromCoequalizerPullbackCone f) :=
  ⟨injective_fromCoequalizerPullbackCone f, surjective_fromCoequalizerPullbackCone hf⟩

/-- For a surjective map `f : X ⟶ Y` of types, the (categorical) coequalizer of the two
pullbackCone projections of `f : X ⟶ Y` along itself is given by `Y`. -/
noncomputable def coequalizerPullbackConeOfSurjective (hf : Surjective f) :
    coequalizer (Types.pullbackCone f f).fst (Types.pullbackCone f f).snd ≅ Y :=
  Types.coequalizerIso _ _ ≪≫ (Equiv.ofBijective (Coequalizer.desc _ _ f (funext fun p => p.2))
    (bijective_fromCoequalizerPullbackCone hf)).toIso

/-- For a morphism `f : X ⟶ Y` in the category of types which is surjective as a function,
`f : X ⟶ Y` has a structure of a regular epimorphism as the coequalizer of the two pullbackCone
projections of `f : X ⟶ Y` along itself. -/
noncomputable def regularEpiPullbackObjOfSurjective (hf : Surjective f) : RegularEpi f where
  W := Types.PullbackObj f f
  left := (Types.pullbackCone f f).fst
  right := (Types.pullbackCone f f).snd
  w := funext fun p => p.2
  isColimit := by
    refine Cofork.isColimitOfIsos _
      (coequalizerIsCoequalizer (Types.pullbackCone f f).fst (Types.pullbackCone f f).snd) _
      (.refl _) (.refl _) (coequalizerPullbackConeOfSurjective hf) ?_ ?_ ?_
    · simp
    · simp
    · rw [coequalizerPullbackConeOfSurjective]
      cat_disch

/-- For a morphism `f : X ⟶ Y` in the category of types which is surjective as a function, then
`f : X ⟶ Y` has a structure of a regular epimorphism as the coequalizer of the two pullbackCone
projections of `f : X ⟶ Y` along itself. -/
noncomputable def regularEpiPullbackOfSurjective {X Y : Type u} {f : X ⟶ Y} (hf : Surjective f) :
    RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := Cofork.isColimitOfIsos _ (regularEpiPullbackObjOfSurjective hf).isColimit _
    (Types.pullbackIsoPullback f f).symm (.refl X) (.refl Y)
      (by cat_disch) (by cat_disch) (by cat_disch)

end CoequalizerPullbackCone

section RegularEpi

/-- A morphism in the category of types has a sturcture of a regular epimorphism if and only if
it is a surjective function. -/
lemma regularEpi_iff_surjective {X Y : Type u} {f : X ⟶ Y} :
    Nonempty (RegularEpi f) ↔ Surjective f where
  mp := fun ⟨_⟩ => surjective_of_epi _
  mpr hf := ⟨regularEpiPullbackOfSurjective hf⟩

/-- A morphism in the category of types is an effective epimorphism if and only if
it is a surjective function. -/
lemma effectiveEpi_iff_surjective {X Y : Type u} {f : X ⟶ Y} : EffectiveEpi f ↔ Surjective f where
  mp h := regularEpi_iff_surjective.mp ⟨by infer_instance⟩
  mpr h := by
    let := (regularEpi_iff_surjective.mpr h).some
    infer_instance

end RegularEpi

end CategoryTheory.Limits.Types
