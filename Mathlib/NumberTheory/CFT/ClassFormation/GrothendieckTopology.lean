/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.FintypeCat
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryConnected
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryLimits
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCover
public import Mathlib.CategoryTheory.Sites.Coherent.RegularTopology
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# The Grothendieck topology on connected objects of a Galois category

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

open PreGaloisCategory

namespace GaloisCategory

variable [GaloisCategory C]

lemma effectiveEpi_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    EffectiveEpi f := by
  let F := getFiberFunctor C
  rw [← isRegularEpi_iff_effectiveEpi]
  exact ⟨⟨{
    W := pullback f f
    left := pullback.fst _ _
    right := pullback.snd _ _
    w := pullback.condition
    isColimit := isColimitOfReflects F (by
      have : EffectiveEpi (F.map f) := by
        rw [← isRegularEpi_iff_effectiveEpi]
        exact IsRegularEpiCategory.regularEpiOfEpi _
      exact (isColimitMapCoconeCoforkEquiv _ _).2
        (isColimitCoforkOfEffectiveEpi _
        ((PullbackCone.mk _ _ pullback.condition).map F)
        (isLimitPullbackConeMapOfIsLimit F pullback.condition (pullbackIsPullback _ _))))
  }⟩⟩

instance {X Y : (isConnected C).FullSubcategory} (f : X ⟶ Y) :
    EffectiveEpi f := by
  have := effectiveEpi_of_epi f.hom
  let h := EffectiveEpi.getStruct f.hom
  have {W : (isConnected C).FullSubcategory} (e : X ⟶ W)
      (he : ∀ {Z : (isConnected C).FullSubcategory} (g₁ g₂ : Z ⟶ X),
        g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) {Z : C}
      (g₁ g₂ : Z ⟶ X.obj) (hf : g₁ ≫ f.hom = g₂ ≫ f.hom) :
      g₁ ≫ e.hom = g₂ ≫ e.hom := by
    obtain ⟨ι, T, a, ha, _, _⟩ := has_decomp_connected_components Z
    refine Cofan.IsColimit.hom_ext ha _ _ (fun i ↦ ?_)
    simpa [ObjectProperty.hom_ext_iff] using
      he (Z := ⟨T i, inferInstance⟩) (ObjectProperty.homMk (a i ≫ g₁))
        (ObjectProperty.homMk (a i ≫ g₂)) (by cat_disch)
  exact ⟨⟨{
    desc e he := ObjectProperty.homMk (h.desc e.hom (this e he))
    fac e he := by ext; exact h.fac e.hom (this e he)
    uniq e he m hm := by
      ext
      exact h.uniq e.hom _ _ (by simp [← hm])
  }⟩⟩

instance : Preregular (isConnected C).FullSubcategory where
  exists_fac {X Y Z} f g _ := by
    obtain ⟨X₀, a, _, _⟩ := has_connected_component (pullback f.hom g.hom) (by
      let F := getFiberFunctor C
      rw [not_initial_iff_fiber_nonempty F]
      let x : F.obj X.obj := Classical.arbitrary _
      have ⟨z, hz⟩ := surjective_on_fiber_of_epi F g.hom (F.map f.hom x)
      exact ⟨(fiberPullbackEquiv F f.hom g.hom).symm ⟨⟨x, z⟩, hz.symm⟩⟩)
    refine ⟨⟨X₀, inferInstance⟩, ObjectProperty.homMk (a ≫ pullback.fst _ _),
      inferInstance, ObjectProperty.homMk (a ≫ pullback.snd _ _), ?_⟩
    ext
    simp [pullback.condition]

variable (C) in
/-- The regular topology on the category of connected objects in a
Galois category. -/
abbrev isConnectedTopology :
    GrothendieckTopology (isConnected C).FullSubcategory :=
  regularTopology (isConnected C).FullSubcategory

lemma generate_singleton_mem_isConnectedTopology
    {X Y : (isConnected C).FullSubcategory} (f : X ⟶ Y) :
    (Sieve.generate (.singleton f)) ∈ isConnectedTopology C Y := by
  dsimp [isConnectedTopology]
  rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
  exact ⟨_ ,f, inferInstance, Sieve.le_generate _ _ _ (by simp)⟩

lemma exists_isGaloisCover_of_mem_isConnectedTopology
    {X : C} [PreGaloisCategory.IsConnected X] (R : Sieve (isConnectedMk X))
    (hR : R ∈ isConnectedTopology C _) :
    ∃ (Y : C) (_ : PreGaloisCategory.IsConnected Y) (f : Y ⟶ X),
      IsGaloisCover f ∧ R (isConnectedHomMk f) := by
  rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at hR
  obtain ⟨Z, g, _, hg⟩ := hR
  obtain ⟨Y, f, _, _⟩ := exists_isGaloisCover g.hom
  exact ⟨Y, inferInstance, f ≫ g.hom, inferInstance,
    R.downward_closed (g := isConnectedHomMk f) hg⟩

/-
/-- A fiber functor on a Galois category `C` induces a fiber functor on the
site of connected objects in `C`. -/
def isConnectedTopologyFiberFunctor
    (F : C ⥤ FintypeCat.{w}) [EssentiallySmall.{w} C] [FiberFunctor F] :
    GrothendieckTopology.Point.{w} (isConnectedTopology C) where
  fiber := ObjectProperty.ι _ ⋙ F ⋙ ObjectProperty.ι _
  jointly_surjective {X} R hR x := by
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at hR
    obtain ⟨Y, f, _, hR⟩ := hR
    obtain ⟨y, rfl⟩ := surjective_of_epi ((forget _).map (F.map f.hom)) x
    exact ⟨Y, f, hR, y, rfl⟩
  initiallySmall := sorry
  isCofiltered := sorry
-/

end GaloisCategory

end CategoryTheory
