/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Galois.ContAction
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Limits.Over

/-!
# ...

-/

-- #42397, #42396, #42320

public section

universe w v u

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

noncomputable def Over.isInitialEquiv {S : C} {X : Over S}
    [PreservesColimit (Functor.empty (Over S)) (Over.forget S)] :
    IsInitial X ≃ IsInitial X.left where
  toFun h := IsInitial.isInitialObj (G := Over.forget S)  _  h
  invFun h :=
    IsInitial.ofUniqueHom (fun Z ↦ Over.homMk (h.to _) (h.hom_ext _ _))
      (fun Z m ↦ by ext; apply h.hom_ext)
  left_inv _ := by subsingleton
  right_inv _ := by subsingleton

variable (C) in
abbrev PreGaloisCategory.isConnected : ObjectProperty C :=
  IsConnected

instance (X : (PreGaloisCategory.isConnected C).FullSubcategory) :
    PreGaloisCategory.IsConnected X.obj :=
  X.property

open PreGaloisCategory

namespace PreGaloisCategory

variable (F : C ⥤ FintypeCat.{w}) [GaloisCategory C] [FiberFunctor F]

end PreGaloisCategory

instance (G : Type*) [Group G] : HasFiniteColimits (Action FintypeCat.{w} G) where
  out _ _ _ := inferInstance

namespace GaloisCategory

instance [GaloisCategory C] : HasFiniteLimits C := by
  infer_instance

instance [GaloisCategory C] : HasFiniteColimits C where
  out _ _ _ :=
    Adjunction.hasColimitsOfShape_of_equivalence
      (functorToContAction (GaloisCategory.getFiberFunctor C))

instance [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] :
    PreservesFiniteColimits
      (ObjectProperty.ι _ : ContAction FintypeCat.{w} (Aut F) ⥤ _) where
  preservesFiniteColimits _ _ _ := inferInstance

instance [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] :
    PreservesFiniteColimits F := by
  change (PreservesFiniteColimits
    (functorToContAction F ⋙ ObjectProperty.ι _ ⋙ Action.forget _ _))
  apply +allowSynthFailures comp_preservesFiniteColimits
  apply +allowSynthFailures comp_preservesFiniteColimits

open PreGaloisCategory

lemma has_connected_component [GaloisCategory C] (X : C) (hX : IsInitial X → False) :
    ∃ (X₀ : C) (f : X₀ ⟶ X), Mono f ∧ PreGaloisCategory.IsConnected X₀ := by
  obtain ⟨ι, W, a, ha, _, _⟩ := has_decomp_connected_components X
  have : Nonempty ι := by
    by_contra!
    exact hX (IsInitial.ofUniqueHom
      (fun _ ↦ Cofan.IsColimit.desc ha (fun i ↦ (IsEmpty.false i).elim))
      (fun _ _ ↦ Cofan.IsColimit.hom_ext ha _ _ (fun i ↦ (IsEmpty.false i).elim)))
  exact ⟨W (Classical.arbitrary _), a _, MonoCoprod.mono_inj _ _ ha _, inferInstance⟩

instance [GaloisCategory C] {X Y : (isConnected C).FullSubcategory} (f : X ⟶ Y) :
    Epi f.hom := by
  let F := GaloisCategory.getFiberFunctor C
  exact epi_of_nonempty_of_isConnected F _

instance [GaloisCategory C] {X Y : (isConnected C).FullSubcategory} (f : X ⟶ Y) :
    Epi f where
  left_cancellation {Z} g₁ g₂ h := by
    ext
    simp only [← cancel_epi f.hom, ← InducedCategory.comp_hom, h]

instance : SplitEpiCategory FintypeCat.{w} where
  isSplitEpi_of_epi f hf := by
    replace hf : Function.Surjective f := by
      change Function.Surjective (FintypeCat.incl.map f)
      rw [← CategoryTheory.epi_iff_surjective]
      infer_instance
    exact ⟨⟨ SplitEpi.mk (FintypeCat.homMk (Function.surjInv hf)) (by
      ext x
      simp [Function.rightInverse_surjInv hf x])⟩⟩

instance : IsRegularEpiCategory FintypeCat.{w} := by
  infer_instance

lemma effectiveEpi_of_epi [GaloisCategory C] {X Y : C} (f : X ⟶ Y) [Epi f] :
    EffectiveEpi f := by
  let F := GaloisCategory.getFiberFunctor C
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

instance [GaloisCategory C] {X Y : (isConnected C).FullSubcategory} (f : X ⟶ Y) :
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

instance [GaloisCategory C] : Preregular (isConnected C).FullSubcategory where
  exists_fac {X Y Z} f g _ := by
    obtain ⟨X₀, a, _, _⟩ := has_connected_component (pullback f.hom g.hom) (by
      let F := GaloisCategory.getFiberFunctor C
      rw [not_initial_iff_fiber_nonempty F]
      let x : F.obj X.obj := Classical.arbitrary _
      have ⟨z, hz⟩ := surjective_on_fiber_of_epi F g.hom (F.map f.hom x)
      exact ⟨(fiberPullbackEquiv F f.hom g.hom).symm ⟨⟨x, z⟩, hz.symm⟩⟩)
    refine ⟨⟨X₀, inferInstance⟩, ObjectProperty.homMk (a ≫ pullback.fst _ _),
      inferInstance, ObjectProperty.homMk (a ≫ pullback.snd _ _), ?_⟩
    ext
    simp [pullback.condition]

example [GaloisCategory C] : GrothendieckTopology (isConnected C).FullSubcategory :=
  regularTopology (isConnected C).FullSubcategory

lemma isConnected_over_iff
    {S : C} (X : Over S)
    [PreservesColimit (Functor.empty.{0} (Over S)) (Over.forget S)] :
    PreGaloisCategory.IsConnected X ↔
      PreGaloisCategory.IsConnected X.left := by
  refine ⟨fun _ ↦ ⟨fun h ↦ IsConnected.notInitial (Over.isInitialEquiv.symm h), ?_⟩,
    fun _ ↦ ⟨fun h ↦ IsConnected.notInitial (Over.isInitialEquiv h), ?_⟩⟩
  · sorry
  · sorry

instance (S : C) [PreservesColimit (Functor.empty.{0} (Over S)) (Over.forget S)] :
    PreservesIsConnected (Over.forget S) where
  preserves {X} _ := by
    rw [Over.forget_obj, ← isConnected_over_iff]
    infer_instance

section

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (S : C)
  [PreGaloisCategory.IsConnected S] (s : F.obj S)

@[implicit_reducible]
def fiberFunctorOver : Over S ⥤ FintypeCat.{w} where
  obj X := .of ((F.map X.hom) ⁻¹' {s})
  map f := FintypeCat.homMk (fun x ↦⟨F.map f.left x, by
    simpa only [← ConcreteCategory.comp_apply, ← F.map_comp, f.w,
      Set.mem_preimage, Set.mem_singleton_iff] using x.prop⟩)

end

end GaloisCategory

end CategoryTheory
