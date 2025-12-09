/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!

# The category of type-valued sheaves is a regular epi category

This file proves two main results:
* When the target category `D` is a regular epi category (i.e. every epimorphism is regular) and
  has pushouts and kernel pairs of epimorphisms, the functor category `C ⥤ D` is a regular epi
  category. This is an instance that applies directly when `D` is `Type*`.
* `isRegularEpiCategory_sheaf`: Let `J` be a Grothendieck topology on `C`, and suppose that
  `D` is a regular epi category which has pushouts and pullbacks, and that sheafification of
  `D`-valued `J`-sheaves exists. Suppose further that the category `Sheaf J D` is balanced, and
  that the underlying morphism of presheaves of every epimorphism in `Sheaf J D` can be factored
  as an epimorphism followed by a monomorphism. Then `Sheaf J D` is a regular epi category.

  Note: This is not an instance because of the factorisation requirement, but it can in principle be
  turned into an instance whenever `D` has equalizers and `Cᵒᵖ ⥤ D` has images. This holds in
  particular when `D` is `Type*` or any abelian category. We add it as an instance for `D := Type*`,
  but the fact that `Sheaf J D` is a regular epi category when `D` is an abelian category
  already follows from the sheaf category being abelian.

## References

We follow the proof of Proposition 3.4.13 in [borceux-vol3]
*Handbook of Categorical Algebra: Volume 3, Sheaf Theory*, by Borceux, 1994.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Category Functor Limits

variable {C D : Type*} [Category C] [Category D]

instance [∀ {F G : D} (f : F ⟶ G) [Epi f], HasPullback f f] [HasPushouts D]
    [IsRegularEpiCategory D] :
    IsRegularEpiCategory (C ⥤ D) where
  regularEpiOfEpi {F G} f := ⟨⟨{
    W := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.pt
    left := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.fst
    right := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.snd
    w := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.condition
    isColimit := evaluationJointlyReflectsColimits _ fun k ↦ by
      have := IsRegularEpiCategory.regularEpiOfEpi (f.app k)
      refine .equivOfNatIsoOfIso ?_ _ _ ?_ (isColimitCoforkOfEffectiveEpi (f.app k)
        (pullback.cone (f.app k) (f.app k))
        (pullback.isLimit (f.app k) (f.app k)))
      · refine NatIso.ofComponents (by rintro (_ | _); exacts [Iso.refl _, Iso.refl _]) ?_
        rintro _ _ (_ | _)
        all_goals cat_disch
      · exact Cocones.ext (Iso.refl _) <| by rintro (_ | _ | _); all_goals cat_disch }⟩⟩

-- TODO: cite Borceux Handbook of Algebra for the proof
lemma isRegularEpiCategory_sheaf (J : GrothendieckTopology C)
    [HasPullbacks D] [HasPushouts D] [IsRegularEpiCategory D]
    (h : ∀ {F G : Sheaf J D} (f : F ⟶ G) [Epi f], ∃ (I : Cᵒᵖ ⥤ D) (p : F.val ⟶ I) (i : I ⟶ G.val),
      Epi p ∧ Mono i ∧ p ≫ i = f.val)
    [HasSheafify J D] [Balanced (Sheaf J D)] : IsRegularEpiCategory (Sheaf J D) where
  regularEpiOfEpi {F G} f _ := by
    -- Factor `f` on the level of presheaves as an epimorphism `p` followed by a monomorphism `i`.
    obtain ⟨I, p, i, hp, hi, hpi⟩ := h f
    -- The sheafification of `f.val` is `f` pre- and postcomposed with isomorphisms.
    have h₁ : (presheafToSheaf J D).map f.val =
          (sheafificationAdjunction J D).counit.app F ≫ f ≫
          inv ((sheafificationAdjunction J D).counit.app G) := by
        simpa [← Category.assoc] using (sheafificationAdjunction J D).counit_naturality f
    have h₂ : f = inv ((sheafificationAdjunction J D).counit.app F) ≫
        (presheafToSheaf J D).map f.val ≫ (sheafificationAdjunction J D).counit.app G := by
      simp [h₁]
    -- The sheafification of `f.val` is still an epimorphism
    have : Epi ((presheafToSheaf J D).map f.val) := by
      rw [h₁]
      infer_instance
    -- The sheafification of `i` is an epimorphism, because the sheafification of `p ≫ i = f.val`
    -- is an epimorphism.
    have : Epi ((presheafToSheaf J D).map i) := by
      rw [← hpi, Functor.map_comp] at this
      exact epi_of_epi ((presheafToSheaf J D).map p) _
    -- Since the sheafification of `i` is both a monomorphism and an epimorphism, it is an
    -- isomorphism.
    have : IsIso ((presheafToSheaf J D).map i) :=
      Balanced.isIso_of_mono_of_epi _
    -- The next five lines show that it suffices to show that the sheafification of `p` is a
    -- regular epimorphism.
    rw [h₂, isRegularEpi_iff_effectiveEpi]
    suffices EffectiveEpi ((presheafToSheaf J D).map f.val) by infer_instance
    rw [← hpi, Functor.map_comp]
    suffices EffectiveEpi ((presheafToSheaf J D).map p) by infer_instance
    rw [← isRegularEpi_iff_effectiveEpi]
    -- The underlying presheaf of the kernel pair of `f` is a kernel pair for `p`, and since
    -- sheafification preserves colimits, `p` exhibits its target `I` as a coequalizer of this
    -- kernel pair. The result follows.
    let c : PullbackCone p p := PullbackCone.mk
        (W := (pullback f f).val) (pullback.fst f f).val (pullback.snd f f).val <| by
      simp [← cancel_mono i, hpi, ← Sheaf.comp_val, pullback.condition]
    have : IsRegularEpi p := IsRegularEpiCategory.regularEpiOfEpi _
    let hc := isColimitOfPreserves (presheafToSheaf J D) <|
      isColimitCoforkOfEffectiveEpi p c (PullbackCone.isLimitOfFactors f.val f.val i _ _ hpi hpi _
        ((isLimitOfPreserves _ <| pullback.isLimit f f).equivOfNatIsoOfIso _ _ _ <|
          PullbackCone.isoMk ((sheafToPresheaf J D).mapCone (pullback.cone f f))))
    exact ⟨⟨{
      W := (presheafToSheaf J D).obj (pullback f f).val
      left := (presheafToSheaf J D).map (pullback.fst f f).val
      right := (presheafToSheaf J D).map (pullback.snd f f).val
      w := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        rw [← cancel_mono i]
        simp [hpi, ← Sheaf.comp_val, pullback.condition]
      isColimit := by
        refine .equivOfNatIsoOfIso ?_ _ _ ?_ hc
        · refine NatIso.ofComponents ?_ ?_
          · rintro (_ | _); exacts [Iso.refl _, Iso.refl _]
          · rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals simp [c]
        · refine Cocones.ext (Iso.refl _) ?_
          rintro (_ | _)
          all_goals simp [c] }⟩⟩

instance (J : GrothendieckTopology C) [HasSheafify J (Type u)] :
    IsRegularEpiCategory (Sheaf J (Type u)) := isRegularEpiCategory_sheaf J fun f hf ↦
  ⟨image f.val, factorThruImage f.val, image.ι f.val, inferInstance, inferInstance, by simp⟩

example {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    IsRegularEpiCategory (Sheaf J (Type (max u v))) :=
  inferInstance

end CategoryTheory
