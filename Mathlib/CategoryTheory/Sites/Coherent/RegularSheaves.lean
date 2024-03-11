/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Coherent.Basic
/-!

# Sheaves for the regular topology

This file characterises sheaves for the regular topology.

## Main results

* `isSheaf_iff_equalizerCondition`: In a preregular category with pullbacks, the sheaves for the
  regular topology are precisely the presheaves satisfying an equaliser condition with respect to
  effective epimorphisms.

* `isSheaf_of_projective`: In a preregular category in which every object is projective, every
  presheaf is a sheaf for the regular topology.
-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

open Opposite Presieve

/-- A presieve is *regular* if it consists of a single effective epimorphism. -/
class Presieve.regular {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a single epimorphism. -/
  single_epi : ∃ (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) ↦ Y)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f

namespace regularCoverage

/--
The map to the explicit equalizer used in the sheaf condition.
-/
def MapToEqualizer (P : Cᵒᵖ ⥤ Type*) {W X B : C} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } := fun t ↦
  ⟨P.map f.op t, by simp only [Set.mem_setOf_eq, ← FunctorToTypes.map_comp_apply, ← op_comp, w]⟩

/--
The sheaf condition with respect to regular presieves, given the existence of the relavant pullback.
-/
def EqualizerCondition (P : Cᵒᵖ ⥤ Type*) : Prop :=
  ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], Function.Bijective
    (MapToEqualizer P π (pullback.fst (f := π) (g := π)) (pullback.snd (f := π) (g := π))
    pullback.condition)

lemma EqualizerCondition.isSheafFor {B : C} {S : Presieve B} [S.regular] [S.hasPullbacks]
    {F : Cᵒᵖ ⥤ Type*}
    (hF : EqualizerCondition F) : S.IsSheafFor F := by
  obtain ⟨X, π, hS, πsurj⟩ := Presieve.regular.single_epi (R := S)
  subst hS
  rw [isSheafFor_arrows_iff_pullbacks]
  intro y h
  have : (Presieve.singleton π).hasPullbacks := by rw [← ofArrows_pUnit]; infer_instance
  have : HasPullback π π := hasPullbacks.has_pullbacks Presieve.singleton.mk Presieve.singleton.mk
  specialize hF X B π
  rw [Function.bijective_iff_existsUnique] at hF
  obtain ⟨t, ht, ht'⟩ := hF ⟨y (), h () ()⟩
  refine ⟨t, fun _ ↦ ?_, fun x h ↦ ht' x ?_⟩
  · simpa [MapToEqualizer] using ht
  · simpa [MapToEqualizer] using h ()

lemma equalizerCondition_of_regular {F : Cᵒᵖ ⥤ Type*}
    (hSF : ∀ {B : C} (S : Presieve B) [S.regular] [S.hasPullbacks], S.IsSheafFor F) :
    EqualizerCondition F := by
  intro X B π _ _
  have : (ofArrows (fun _ ↦ X) (fun _ ↦ π)).regular := ⟨X, π, rfl, inferInstance⟩
  have : (ofArrows (fun () ↦ X) (fun _ ↦ π)).hasPullbacks := ⟨
      fun hf _ hg ↦ (by cases hf; cases hg; infer_instance)⟩
  specialize hSF (ofArrows (fun () ↦ X) (fun _ ↦ π))
  rw [isSheafFor_arrows_iff_pullbacks] at hSF
  rw [Function.bijective_iff_existsUnique]
  intro ⟨x, hx⟩
  obtain ⟨t, ht, ht'⟩ := hSF (fun _ ↦ x) (fun _ _ ↦ hx)
  refine ⟨t, ?_, fun y h ↦ ht' y ?_⟩
  · simpa [MapToEqualizer] using ht ()
  · simpa [MapToEqualizer] using h

lemma isSheafFor_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Projective X]
    (F : Cᵒᵖ ⥤ Type*) : S.IsSheafFor F := by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  rw [isSheafFor_arrows_iff]
  refine fun x hx ↦ ⟨F.map (Projective.factorThru (𝟙 _) f).op <| x (), fun _ ↦ ?_, fun y h ↦ ?_⟩
  · simpa using (hx () () Y (𝟙 Y) (f ≫ (Projective.factorThru (𝟙 _) f)) (by simp)).symm
  · simp only [← h (), ← FunctorToTypes.map_comp_apply, ← op_comp, Projective.factorThru_comp,
      op_id, FunctorToTypes.map_id_apply]

lemma EqualizerCondition.isSheaf_iff (F : Cᵒᵖ ⥤ Type*)
    [∀ ⦃X Y : C⦄ (π : X ⟶ Y) [EffectiveEpi π], HasPullback π π] [Preregular C] :
    Presieve.IsSheaf (regularCoverage C).toGrothendieck F ↔ EqualizerCondition F := by
  rw [Presieve.isSheaf_coverage]
  refine ⟨fun h ↦ equalizerCondition_of_regular fun S ⟨Y, f, hh⟩ _ ↦ h S ⟨Y, f, hh⟩, ?_⟩
  rintro h X S ⟨Y, f, rfl, hf⟩
  exact @isSheafFor _ _ _ _ ⟨Y, f, rfl, hf⟩ ⟨fun g _ h ↦ by cases g; cases h; infer_instance⟩ _ h

lemma isSheaf_of_projective (F : Cᵒᵖ ⥤ Type*) [Preregular C] [∀ (X : C), Projective X] :
    IsSheaf (regularCoverage C).toGrothendieck F :=
  (isSheaf_coverage _ _).mpr fun S ⟨_, h⟩ ↦ have : S.regular := ⟨_, h⟩
    isSheafFor_regular_of_projective _ _

/-- Every Yoneda-presheaf is a sheaf for the regular topology. -/
theorem isSheaf_yoneda_obj [Preregular C] (W : C)  :
    Presieve.IsSheaf (regularCoverage C).toGrothendieck (yoneda.obj W) := by
  rw [isSheaf_coverage]
  intro X S ⟨_, hS⟩
  have : S.regular := ⟨_, hS⟩
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  have h_colim := isColimitOfEffectiveEpiStruct f hf.effectiveEpi.some
  rw [← Sieve.generateSingleton_eq, ← Presieve.ofArrows_pUnit] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows (fun () ↦ Y) (fun () ↦ f))
  obtain ⟨t, t_amalg, t_uniq⟩ :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert Presieve.isAmalgamation_restrict (Sieve.le_generate
      (Presieve.ofArrows (fun () ↦ Y) (fun () ↦ f))) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
  · exact fun y hy ↦ t_uniq y <| Presieve.isAmalgamation_sieveExtend x y hy

/-- The regular topology on any preregular category is subcanonical. -/
theorem subcanonical [Preregular C] : Sheaf.Subcanonical (regularCoverage C).toGrothendieck :=
  Sheaf.Subcanonical.of_yoneda_isSheaf _ isSheaf_yoneda_obj

end regularCoverage

end CategoryTheory
