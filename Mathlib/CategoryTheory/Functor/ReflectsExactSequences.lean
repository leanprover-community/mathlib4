/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Functors which reflect exact sequences

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

namespace Functor

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

class ReflectsExactSequences (F : C ⥤ D) : Prop where
  reflects' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w₂ : F.map f ≫ F.map g = 0)
    (ex₂ : (ShortComplex.mk _ _ w₂).Exact) :
    ∃ (zero : f ≫ g = 0), (ShortComplex.mk _ _ zero).Exact

lemma ReflectsExactSequences.reflects (F : C ⥤ D)
    [F.ReflectsExactSequences]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w₂ : F.map f ≫ F.map g = 0)
    (ex₂ : (ShortComplex.mk _ _ w₂).Exact) :
    ∃ (zero : f ≫ g = 0), (ShortComplex.mk _ _ zero).Exact :=
  @ReflectsExactSequences.reflects' _ _ _ _ _ _ F _ _ _ _ f g w₂ ex₂

lemma ReflectsExactSequences.reflectsShortComplexExact (F : C ⥤ D)
    [F.ReflectsExactSequences] [F.PreservesZeroMorphisms] (S : ShortComplex C)
    (hS : (S.map F).Exact) : S.Exact :=
  (reflects F S.f S.g (by simp only [← F.map_comp, S.zero, F.map_zero]) hS).choose_spec

end

section

variable [HasZeroMorphisms C] [Preadditive D]

lemma eq_zero_of_map_eq_zero (F : C ⥤ D) [F.ReflectsExactSequences]
    [HasZeroObject D] {X Y : C} (f : X ⟶ Y) (hf : F.map f = 0) : f = 0 := by
  simpa only [comp_id] using (ReflectsExactSequences.reflects F f (𝟙 Y)
      (by rw [F.map_id, comp_id, hf]) (by
    simp only [F.map_id, hf, ShortComplex.exact_iff_mono]
    infer_instance)).choose

/-- reflectsExactSequences_iff_reflectsShortComplexExact' -/
lemma reflectsExactSequences_iff_reflectsShortComplexExact' (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [HasZeroObject D] :
    F.ReflectsExactSequences ↔
      (∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f = 0 → f = 0) ∧
      ∀ (S : ShortComplex C), (S.map F).Exact → S.Exact := by
  constructor
  · intro hF
    exact ⟨fun _ _ => F.eq_zero_of_map_eq_zero, ReflectsExactSequences.reflectsShortComplexExact F⟩
  · rintro ⟨hF₁, hF₂⟩
    refine ⟨fun {X Y Z} f g w₂ ex₂ => ?_⟩
    have H := hF₁ (f ≫ g) (by rw [F.map_comp, w₂])
    exact ⟨H, hF₂ (ShortComplex.mk f g H) ex₂⟩

end

section

variable [Abelian C] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms] [Faithful F]

set_option backward.isDefEq.respectTransparency false in
-- adapted from the proof in `CategoryTheory.Abelian.Exact` using the previous homology API
instance reflectsExactSequencesOfPreservesZeroMorphismsOfFaithful : F.ReflectsExactSequences := by
  rw [reflectsExactSequences_iff_reflectsShortComplexExact']
  refine ⟨fun _ _ f hf => F.map_injective (by rw [hf, F.map_zero]),
    fun S hS => ?_⟩
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at hS ⊢
  dsimp at hS
  obtain ⟨k, hk⟩ := kernel.lift' (F.map S.g) (F.map (kernel.ι S.g)) (by
    rw [← F.map_comp, kernel.condition, F.map_zero])
  obtain ⟨l, hl⟩ := cokernel.desc' (F.map S.f) (F.map (cokernel.π S.f)) (by
    rw [← F.map_comp, cokernel.condition, F.map_zero])
  apply F.map_injective
  rw [F.map_comp, ← hk, ← hl, assoc, reassoc_of% hS, zero_comp, comp_zero, F.map_zero]

end

end Functor

end CategoryTheory
