/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EffectiveEpi.Enough
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.DenseSubsite
/-!

# Projective objects in precoherent categories

We prove that if every object in the image of a functor `F : C ⥤ D` into a precoherent category is
projective, and we have `F.EffectivelyEnough`, then we have `F.IsCoverDense (coherentTopology _)`.

We give the corresponding result for the regular topology as well.
-/

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  [∀ (X : C), Projective (F.obj X)] [F.EffectivelyEnough]

namespace coherentTopology

variable [Precoherent D]

lemma generate_singleton_functor_π_mem (B : D) :
    Sieve.generate (Presieve.singleton (F.π B)) ∈ coherentTopology D B := by
  apply Coverage.saturate.of
  refine ⟨Unit, inferInstance, fun _ => F.over B,
    fun _ => F.π B, ?_ , ?_⟩
  · funext X f
    ext
    refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
    rintro ⟨⟩
    simp only [Presieve.singleton_eq_iff_domain]
  · rw [← effectiveEpi_iff_effectiveEpiFamily]
    infer_instance

instance : F.IsCoverDense (coherentTopology _) := by
  constructor
  intro B
  convert generate_singleton_functor_π_mem F B
  ext Y f
  refine ⟨fun ⟨⟨obj, lift, map, fact⟩⟩ ↦ ?_, fun ⟨Z, h, g, hypo1, hf⟩ ↦ ?_⟩
  · obtain ⟨p, p_factors⟩ := Projective.factors map (F.π B)
    refine ⟨_, ⟨lift ≫ p, ⟨(F.π B),
      ⟨Presieve.singleton.mk, by rw [← fact, ← p_factors, Category.assoc]⟩⟩⟩⟩
  · cases hypo1
    exact ⟨⟨_, h, F.π B, hf⟩⟩

end coherentTopology

namespace regularTopology

variable [Preregular D]

lemma generate_singleton_functor_π_mem (B : D) :
    Sieve.generate (Presieve.singleton (F.π B)) ∈ regularTopology D B := by
  apply Coverage.saturate.of
  refine ⟨F.over B, F.π B, ?_, inferInstance⟩
  funext X f
  ext
  refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
  rintro ⟨⟩
  simp only [Presieve.singleton_eq_iff_domain]

instance : F.IsCoverDense (regularTopology _) := by
  constructor
  intro B
  convert generate_singleton_functor_π_mem F B
  ext Y f
  refine ⟨fun ⟨⟨obj, lift, map, fact⟩⟩ ↦ ?_, fun ⟨Z, h, g, hypo1, hf⟩ ↦ ?_⟩
  · obtain ⟨p, p_factors⟩ := Projective.factors map (F.π B)
    refine ⟨_, ⟨lift ≫ p, ⟨(F.π B),
      ⟨Presieve.singleton.mk, by rw [← fact, ← p_factors, Category.assoc]⟩⟩⟩⟩
  · cases hypo1
    exact ⟨⟨_, h, F.π B, hf⟩⟩

end regularTopology
