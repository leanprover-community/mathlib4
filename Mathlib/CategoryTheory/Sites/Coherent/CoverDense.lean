/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EffectiveEpi.Enough
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.DenseSubsite
/-!

# Cover-dense functors into precoherent categories

We prove that if for a functor `F : C ⥤ D` into a precoherent category we have
`F.EffectivelyEnough`, then `F.IsCoverDense (coherentTopology _)`.

We give the corresponding result for the regular topology as well.
-/

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  [F.EffectivelyEnough]

namespace Functor

lemma isCoverDense_of_generate_singleton_functor_π_mem (K : GrothendieckTopology D)
    (h : ∀ B, Sieve.generate (Presieve.singleton (F.π B)) ∈ K B) : F.IsCoverDense K where
  is_cover B := by
    refine K.superset_covering ?_ (h B)
    intro Y f ⟨Z, g, _, h, w⟩
    cases h
    exact ⟨⟨_, g, F.π B, w⟩⟩

end Functor

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

instance : F.IsCoverDense (coherentTopology _) :=
  F.isCoverDense_of_generate_singleton_functor_π_mem _ (generate_singleton_functor_π_mem F)

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

instance : F.IsCoverDense (regularTopology _) :=
  F.isCoverDense_of_generate_singleton_functor_π_mem _ (generate_singleton_functor_π_mem F)

end regularTopology
