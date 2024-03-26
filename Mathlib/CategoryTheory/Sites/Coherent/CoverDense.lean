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

namespace coherentTopology

variable [Precoherent D]

lemma generate_singleton_functor_π_mem (B : D) :
    ∃ (X : C) (f : F.obj X ⟶ B), Sieve.generate (Presieve.singleton f) ∈ coherentTopology D B := by
  refine ⟨_, F.effectiveEpiOver B, ?_⟩
  apply Coverage.saturate.of
  refine ⟨Unit, inferInstance, fun _ => F.effectiveEpiOverObj B,
    fun _ => F.effectiveEpiOver B, ?_ , ?_⟩
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
    ∃ (X : C) (f : F.obj X ⟶ B), Sieve.generate (Presieve.singleton f) ∈ regularTopology D B := by
  refine ⟨_, F.effectiveEpiOver B, ?_⟩
  apply Coverage.saturate.of
  refine ⟨F.effectiveEpiOverObj B, F.effectiveEpiOver B, ?_, inferInstance⟩
  funext X f
  ext
  refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
  rintro ⟨⟩
  simp only [Presieve.singleton_eq_iff_domain]

instance : F.IsCoverDense (regularTopology _) :=
  F.isCoverDense_of_generate_singleton_functor_π_mem _ (generate_singleton_functor_π_mem F)

end regularTopology
