/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EffectiveEpi.Enough
import Mathlib.CategoryTheory.EffectiveEpi.Preserves
import Mathlib.CategoryTheory.Sites.Coherent.RegularTopology
/-!

# Reflecting the property of being preregular

We prove that given a fully faithful functor `F : C ⥤ D`, with `Preregular D`, such that for every
object `X` of `D` there exists an object `W` of `C` with an effective epi `π : F.obj W ⟶ X`, the
category `C` is `Preregular`.
-/

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [F.EffectivelyEnough]
  [Preregular D] [F.Full] [F.Faithful]

lemma Functor.reflects_preregular : Preregular C where
  exists_fac f g _ := by
    obtain ⟨W, f', _, i, w⟩ := Preregular.exists_fac (F.map f) (F.map g)
    refine ⟨_, F.preimage (F.effectiveEpiOver W ≫ f'),
      ⟨F.effectiveEpi_of_map _ ?_, F.preimage (F.effectiveEpiOver W ≫ i), ?_⟩⟩
    · simp only [Functor.map_preimage]
      infer_instance
    · apply F.map_injective
      simp [w]

end CategoryTheory
