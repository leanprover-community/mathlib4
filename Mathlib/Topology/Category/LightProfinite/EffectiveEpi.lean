/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHausLike.EffectiveEpi
import Mathlib.Topology.Category.LightProfinite.Limits
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
/-!

# Effective epimorphisms in `LightProfinite`

This file proves that `EffectiveEpi`, `Epi` and `Surjective` are all equivalent in `LightProfinite`.
As a consequence we prove that `LightProfinite` is `Preregular`. It follows from the constructions
in `LightProfinite/Limits.lean` that `LightProfinite` is `FinitaryExtensive`. Together this implies
that it is `Precoherent`.

-/

universe u

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

open CategoryTheory Limits CompHausLike

namespace LightProfinite

theorem effectiveEpi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨struct f h⟩⟩⟩
  rw [← epi_iff_surjective]
  infer_instance

instance : Preregular LightProfinite := by
  apply CompHausLike.preregular
  intro _ _ f
  exact (effectiveEpi_iff_surjective f).mp

-- Was an `example`, but that made the linter complain about unused imports
instance : Precoherent LightProfinite.{u} := inferInstance

end LightProfinite
