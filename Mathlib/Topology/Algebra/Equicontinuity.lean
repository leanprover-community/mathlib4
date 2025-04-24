/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.Algebra.UniformConvergence
import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Algebra-related equicontinuity criterions
-/


open Function

open UniformConvergence

@[to_additive]
theorem equicontinuous_of_equicontinuousAt_one {ι G M hom : Type*} [TopologicalSpace G]
    [UniformSpace M] [Group G] [Group M] [IsTopologicalGroup G] [IsUniformGroup M]
    [FunLike hom G M] [MonoidHomClass hom G M] (F : ι → hom)
    (hf : EquicontinuousAt ((↑) ∘ F) (1 : G)) :
    Equicontinuous ((↑) ∘ F) := by
  rw [equicontinuous_iff_continuous]
  rw [equicontinuousAt_iff_continuousAt] at hf
  let φ : G →* (ι →ᵤ M) :=
    { toFun := swap ((↑) ∘ F)
      map_one' := by dsimp [UniformFun]; ext; exact map_one _
      map_mul' := fun a b => by dsimp [UniformFun]; ext; exact map_mul _ _ _ }
  exact continuous_of_continuousAt_one φ hf

@[to_additive]
theorem uniformEquicontinuous_of_equicontinuousAt_one {ι G M hom : Type*} [UniformSpace G]
    [UniformSpace M] [Group G] [Group M] [IsUniformGroup G] [IsUniformGroup M]
    [FunLike hom G M] [MonoidHomClass hom G M]
    (F : ι → hom) (hf : EquicontinuousAt ((↑) ∘ F) (1 : G)) :
    UniformEquicontinuous ((↑) ∘ F) := by
  rw [uniformEquicontinuous_iff_uniformContinuous]
  rw [equicontinuousAt_iff_continuousAt] at hf
  let φ : G →* (ι →ᵤ M) :=
    { toFun := swap ((↑) ∘ F)
      map_one' := by dsimp [UniformFun]; ext; exact map_one _
      map_mul' := fun a b => by dsimp [UniformFun]; ext; exact map_mul _ _ _ }
  exact uniformContinuous_of_continuousAt_one φ hf
