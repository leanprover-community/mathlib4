/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.equicontinuity
! leanprover-community/mathlib commit 01ad394a11bf06b950232720cf7e8fc6b22f0d6a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.UniformConvergence

/-!
# Algebra-related equicontinuity criterions
-/


open Function

open UniformConvergence

@[to_additive]
theorem equicontinuous_of_equicontinuousAt_one {ι G M hom : Type _} [TopologicalSpace G]
    [UniformSpace M] [Group G] [Group M] [TopologicalGroup G] [UniformGroup M]
    [MonoidHomClass hom G M] (F : ι → hom) (hf : EquicontinuousAt (coeFn ∘ F) (1 : G)) :
    Equicontinuous (coeFn ∘ F) :=
  by
  letI : CoeFun hom fun _ => G → M := FunLike.hasCoeToFun
  rw [equicontinuous_iff_continuous]
  rw [equicontinuousAt_iff_continuousAt] at hf
  let φ : G →* ι → M :=
    { toFun := swap (coeFn ∘ F)
      map_one' := by ext <;> exact map_one _
      map_mul' := fun a b => by ext <;> exact map_mul _ _ _ }
  exact continuous_of_continuousAt_one φ hf
#align equicontinuous_of_equicontinuous_at_one equicontinuous_of_equicontinuousAt_one
#align equicontinuous_of_equicontinuous_at_zero equicontinuous_of_equicontinuous_at_zero

@[to_additive]
theorem uniformEquicontinuous_of_equicontinuousAt_one {ι G M hom : Type _} [UniformSpace G]
    [UniformSpace M] [Group G] [Group M] [UniformGroup G] [UniformGroup M] [MonoidHomClass hom G M]
    (F : ι → hom) (hf : EquicontinuousAt (coeFn ∘ F) (1 : G)) : UniformEquicontinuous (coeFn ∘ F) :=
  by
  letI : CoeFun hom fun _ => G → M := FunLike.hasCoeToFun
  rw [uniformEquicontinuous_iff_uniformContinuous]
  rw [equicontinuousAt_iff_continuousAt] at hf
  let φ : G →* ι → M :=
    { toFun := swap (coeFn ∘ F)
      map_one' := by ext <;> exact map_one _
      map_mul' := fun a b => by ext <;> exact map_mul _ _ _ }
  exact uniformContinuous_of_continuousAt_one φ hf
#align uniform_equicontinuous_of_equicontinuous_at_one uniformEquicontinuous_of_equicontinuousAt_one
#align uniform_equicontinuous_of_equicontinuous_at_zero uniform_equicontinuous_of_equicontinuous_at_zero

