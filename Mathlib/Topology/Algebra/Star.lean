/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Algebra.Star.Basic

/-!
# Continuity of `star`

This file defines the `ContinuousStar` typeclass, along with instances on `Pi`, `Prod`,
`MulOpposite`, and `Units`.
-/

open Filter Topology

/-- Basic hypothesis to talk about a topological space with a continuous `star` operator. -/
class ContinuousStar (R : Type*) [TopologicalSpace R] [Star R] : Prop where
  /-- The `star` operator is continuous. -/
  continuous_star : Continuous (star : R → R)

export ContinuousStar (continuous_star)

section Continuity

variable {α R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R]

theorem continuousOn_star {s : Set R} : ContinuousOn star s :=
  continuous_star.continuousOn

theorem continuousWithinAt_star {s : Set R} {x : R} : ContinuousWithinAt star s x :=
  continuous_star.continuousWithinAt

theorem continuousAt_star {x : R} : ContinuousAt star x :=
  continuous_star.continuousAt

theorem tendsto_star (a : R) : Tendsto star (𝓝 a) (𝓝 (star a)) :=
  continuousAt_star

theorem Filter.Tendsto.star {f : α → R} {l : Filter α} {y : R} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => star (f x)) l (𝓝 (star y)) :=
  (continuous_star.tendsto y).comp h

variable [TopologicalSpace α] {f : α → R} {s : Set α} {x : α}

@[continuity, fun_prop]
theorem Continuous.star (hf : Continuous f) : Continuous fun x => star (f x) :=
  continuous_star.comp hf

@[fun_prop]
theorem ContinuousAt.star (hf : ContinuousAt f x) : ContinuousAt (fun x => star (f x)) x :=
  continuousAt_star.comp hf

@[fun_prop]
theorem ContinuousOn.star (hf : ContinuousOn f s) : ContinuousOn (fun x => star (f x)) s :=
  continuous_star.comp_continuousOn hf

theorem ContinuousWithinAt.star (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => star (f x)) s x :=
  Filter.Tendsto.star hf

/-- The star operation bundled as a continuous map. -/
@[simps]
def starContinuousMap : C(R, R) :=
  ⟨star, continuous_star⟩

end Continuity

section Instances

variable {R S ι : Type*}

instance [Star R] [Star S] [TopologicalSpace R] [TopologicalSpace S] [ContinuousStar R]
    [ContinuousStar S] : ContinuousStar (R × S) :=
  ⟨(continuous_star.comp continuous_fst).prodMk (continuous_star.comp continuous_snd)⟩

instance {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Star (C i)]
    [∀ i, ContinuousStar (C i)] : ContinuousStar (∀ i, C i) where
  continuous_star := continuous_pi fun i => Continuous.star (continuous_apply i)

instance [Star R] [TopologicalSpace R] [ContinuousStar R] : ContinuousStar Rᵐᵒᵖ :=
  ⟨MulOpposite.continuous_op.comp <| MulOpposite.continuous_unop.star⟩

instance [Monoid R] [StarMul R] [TopologicalSpace R] [ContinuousStar R] :
    ContinuousStar Rˣ :=
  ⟨continuous_induced_rng.2 Units.continuous_embedProduct.star⟩

end Instances
