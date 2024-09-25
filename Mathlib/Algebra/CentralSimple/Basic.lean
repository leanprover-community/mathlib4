/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Kevin Buzzard
-/

import Mathlib.Algebra.CentralSimple.Defs
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Central Simple Algebras

In this file, we prove some basic results about central simple algebras over a field.

## Main results

- `Algebra.IsCentralSimple.center_eq_bot`: the center of a central simple algebra over a field `K`
  is equal to `K`.
- `Algebra.IsCentralSimple.self`: a field is a central simple algebra over itself.
- `Algebra.IsCentralSimple.baseField_essentially_unique`: Let `D/K/k` is a tower of scalars where
  `K` and `k` are fields. If `D` is central simple over `k`, `K` is isomorphic to `k`.
-/

universe u v

namespace Algebra.IsCentralSimple

variable (K : Type u) [Field K] (D : Type v) [Ring D] [Algebra K D] [IsCentralSimple K D]

@[simp]
lemma center_eq_bot : Subalgebra.center K D = ⊥ := eq_bot_iff.2 IsCentralSimple.is_central

variable {D} in
lemma mem_center_iff {x : D} : x ∈ Subalgebra.center K D ↔ ∃ (a : K), x = algebraMap K D a := by
  rw [center_eq_bot, Algebra.mem_bot]
  simp [eq_comm]

instance self : IsCentralSimple K K where
  is_central x := by simp [Algebra.mem_bot]

lemma baseField_essentially_unique
    {k K D : Type*} [Field k] [Field K] [Ring D]
    [Algebra k K] [Algebra K D] [Algebra k D] [IsScalarTower k K D]
    [IsCentralSimple k D] :
    Function.Bijective (algebraMap k K) := by
  haveI : IsSimpleRing D := IsCentralSimple.is_simple k
  haveI : IsCentralSimple K D :=
  { is_central := fun x ↦ show x ∈ Subalgebra.center k D → _ by
      simp only [center_eq_bot, mem_bot, Set.mem_range, forall_exists_index]
      rintro x rfl
      exact  ⟨algebraMap k K x, by simp [algebraMap_eq_smul_one, smul_assoc]⟩
    is_simple := IsCentralSimple.is_simple k }
  refine ⟨NoZeroSMulDivisors.algebraMap_injective k K, fun x => ?_⟩
  have H : algebraMap K D x ∈ (Subalgebra.center K D : Set D) := Subalgebra.algebraMap_mem _ _
  rw [show (Subalgebra.center K D : Set D) = Subalgebra.center k D by rfl] at H
  simp only [center_eq_bot, coe_bot, Set.mem_range] at H
  obtain ⟨x', H⟩ := H
  exact ⟨x', (algebraMap K D).injective <| by simp [← H, algebraMap_eq_smul_one]⟩

end Algebra.IsCentralSimple
