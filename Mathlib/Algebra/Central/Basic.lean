/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Jujian Zhang, Yunzhou Xie
-/

import Mathlib.Algebra.Central.Defs

/-!
# Central Algebras

In this file, we prove some basic results about central algebras over a commutative ring.

## Main results

- `Algebra.IsCentral.center_eq_bot`: the center of a central algebra over `K` is equal to `K`.
- `Algebra.IsCentral.self`: a commutative ring is a central algebra over itself.
- `Algebra.IsCentral.baseField_essentially_unique`: Let `D/K/k` be a tower of scalars where
  `K` and `k` are fields. If `D` is a nontrivial central algebra over `k`, `K` is isomorphic to `k`.
-/

universe u v

namespace Algebra.IsCentral

variable (K : Type u) [CommSemiring K] (D D' : Type v) [Semiring D] [Algebra K D]
  [h : IsCentral K D] [Semiring D'] [Algebra K D']

@[simp]
lemma center_eq_bot : Subalgebra.center K D = ⊥ := eq_bot_iff.2 IsCentral.out

variable {D} in
lemma mem_center_iff {x : D} : x ∈ Subalgebra.center K D ↔ ∃ (a : K), x = algebraMap K D a := by
  rw [center_eq_bot, Algebra.mem_bot]
  simp [eq_comm]

instance self : IsCentral K K where
  out x := by simp [Algebra.mem_bot]

lemma baseField_essentially_unique
    (k K D : Type*) [Field k] [Field K] [Ring D] [Nontrivial D]
    [Algebra k K] [Algebra K D] [Algebra k D] [IsScalarTower k K D]
    [IsCentral k D] :
    Function.Bijective (algebraMap k K) := by
  haveI : IsCentral K D :=
  { out := fun x ↦ show x ∈ Subalgebra.center k D → _ by
      simp only [center_eq_bot, mem_bot, Set.mem_range, forall_exists_index]
      rintro x rfl
      exact  ⟨algebraMap k K x, by simp [algebraMap_eq_smul_one, smul_assoc]⟩ }
  refine ⟨FaithfulSMul.algebraMap_injective k K, fun x => ?_⟩
  have H : algebraMap K D x ∈ (Subalgebra.center K D : Set D) := Subalgebra.algebraMap_mem _ _
  rw [show (Subalgebra.center K D : Set D) = Subalgebra.center k D by rfl] at H
  simp only [center_eq_bot, coe_bot, Set.mem_range] at H
  obtain ⟨x', H⟩ := H
  exact ⟨x', (algebraMap K D).injective <| by simp [← H, algebraMap_eq_smul_one]⟩

lemma of_algEquiv (e : D ≃ₐ[K] D') : IsCentral K D' where
  out x hx :=
    have ⟨k, hk⟩ := h.1 ((MulEquivClass.apply_mem_center_iff e.symm).mpr hx)
    ⟨k, by simpa [ofId] using congr(e $hk)⟩

open MulOpposite in
/-- Opposite algebra of a central algebra is central. This instance combined with the coming
  `IsSimpleRing` instance for the opposite of central simple algebra will be an
  inverse for an element in `BrauerGroup`, find out more about this in
  `Mathlib/Algebra/BrauerGroup/Basic.lean`. -/
instance : IsCentral K Dᵐᵒᵖ where
  out z hz :=
    have ⟨k, hk⟩ := h.1 (MulOpposite.unop_mem_center_iff.mpr hz)
    ⟨k, by simpa using congr(op $hk)⟩

end Algebra.IsCentral
