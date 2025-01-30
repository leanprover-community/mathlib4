/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/

import Mathlib.Algebra.Central.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!

## Main Results

- `Algebra.IsCentral.left_of_tensor`: If `B` and `C` are nontrivial finite dimensional
  `K`-algebras, and `B ⊗[K] C` is a central algebra over `K`, then `B` is a
  central algebra over `K`.
- `Algebra.IsCentral.right_of_tensor`: If `B` and `C` are nontrivial finite dimensional
  `K`-algebras, and `B ⊗[K] C` is a central algebra over `K`, then `C` is a
  central algebra over `K`.

## Tags
Central Algebras, Central Simple Algebras, Noncommutative Algebra
-/

universe u v

open TensorProduct

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

lemma Algebra.TensorProduct.includeLeft_map_center_le :
    (Subalgebra.center K B).map includeLeft ≤ Subalgebra.center K (B ⊗[K] C) := by
  intro x hx
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨b, hb0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b' c => simp [hb0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

lemma Algebra.TensorProduct.includeRight_mep_center_le :
    (Subalgebra.center K C).map includeRight ≤ Subalgebra.center K (B ⊗[K] C) := fun x hx ↦ by
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨c, hc0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b c' => simp [hc0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

namespace Algebra.IsCentral

open Algebra.TensorProduct in
lemma left_of_tensor (inj : Function.Injective (algebraMap K C)) [Module.Flat K B]
    [hbc : Algebra.IsCentral K (B ⊗[K] C)] : IsCentral K B where
  out := (Subalgebra.map_le.mp ((includeLeft_map_center_le K B C).trans hbc.1)).trans
    fun _ ⟨k, hk⟩ ↦ ⟨k, includeLeft_injective (S := K) inj hk⟩

lemma right_of_tensor (inj : Function.Injective (algebraMap K B)) [Module.Flat K C]
    [Algebra.IsCentral K (B ⊗[K] C)] : IsCentral K C :=
  have : IsCentral K (C ⊗[K] B) := IsCentral.of_algEquiv K _ _ <| Algebra.TensorProduct.comm _ _ _
  left_of_tensor K C B inj

/-- Let `A` and `B` be two algebras over a field `K`, if `A ⊗[K] B` is central and `B` is
  non-trivial, then `A` is central. -/
lemma left_of_tensor' (K A B : Type*) [Field K] [Ring A] [Ring B] [Nontrivial B]
    [Algebra K A] [Algebra K B] [IsCentral K (A ⊗[K] B)] : IsCentral K A :=
  left_of_tensor K A B <| NoZeroSMulDivisors.algebraMap_injective K B

/-- Let `A` and `B` be two algebras over a field `K`, if `A ⊗[K] B` is central and `A` is
  non-trivial, then `B` is central. -/
lemma right_of_tensor' (K A B : Type*) [Field K] [Ring A] [Ring B] [Nontrivial A]
    [Algebra K A] [Algebra K B] [IsCentral K (A ⊗[K] B)] : IsCentral K B :=
  right_of_tensor K A B <| NoZeroSMulDivisors.algebraMap_injective K A


end Algebra.IsCentral
