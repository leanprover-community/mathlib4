/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Adjoin.FG

/-!
# Finitely generated subalgebras of a base change obtained from an element

## Main results
- `exists_fg_and_mem_baseChange`: given an element `x` of a tensor product `A ⊗[R] B` of two
  `R`-algebras `A` and `B`, there exists a finitely generated subalgebra `C` of `B` such that `x`
  is contained in `C ⊗[R] B`.

-/

public section

open TensorProduct

lemma exists_fg_and_mem_baseChange {R A B : Type*} [CommSemiring R]
    [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] (x : A ⊗[R] B) :
    ∃ C : Subalgebra R B, C.FG ∧ x ∈ C.baseChange A := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  classical
  refine ⟨Algebra.adjoin R (S.image fun j ↦ j.2), ?_, ?_⟩
  · exact Subalgebra.fg_adjoin_finset _
  · exact hS ▸ Subalgebra.sum_mem _ fun s hs ↦ (Subalgebra.tmul_mem_baseChange
      (Algebra.subset_adjoin (Finset.mem_image_of_mem _ hs)) s.1)
