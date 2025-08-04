/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Multilinear maps in relation to bases.

This file proves lemmas about the action of multilinear maps on basis vectors.

-/


open MultilinearMap

variable {ι R : Type*} [CommSemiring R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

/-- Two multilinear maps indexed by a `Fintype` are equal if they are equal when all arguments
are basis vectors. -/
theorem Module.Basis.ext_multilinear [Finite ι] {f g : MultilinearMap R M N} {ιM : ι → Type*}
    (e : ∀ i, Basis (ιM i) R (M i))
    (h : ∀ v : (i : ι) → ιM i, (f fun i ↦ e i (v i)) = g fun i ↦ e i (v i)) : f = g := by
  cases nonempty_fintype ι
  classical
  ext m
  rcases Function.Surjective.piMap (fun i ↦ (e i).repr.symm.surjective) m with ⟨x, rfl⟩
  unfold Pi.map
  simp_rw [(e _).repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum_finset, map_smul_univ, h]

@[deprecated (since := "2025-05-12")]
alias Basis.ext_multilinear_fin := Module.Basis.ext_multilinear
