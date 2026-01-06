/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Basic facts about algebra representations

This file collects basic general facts about algebra representations. The purpose of this file is
to have general results so that when we prove a corresponding fact about group representations
(or Lie algebra representations etc), we can deduce them as special cases of facts from this file.

-/

@[expose] public section

variable {A : Type*} (k V : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V]

/-- Schur's Lemma: If `V` is a representation of an algebra `A` over an algebraically closed field
`k`, then any endomorphism of `V` is scalar. -/
theorem scalar_linear_map_of_simple_alg_closed [IsSimpleModule A V] [FiniteDimensional k V]
    [IsAlgClosed k] (f : V →ₗ[A] V) : ∃ a : k, ∀ v : V, f v = a • v := by
  letI _ : Nontrivial V := by exact IsSimpleModule.nontrivial A V
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f : Module.End k V)
  set g := f + (-c) • (LinearMap.id : V →ₗ[A] V)
  have schur := LinearMap.bijective_or_eq_zero g
  suffices ¬Function.Bijective g by
    have hg := Or.resolve_left schur this
    use c
    intro v
    have h : g v = 0 := by simp [hg]
    dsimp [g] at h
    rw [neg_smul] at h
    exact eq_of_add_neg_eq_zero h
  intro ⟨inj, _⟩
  rw [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue] at hc
  apply Submodule.exists_mem_ne_zero_of_ne_bot at hc
  obtain ⟨b, hb, b_nz⟩ := hc
  rw [Module.End.mem_genEigenspace_one] at hb
  specialize @inj b 0
  apply b_nz
  apply inj
  dsimp [g]
  simp only [neg_smul, map_zero, smul_zero, add_zero]
  exact add_neg_eq_zero.mpr hb

/-- Any finite-dimensional irreducible representation of a commutative algebra over an algebraically
closed field is one-dimensional. -/
theorem one_dimensional_of_simple_of_abelian [IsSimpleModule A V] [FiniteDimensional k V]
    [IsAlgClosed k] [IsMulCommutative A] : Module.finrank k V = 1 := by
  letI _ : Nontrivial V := by exact IsSimpleModule.nontrivial A V
  obtain ⟨v, v_nz⟩ := exists_ne (0 : V)
  set U : Submodule A V := { Submodule.span k {v} with
    smul_mem' a w hw := by
      set f : V →ₗ[A] V := {
        toFun v := a • v
        map_add' x y := DistribMulAction.smul_add a x y
        map_smul' a' v := smul_comm a a' v
      }
      obtain ⟨t, ht⟩ := scalar_linear_map_of_simple_alg_closed k V f
      specialize ht w
      dsimp [f] at ht
      rw [ht]
      exact (k ∙ v).smul_mem' t hw
  }
  obtain hU | hU := eq_bot_or_eq_top U
  · exfalso
    have hv : v ∈ U := by exact Submodule.mem_span_singleton_self v
    rw [hU] at hv
    exact v_nz hv
  · rw [finrank_eq_one_iff_of_nonzero v v_nz]
    rw [Submodule.eq_top_iff'] at hU ⊢
    exact hU
