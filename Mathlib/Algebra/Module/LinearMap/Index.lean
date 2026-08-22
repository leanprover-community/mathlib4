/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Exact.Sequence
public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The index of a linear map

In this file we define the index of a linear map and provide some basic API.

## Main definitions / results:

* `LinearMap.index`: the index of a linear map, with sign convention `index = dim ker - dim coker`.
* `LinearMap.index_comp`: the index is additive under composition.

-/

noncomputable section

namespace LinearMap

open Function Module

variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

section Ring

variable {R : Type*} [Ring R] [Module R M] [Module R N] (f : M →ₗ[R] N)

public class HasIndex : Prop where
  finite_ker : f.ker.FG
  finite_coker : f.range.CoFG

instance (priority := 100) [f.HasIndex] : Module.Finite R f.ker := .of_fg HasIndex.finite_ker
instance (priority := 100) [f.HasIndex] : Module.Finite R (N ⧸ f.range) := HasIndex.finite_coker

/-- The index of a linear map with sign convention `index = dim ker - dim coker`.

This is only well behaved under the assumption `f.HasIndex`; otherwise the value is junk. -/
public def index : ℤ := finrank R f.ker - finrank R (N ⧸ f.range)

variable {f}

theorem HasIndex.of_eq (f' : M →ₗ[R] N) (eq : f = f') [f'.HasIndex] : f.HasIndex := eq ▸ ‹_›

public lemma index_eq_finrank_sub :
    f.index = finrank R f.ker - finrank R (N ⧸ f.range) := by
  rfl

instance [Subsingleton R] : f.HasIndex where
  finite_ker := .of_finite
  finite_coker := inferInstance

@[nontriviality] public lemma index_of_subsingleton [Subsingleton R] :
    f.index = 0 := by
  simp [index_eq_finrank_sub]

@[simp] public lemma index_zero :
    (0 : M →ₗ[R] N).index = finrank R M - finrank R N := by
  rw [index_eq_finrank_sub, ker_zero, range_zero]
  simpa using (Submodule.quotEquivOfEqBot _ rfl).finrank_eq

public lemma index_of_injective [Nontrivial R] (hf : Injective f) :
    f.index = - finrank R (N ⧸ f.range) := by
  simpa [index_eq_finrank_sub] using ker_eq_bot.2 hf ▸ finrank_bot _ _

variable [StrongRankCondition R]

public lemma index_of_surjective (hf : Surjective f) :
    f.index = finrank R f.ker := by
  rw [index_eq_finrank_sub, range_eq_top.mpr hf]
  simp [finrank_eq_zero_of_subsingleton]

set_option backward.isDefEq.respectTransparency.types false in
@[simp] public lemma index_id :
    (id : M →ₗ[R] M).index = 0 := by
  nontriviality R
  rw [index_eq_finrank_sub, range_id]
  simp [finrank_eq_zero_of_subsingleton]

@[simp] public lemma _root_.LinearEquiv.index_eq_zero {e : M ≃ₗ[R] N} :
    e.toLinearMap.index = 0 := by
  nontriviality R
  have := index_of_injective e.injective
  have := index_of_surjective e.surjective
  lia

instance [IsNoetherian R M] [Module.Finite R N] : f.HasIndex where
  finite_ker := .of_finite
  finite_coker := inferInstance

end Ring

section DivisionRing

variable {k : Type*} [DivisionRing k] [Module k M] [Module k N] [Module k P]
  {f : M →ₗ[k] N} {g : N →ₗ[k] P}

public lemma hasIndex_iff_exists_isQuasiInverse :
    f.HasIndex ↔ ∃ g : N →ₗ[k] M, g.IsQuasiInverse f := by
  constructor
  · sorry
  · rintro ⟨g, hg⟩
    sorry

@[simp] public lemma index_neg :
    (-f).index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub, ker_neg, range_neg]

public lemma index_eq_of_finiteDimensional [FiniteDimensional k M] [FiniteDimensional k N] :
    f.index = finrank k M - finrank k N := by
  -- `0 → f.ker → M → N → f.coker → 0`
  rw [index_eq_finrank_sub]
  have h₁ := f.range.finrank_quotient_add_finrank
  have h₂ := f.quotKerEquivRange.finrank_eq
  have h₃ := f.ker.finrank_quotient_add_finrank
  lia

instance [f.HasIndex] [g.HasIndex] : (g ∘ₗ f).HasIndex where
  finite_ker := by rw [ker_comp]; exact .of_finite
  finite_coker := by rw [range_comp]; infer_instance

set_option backward.isDefEq.respectTransparency.types false in
open Submodule in
@[simp] public lemma index_comp [f.HasIndex] [g.HasIndex] :
    (g ∘ₗ f).index = g.index + f.index := by
  -- `0 → f.ker → (g ∘ₗ f).ker → g.ker → f.coker → (g ∘ₗ f).coker → g.coker → 0`
  have aux : f.range ≤ comap g (g ∘ₗ f).range := by rw [← map_le_iff_le_comap, range_comp]
  let f₀ : f.ker →ₗ[k] (g ∘ₗ f).ker := inclusion <| ker_le_ker_comp f g
  let f₁ : (g ∘ₗ f).ker →ₗ[k] g.ker := f.restrict <| by simp
  let f₂ : g.ker →ₗ[k] N ⧸ f.range := f.range.mkQ ∘ₗ g.ker.subtype
  let f₃ : (N ⧸ f.range) →ₗ[k] P ⧸ (g ∘ₗ f).range := f.range.mapQ (g ∘ₗ f).range g aux
  let f₄ : (P ⧸ (g ∘ₗ f).range) →ₗ[k] P ⧸ g.range := factor <| range_comp_le_range f g
  have h₀ : Injective f₀ := inclusion_injective _
  have h₁ : Exact f₀ f₁ := by rw [exact_iff]; simp [f₀, f₁, ker_restrict, range_inclusion]
  have h₂ : Exact f₁ f₂ := by rw [exact_iff]; simp [f₁, f₂, ker_comp, map_comap_eq]
  have h₃ : Exact f₂ f₃ := by rw [exact_iff]; simp [f₂, f₃, range_comp, ker_mapQ, comap_map_eq]
  have h₄ : Exact f₃ f₄ := by rw [exact_iff]; simp [f₃, f₄, factor, ker_mapQ, range_mapQ]
  have h₅ : Surjective f₄ := factor_surjective _
  grind [index, sum_neg_one_pow_finrank_eq_zero_of_exact_six f₀ f₁ f₂ f₃ f₄ h₀ h₁ h₂ h₃ h₄ h₅]

end DivisionRing

section Field

variable {k : Type*} [Field k] [Module k M] [Module k N] {f : M →ₗ[k] N}

public lemma index_smul (t : k) (ht : t ≠ 0) :
    (t • f).index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub, ker_smul _ _ ht, range_smul _ _ ht]

end Field

end LinearMap
