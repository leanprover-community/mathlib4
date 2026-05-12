/-
Copyright (c) 2026 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [AddCommGroup E] [AddCommGroup F] [TopologicalSpace E] [TopologicalSpace F]
  [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]
variable {f : E →L[𝕜] F}

public noncomputable section FredholmOperators

-- TODO: MOVE
@[simp]
lemma FiniteDimensional.range_zero {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R]
  [DivisionRing R₂] [AddCommMonoid M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
  [RingHomSurjective τ₁₂] : FiniteDimensional R₂ (0 : M →ₛₗ[τ₁₂] M₂).range := by
  rw [← Submodule.fg_iff_finiteDimensional, LinearMap.range_zero]
  exact Submodule.fg_bot

-- TODO: MOVE next to LinearMap.range_smul
lemma LinearMap.range_smul_le {K : Type*} {V : Type*} {V₂ : Type*} [Semifield K] [AddCommMonoid V]
    [Module K V] [AddCommMonoid V₂] [Module K V₂] (f : V →ₗ[K] V₂) (a : K) :
    (a • f).range ≤ f.range := by
  by_cases ha : a = 0
  · simp_all
  · exact f.range_smul a ha |>.le

section
variable {K : Type*} {V : Type*} {V₂ : Type*} [Field K] [AddCommMonoid V]
    [Module K V] [AddCommGroup V₂] [Module K V₂]

def LinearMap.hasFiniteRank (f : V →ₗ[K] V₂) := FiniteDimensional K f.range

@[simp] def LinearMap.hasFiniteRank.smul {f : V →ₗ[K] V₂}
    (hf : f.hasFiniteRank) (c : K) : (c • f).hasFiniteRank := by
  unfold LinearMap.hasFiniteRank at *
  rw [← Submodule.fg_iff_finiteDimensional] at *
  exact hf.of_le <| LinearMap.range_smul_le _ c

@[simp] def LinearMap.hasFiniteRank.zero : (0 : V →ₗ[K] V₂).hasFiniteRank := by
  unfold LinearMap.hasFiniteRank
  simp

@[simp] def LinearMap.hasFiniteRank.neg {f : V →ₗ[K] V₂}
    (hf : f.hasFiniteRank) : (-f).hasFiniteRank := by
  rw [show -f = (-1 : K) • f by module]
  apply hf.smul

@[simp] lemma LinearMap.hasFiniteRank.add {f g : V →ₗ[K] V₂}
    (hf : f.hasFiniteRank) (hg : g.hasFiniteRank) : (f + g).hasFiniteRank := by
  unfold LinearMap.hasFiniteRank at *
  exact Submodule.finiteDimensional_of_le <| LinearMap.range_add_le f g

@[simp] def LinearMap.hasFiniteRank.sub {f g : V →ₗ[K] V₂}
    (hf : f.hasFiniteRank) (hg : g.hasFiniteRank) : (f - g).hasFiniteRank := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

variable {V₃ : Type*} [AddCommGroup V₃] [Module K V₃]

lemma LinearMap.hasFiniteRank.comp_right {u : V →ₗ[K] V₂} (h : u.hasFiniteRank)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).hasFiniteRank := by
  unfold LinearMap.hasFiniteRank at *
  rw [← Submodule.fg_iff_finiteDimensional, LinearMap.range_comp] at *
  exact Submodule.FG.map v h

lemma LinearMap.hasFiniteRank.comp_left {v : V₂ →ₗ[K] V₃} (h : v.hasFiniteRank)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).hasFiniteRank := by
  unfold LinearMap.hasFiniteRank at *
  rw [← Submodule.fg_iff_finiteDimensional] at *
  exact h.of_le <| u.range_comp_le_range v

lemma LinearMap.hasFiniteRank.comp_sub_comp {u v : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃}
    (h : (u - v).hasFiniteRank) (h' : (u' - v').hasFiniteRank) :
    (u' ∘ₗ u - v' ∘ₗ v).hasFiniteRank := by
  rw [show u' ∘ₗ u - v' ∘ₗ v = (u' - v') ∘ₗ u + v' ∘ₗ (u - v) by ext; simp]
  exact (h'.comp_left u).add <| h.comp_right v'

end

open Topology ContinuousLinearMap

variable (f)

structure IsFredholm_struc : Prop where
  isStrict : IsStrictMap f
  isClosed_range : IsClosed (f.range : Set F)
  kerFG : FiniteDimensional 𝕜 f.toLinearMap.ker
  cokerFG : FiniteDimensional 𝕜 (F ⧸ f.range)

/-FAE: I don't like this definition that seems to fix `g` (making it a structure would be even more
  disgusting). -/
def IsFredholm_exists : Prop := ∃ g : F →L[𝕜] E,
  FiniteDimensional 𝕜 (f ∘L g - .id 𝕜 F).range  ∧ FiniteDimensional 𝕜 (g ∘L f - .id 𝕜 E).range

namespace QuotFiniteSubmodules
variable [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [ContinuousAdd E] [ContinuousAdd F]

variable (𝕜 E F) in
def FiniteRank : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {u | u.toLinearMap.hasFiniteRank}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

scoped instance : Setoid (E →L[𝕜] F) := (FiniteRank 𝕜 E F).quotientRel

lemma eqv_iff {u v : E →L[𝕜] F} : u ≈ v ↔ (u - v).toLinearMap.hasFiniteRank := by
  erw [← @Quotient.eq_iff_equiv, Submodule.Quotient.eq]
  rfl

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]  [Module 𝕜 G]
  [ContinuousConstSMul 𝕜 G] [ContinuousAdd G]

lemma rel_comp {u v : E →L[𝕜] F} {u' v' : F →L[𝕜] G} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘L u ≈ v' ∘L v := by
  rw [eqv_iff] at *
  exact h.comp_sub_comp h'

def IsFredholm_quot : Prop := ∃ g : F →L[𝕜] E,
  (f ∘L g ≈ .id 𝕜 F) ∧ (g ∘L f ≈ .id 𝕜 E)

end QuotFiniteSubmodules

theorem AnatoleDream_1 (hf : IsFredholm_struc f) : IsFredholm_exists f:= sorry

def AnatoleDream_1_symm (hf : IsFredholm_exists f) : IsFredholm_struc f := sorry

open QuotFiniteSubmodules in
theorem AnatoleDream_2 [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [ContinuousAdd E]
    [ContinuousAdd F] (hf : IsFredholm_struc f) : IsFredholm_quot f := sorry

open QuotFiniteSubmodules in
def AnatoleDream_2_symm [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [ContinuousAdd E]
    [ContinuousAdd F] (hf : IsFredholm_quot f) : (IsFredholm_struc f) := sorry

/- ## API -/

namespace LinearMap

open Module

variable (k : Type*) [Field k] [Module k E] [Module k F] (f : E →ₗ[k] F)

/-- The index of a linear map.

In the case that either the kernel or cokernel is not finite-dimensional, the value is junk. -/
def index : ℤ := finrank k f.ker - finrank k (F ⧸ f.range)

@[simp] lemma index_id :
    (id : E →ₗ[k] E).index = 0 := by
  sorry

@[simp] lemma index_zero :
    (0 : E →ₗ[k] F).index = finrank k E - finrank k F := by
  sorry

lemma index_smul (t : k) (ht : t ≠ 0) :
    (t • f).index = f.index := by
  sorry

lemma index_neg
    /- TODO required assumptions. -/ :
    (-f).index = -f.index := by
  sorry

lemma index_comp {G : Type*} [AddCommGroup G] [Module k G] (g : F →ₗ[k] G)
    /- TODO required assumptions. -/ :
    (g ∘ₗ f).index = g.index + f.index := by
  sorry

lemma index_eq_of_finiteDimensional [FiniteDimensional k E] [FiniteDimensional k F] :
    f.index = finrank k E - finrank k F := by
  -- 0 → f.ker → E → F → f.coker → 0
  sorry

end LinearMap

/- ## Kernel -/

-- uses only `g.comp f ≃ 1`
lemma KernelFG_of_isFredholm (hf : IsFredholm_exists f) : FiniteDimensional 𝕜 f.ker := by
  obtain ⟨g, -, hg_left⟩ := hf
  have : f.ker ≤ (g.comp f - 1).range := by
    intro x hx
    use -x
    simp only [LinearMap.mem_ker, coe_coe] at hx
    simp [hx]
  rw [← Submodule.fg_iff_finiteDimensional]
  apply Submodule.FG.of_le _ this
  exact Module.Finite.iff_fg.mp hg_left





/- ## Coernel -/

/- ## GoodRelation -/

/- ## IsStrict Using Technical Lemma -/




end FredholmOperators
