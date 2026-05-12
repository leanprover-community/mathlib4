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

public section FredholmOperators

open Topology ContinuousLinearMap Submodule

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
    (a • f).range ≤f.range := by
  by_cases ha : a = 0
  · simp_all
  · exact f.range_smul a ha |>.le

variable (𝕜 E F) in
def FiniteRank : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {u | FiniteDimensional 𝕜 u.range}
  add_mem' {u v} (hu : FiniteDimensional 𝕜 u.range) (hv : FiniteDimensional 𝕜 v.range) :=
    Submodule.finiteDimensional_of_le <| LinearMap.range_add_le u.toLinearMap v.toLinearMap
  zero_mem' := by simp
  smul_mem' c {u} (hu : FiniteDimensional 𝕜 u.range) := by
    sorry

scoped instance : Setoid (E →L[𝕜] F) := (FiniteRank 𝕜 E F).quotientRel

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

/- ## Kernel -/

/- ## Coernel -/

/- ## GoodRelation -/

/- ## IsStrict Using Technical Lemma -/

/- ## Quasi-inverse is inverse on a finite codim space -/

section LinearMap

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

theorem LinearMap.mem_ker_of_mem_ker (u : E →ₗ[𝕜] F) (v : F →ₗ[𝕜] E)
    (x : E) (hx : x ∈ (.id - v ∘ₗ u).ker) :
    u x ∈ (.id - u ∘ₗ v).ker := by
  simp_all [← map_sub]

theorem LinearMap.restrict_inverse (u : E →ₗ[𝕜] F) (v : F →ₗ[𝕜] E) :
    (u.restrict (u.mem_ker_of_mem_ker v)) ∘ₗ (v.restrict (v.mem_ker_of_mem_ker u)) = id := by
  ext x
  sorry

end LinearMap

variable {u : E →L[𝕜] F} {v : F →L[𝕜] E} [T1Space E]

theorem lemma2 (hr : v ∘L u ≈ .id 𝕜 E) :
    ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F),
      IsClosed E₁.carrier ∧ E₁.CoFG ∧ map u.toLinearMap E₁ ≤ F₁ ∧ map v.toLinearMap F₁ ≤ E₁ := by
  refine ⟨(.id 𝕜 E - v ∘L u).ker, (.id 𝕜 F - u ∘L v).ker, ContinuousLinearMap.isClosed_ker _,
    ?_, ?_⟩
  rw [← range_fg_iff_ker_cofg]
  sorry
  sorry


end FredholmOperators
