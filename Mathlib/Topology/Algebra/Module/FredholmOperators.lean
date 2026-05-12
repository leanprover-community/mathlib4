/-
Copyright (c) 2026 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.LinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [AddCommGroup E] [AddCommGroup F] [TopologicalSpace E] [TopologicalSpace F]
  [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]
variable {f : E →L[𝕜] F}

public section FredholmOperators

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
  carrier := {u | FiniteDimensional 𝕜 u.range}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

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
