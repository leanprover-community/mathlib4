/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yury Kudryashov, Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM

/-!
# Topology of compact convergence on the space of continuous linear maps

In this file, we define a type alias `CompactConvergenceCLM` for `E →L[𝕜] F`,
endowed with the topology of uniform convergence on compact subsets.

More concretely, `CompactConvergenceCLM` is an abbreviation for
`UniformConvergenceCLM σ F {(S : Set E) | IsCompact S}`. We denote it by `E →SL_c[σ] F`.

Here is a list of type aliases for `E →L[𝕜] F` endowed with various topologies :
* `ContinuousLinearMap`: topology of bounded convergence
* `UniformConvergenceCLM`: topology of `𝔖`-convergence, for a general `𝔖 : Set (Set E)`
* `CompactConvergenceCLM`: topology of compact convergence
* `PointwiseConvergenceCLM`: topology of pointwise convergence, also called "weak-* topology"
  or "strong-operator topology" depending on the context
* `ContinuousLinearMapWOT`: topology of weak pointwise convergence, also called "weak-operator
  topology"

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, bounded convergence
-/

@[expose] public section

open Bornology Filter Function Set Topology ContinuousLinearMap
open scoped UniformConvergence Uniformity

section CompactSets

/-! ### Topology of compact convergence for continuous linear maps -/

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E F G : Type*}
  [AddCommGroup E] [Module 𝕜₁ E]
  [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G]

variable (E F σ) in
/-- The topology of compact convergence on `E →L[𝕜] F`. -/
abbrev CompactConvergenceCLM [TopologicalSpace E] [TopologicalSpace F] :=
  UniformConvergenceCLM σ F {(S : Set E) | IsCompact S}

@[inherit_doc]
scoped[CompactConvergenceCLM]
notation:25 E " →SL_c[" σ "] " F => CompactConvergenceCLM σ E F

@[inherit_doc]
scoped[CompactConvergenceCLM]
notation:25 E " →L_c[" R "] " F => CompactConvergenceCLM (RingHom.id R) E F

namespace CompactConvergenceCLM

instance continuousSMul [RingHomSurjective σ] [RingHomIsometric σ]
    [UniformSpace E] [IsUniformAddGroup E] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜₁ E] [ContinuousSMul 𝕜₂ F] :
    ContinuousSMul 𝕜₂ (E →SL_c[σ] F) :=
  UniformConvergenceCLM.continuousSMul σ F { S | IsCompact S }
    (fun _ hs => hs.totallyBounded.isVonNBounded 𝕜₁)

instance instContinuousEvalConst [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup F] : ContinuousEvalConst (E →SL_c[σ] F) E F :=
  UniformConvergenceCLM.continuousEvalConst σ F _ sUnion_isCompact_eq_univ

instance instT2Space [TopologicalSpace E] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [T2Space F] : T2Space (E →SL_c[σ] F) :=
  UniformConvergenceCLM.t2Space σ F _ sUnion_isCompact_eq_univ

protected theorem hasBasis_nhds_zero_of_basis [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SL_c[σ] F)).HasBasis (fun Si : Set E × ι => IsCompact Si.1 ∧ p Si.2)
      fun Si => { f : E →SL_c[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | IsCompact S }
    ⟨∅, isCompact_empty⟩
    (directedOn_of_sup_mem fun _ _ => IsCompact.union) h

protected theorem hasBasis_nhds_zero [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup F] :
    (𝓝 (0 : E →SL_c[σ] F)).HasBasis
      (fun SV : Set E × Set F => IsCompact SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => { f : E →SL_c[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  CompactConvergenceCLM.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

end CompactConvergenceCLM

section comp

variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

open scoped CompactConvergenceCLM

variable (G) in
/-- Specialization of `ContinuousLinearMap.precomp_uniformConvergenceCLM` to compact
convergence. -/
@[simps! apply]
def ContinuousLinearMap.precompCompactConvergenceCLM [IsTopologicalAddGroup G]
    [ContinuousConstSMul 𝕜₃ G] (L : E →SL[σ] F) : (F →SL_c[τ] G) →L[𝕜₃] E →SL_c[ρ] G :=
  L.precompUniformConvergenceCLM G _ _ (fun _ hs ↦ hs.image L.continuous)

@[deprecated (since := "2026-01-27")]
alias precomp_compactConvergenceCLM := precompCompactConvergenceCLM

@[deprecated (since := "2026-01-27")]
alias precomp_compactConvergenceCLM_apply := precompCompactConvergenceCLM_apply

variable (E) in
/-- Specialization of `ContinuousLinearMap.postcomp_uniformConvergenceCLM` to compact
convergence. -/
@[simps! apply]
def ContinuousLinearMap.postcompCompactConvergenceCLM [IsTopologicalAddGroup F]
    [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₂ F]
    (L : F →SL[τ] G) : (E →SL_c[σ] F) →SL[τ] E →SL_c[ρ] G :=
  L.postcompUniformConvergenceCLM _

@[deprecated (since := "2026-01-27")]
alias postcomp_compactConvergenceCLM := postcompCompactConvergenceCLM

@[deprecated (since := "2026-01-27")]
alias postcomp_compactConvergenceCLM_apply := postcompCompactConvergenceCLM_apply

end comp

end CompactSets
