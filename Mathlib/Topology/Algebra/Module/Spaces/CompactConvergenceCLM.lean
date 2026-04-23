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
* `PointwiseConvergenceCLM`: topology of pointwise convergence, also called "weak-\* topology"
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
  UniformConvergenceCLM σ F {S : Set E | IsCompact S}

@[inherit_doc]
scoped[CompactConvergenceCLM]
notation:25 E " →SL_c[" σ "] " F => CompactConvergenceCLM σ E F

@[inherit_doc]
scoped[CompactConvergenceCLM]
notation:25 E " →L_c[" R "] " F => CompactConvergenceCLM (RingHom.id R) E F

namespace CompactConvergenceCLM

instance continuousSMul [RingHomSurjective σ] [RingHomIsometric σ]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜₁ E] [ContinuousSMul 𝕜₂ F] :
    ContinuousSMul 𝕜₂ (E →SL_c[σ] F) :=
  UniformConvergenceCLM.continuousSMul σ F { S | IsCompact S }
    (fun _ hs => hs.isVonNBounded 𝕜₁)

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

namespace ContinuousLinearEquiv

/-! ### Continuous linear equivalences -/

open scoped CompactConvergenceCLM

section Semilinear

variable {𝕜 : Type*} {𝕜₂ : Type*} {𝕜₃ : Type*} {𝕜₄ : Type*} {E : Type*} {F : Type*}
  {G : Type*} {H : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜₃ G] [Module 𝕜₄ H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₄ H]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  {σ₃₄ : 𝕜₃ →+* 𝕜₄} {σ₄₃ : 𝕜₄ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₁₄ : 𝕜 →+* 𝕜₄} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]

/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. This version is for the type alias
`CompactConvergenceCLM`. -/
def compactConvergenceCLMCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) :
    (E →SL_c[σ₁₄] H) ≃SL[σ₄₃] (F →SL_c[σ₂₃] G) :=
  ContinuousLinearEquiv.uniformConvergenceCLMCongrSL e₁₂ e₄₃ _ _ fun s ↦ by
    simp [← e₁₂.toHomeomorph.isCompact_preimage]

@[simp]
lemma compactConvergenceCLMCongrSL_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (φ : E →SL_c[σ₁₄] H) (f : F) :
    compactConvergenceCLMCongrSL e₁₂ e₄₃ φ f = e₄₃ (φ (e₁₂.symm f)) :=
  rfl

@[simp]
lemma compactConvergenceCLMCongrSL_symm_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (φ : F →SL_c[σ₂₃] G) (e : E) :
    (compactConvergenceCLMCongrSL e₁₂ e₄₃).symm φ e = e₄₃.symm (φ (e₁₂ e)) :=
  rfl

end Semilinear

section Linear

variable {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*} {H : Type*}
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G] [Module 𝕜 H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

/-- A pair of continuous linear equivalences generates a continuous linear equivalence between
the spaces of continuous linear maps. This version is for the type alias
`CompactConvergenceCLM`. -/
def compactConvergenceCLMCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) :
    (E →L_c[𝕜] H) ≃L[𝕜] (F →L_c[𝕜] G) :=
  e₁.compactConvergenceCLMCongrSL e₂

@[simp]
lemma compactConvergenceCLMCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
    (φ : E →L_c[𝕜] H) (f : F) :
    compactConvergenceCLMCongr e₁ e₂ φ f = e₂ (φ (e₁.symm f)) :=
  rfl

@[simp]
lemma compactConvergenceCLMCongr_symm_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
    (φ : F →L_c[𝕜] G) (e : E) :
    (compactConvergenceCLMCongr e₁ e₂).symm φ e = e₂.symm (φ (e₁ e)) :=
  rfl

end Linear

section Pi

open scoped CompactConvergenceCLM

variable [TopologicalSpace E] {ι : Type*} (F : ι → Type*)
  [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜₁ (F i)] [∀ i, TopologicalSpace (F i)]
  [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousConstSMul 𝕜₁ (F i)]

variable (𝕜₁ E) in
/-- `ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →L_c[𝕜] F i` and `E →L_c[𝕜] Π i, F i`. -/
def CompactConvergenceCLM.piEquivL :
    (Π i, E →L_c[𝕜₁] F i) ≃L[𝕜₁] (E →L_c[𝕜₁] Π i, F i) where
  toFun F := ContinuousLinearMap.pi F
  invFun f i := (ContinuousLinearMap.proj i).comp f
  __ := UniformConvergenceCLM.piEquivL _ _ _

@[simp]
lemma CompactConvergenceCLM.piEquivL_apply
    (T : Π i, E →L_c[𝕜₁] F i) (e : E) (i : ι) :
    piEquivL 𝕜₁ E F T e i = T i e :=
  rfl

@[simp]
lemma CompactConvergenceCLM.piEquivL_symm_apply
    (T : E →L_c[𝕜₁] Π i, F i) (e : E) (i : ι) :
    (piEquivL 𝕜₁ E F).symm T i e = T e i :=
  rfl

end Pi

end ContinuousLinearEquiv

end CompactSets
