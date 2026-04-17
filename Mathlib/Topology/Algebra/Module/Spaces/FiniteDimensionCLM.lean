/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM

/-!
# Topologies on `E →L[𝕜] F` when `E` is finite dimensional

When `E` is a finite dimensional T2 vector space over a complete nontrivially normed field,
then the topology of bounded convergence on `E →L[𝕜] F` coincides with the toplogy of
pointwise convergence.

In fact, the same applies to `E →L_c[𝕜] F` (with the topology of compact convergence) and,
more generally, to `E →Lᵤ[𝕜, 𝔖] F` for any covering family `𝔖 : Set (Set E)` of bounded subsets
of `E`.

-/

@[expose] public section

open Module ContinuousLinearMap LinearMap Topology Bornology

namespace UniformConvergenceCLM

variable {ι 𝕜 R E F V Vᵤ : Type*} [Semiring R] [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup V] [AddCommGroup Vᵤ]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 V] [Module 𝕜 Vᵤ]
  [Module R V] [SMulCommClass 𝕜 R V]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [UniformSpace Vᵤ] [IsUniformAddGroup Vᵤ]
  [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 V] [ContinuousSMul 𝕜 Vᵤ]
  [ContinuousConstSMul R V]
  [CompleteSpace 𝕜] [T2Space E] -- hypotheses for automatic continuity in finite dimension
  {𝔖 : Set (Set E)} {𝔗 : Set (Set F)}

open Basis in
theorem continuous_constrL [Finite ι] (b : Basis ι 𝕜 E)
    (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) :
    Continuous (Y := E →Lᵤ[𝕜, 𝔖] V) b.constrL := by
  rcases nonempty_fintype ι
  letI Φ : (ι → V) →ₗ[𝕜] (E →L[𝕜] V) := ⟨⟨b.constrL, by simp [constrL]⟩, by simp [constrL]⟩
  -- This gets a bit painful because of the type alias
  suffices Continuous fun (p : _ × _) ↦ Φ p.1 p.2 from
    UniformConvergenceCLM.continuous_of_continuous_uncurry h𝔖 Φ this
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, b.constrL_apply, equivFun_apply, ← equivFunL_apply]
  fun_prop

variable (R) in
/-- `Basis.constrL` upgraded to a `ContinuousLinearEquiv`, between `ι → V`
and `E →Lᵤ[𝕜, 𝔖] V`. -/
protected noncomputable def constrCLE [Finite ι] (b : Basis ι 𝕜 E)
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ) :
    (ι → V) ≃L[R] (E →Lᵤ[𝕜, 𝔖] V) :=
  have := UniformConvergenceCLM.continuousEvalConst (.id 𝕜) V _ h𝔖₂
  { toFun := b.constrL
    invFun f i := f (b i)
    map_add' f g := toLinearMap_injective (map_add (b.constr R) f g)
    map_smul' c f := toLinearMap_injective (map_smul (b.constr R) c f)
    left_inv := b.constr R |>.left_inv
    right_inv _ := toLinearMap_injective (b.constr R |>.right_inv _)
    continuous_toFun := UniformConvergenceCLM.continuous_constrL b h𝔖₁
    continuous_invFun := continuous_pi fun i ↦ continuous_eval_const (b i) }

/-- If `E` is finite dimensional, the topology of `𝔖`-convergence on `E →Lᵤ[𝕜, 𝔖] F`
identifies with the product topology. -/
theorem isEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ) :
    IsEmbedding ((↑) : (E →Lᵤ[𝕜, 𝔖] V) → (E → V)) := by
  have := UniformConvergenceCLM.continuousEvalConst (.id 𝕜) V _ h𝔖₂
  let b : Basis _ 𝕜 E := Free.chooseBasis 𝕜 E
  have : Continuous (fun (f : E → V) i ↦ f (b i)) := continuous_pi fun i ↦ continuous_apply _
  exact .of_comp continuous_coeFun this
    (UniformConvergenceCLM.constrCLE 𝕜 b h𝔖₁ h𝔖₂).symm.toHomeomorph.isEmbedding

theorem isUniformEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ) :
    IsUniformEmbedding ((↑) : (E →Lᵤ[𝕜, 𝔖] Vᵤ) → (E → Vᵤ)) :=
  let Φ : (E →Lᵤ[𝕜, 𝔖] Vᵤ) →ₗ[𝕜] (E → Vᵤ) := LinearMap.ltoFun _ _ _ _ ∘ₗ coeLM _
  AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := Φ)
    (isEmbedding_coeFn_of_finiteDimensional h𝔖₁ h𝔖₂)

end UniformConvergenceCLM

section ContinuousLinearMap

variable {ι 𝕜 R E F V Vᵤ : Type*} [Semiring R] [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup V] [AddCommGroup Vᵤ]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 V] [Module 𝕜 Vᵤ]
  [Module R V] [SMulCommClass 𝕜 R V]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [UniformSpace Vᵤ] [IsUniformAddGroup Vᵤ]
  [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 V] [ContinuousSMul 𝕜 Vᵤ]
  [ContinuousConstSMul R V]
  [CompleteSpace 𝕜] [T2Space E] -- hypotheses for automatic continuity in finite dimension

theorem Module.Basis.continuous_constrL [Finite ι] (b : Basis ι 𝕜 E) :
    Continuous (b.constrL : (ι → V) → (E →L[𝕜] V)) :=
  UniformConvergenceCLM.continuous_constrL b (fun _ ↦ id)

variable (R) in
/-- `Basis.constrL` upgraded to a `ContinuousLinearEquiv`, between `ι → V`
and `E →L[𝕜, 𝔖] V`. -/
@[simps! apply symm_apply]
protected noncomputable def Module.Basis.constrCLE [Finite ι] (b : Basis ι 𝕜 E) :
    (ι → V) ≃L[R] (E →L[𝕜] V) :=
  UniformConvergenceCLM.constrCLE R b (fun _ ↦ id) sUnion_isVonNBounded_eq_univ

/-- If `E` is finite dimensional, the topology of bounded convergence on `E →L[𝕜] F`
identifies with the product topology. -/
theorem ContinuousLinearMap.isEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E] :
    IsEmbedding ((↑) : (E →L[𝕜] V) → (E → V)) :=
  UniformConvergenceCLM.isEmbedding_coeFn_of_finiteDimensional (fun _ ↦ id)
    sUnion_isVonNBounded_eq_univ

theorem ContinuousLinearMap.isUniformEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E] :
    IsUniformEmbedding ((↑) : (E →L[𝕜] Vᵤ) → (E → Vᵤ)) :=
  UniformConvergenceCLM.isUniformEmbedding_coeFn_of_finiteDimensional (fun _ ↦ id)
    sUnion_isVonNBounded_eq_univ

end ContinuousLinearMap

namespace PointwiseConvergenceCLM

open scoped PointwiseConvergenceCLM
open Set

variable {ι 𝕜 R E F V Vᵤ : Type*} [Semiring R] [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup V] [AddCommGroup Vᵤ]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 V] [Module 𝕜 Vᵤ]
  [Module R V] [SMulCommClass 𝕜 R V]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [UniformSpace Vᵤ] [IsUniformAddGroup Vᵤ]
  [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 V] [ContinuousSMul 𝕜 Vᵤ]
  [ContinuousConstSMul R V]
  [CompleteSpace 𝕜] [T2Space E] -- hypotheses for automatic continuity in finite dimension

theorem continuous_constrL [Finite ι] (b : Basis ι 𝕜 E) :
    Continuous (Y := E →Lₚₜ[𝕜] V) b.constrL :=
  UniformConvergenceCLM.continuous_constrL b (fun _ ↦ Finite.isVonNBounded)

variable (R) in
/-- `Basis.constrL` upgraded to a `ContinuousLinearEquiv`, between `ι → V`
and `E →Lₚₜ[𝕜, 𝔖] V`. -/
protected noncomputable def constrCLE [Finite ι] (b : Basis ι 𝕜 E) :
    (ι → V) ≃L[R] (E →Lₚₜ[𝕜] V) :=
  UniformConvergenceCLM.constrCLE R b (fun _ ↦ Finite.isVonNBounded) sUnion_finite_eq_univ

end PointwiseConvergenceCLM

namespace CompactConvergenceCLM

open scoped CompactConvergenceCLM
open Set

variable {ι 𝕜 R E F V Vᵤ : Type*} [Semiring R] [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup V] [AddCommGroup Vᵤ]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 V] [Module 𝕜 Vᵤ]
  [Module R V] [SMulCommClass 𝕜 R V]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [UniformSpace Vᵤ] [IsUniformAddGroup Vᵤ]
  [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 V] [ContinuousSMul 𝕜 Vᵤ]
  [ContinuousConstSMul R V]
  [CompleteSpace 𝕜] [T2Space E] -- hypotheses for automatic continuity in finite dimension

theorem continuous_constrL [Finite ι] (b : Basis ι 𝕜 E) :
    Continuous (Y := E →L_c[𝕜] V) b.constrL :=
  UniformConvergenceCLM.continuous_constrL b
    (fun _ hS ↦ hS.isVonNBounded 𝕜)

variable (R) in
/-- `Basis.constrL` upgraded to a `ContinuousLinearEquiv`, between `ι → V`
and `E →L_c[𝕜] V`. -/
protected noncomputable def constrCLE [Finite ι] (b : Basis ι 𝕜 E) :
    (ι → V) ≃L[R] (E →L_c[𝕜] V) :=
  UniformConvergenceCLM.constrCLE R b (fun _ hS ↦ hS.isVonNBounded 𝕜) sUnion_isCompact_eq_univ

/-- If `E` is finite dimensional, the topology of compact convergence on `E →L_c[𝕜] F`
identifies with the product topology. -/
theorem isEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E] :
    IsEmbedding ((↑) : (E →L_c[𝕜] V) → (E → V)) :=
  UniformConvergenceCLM.isEmbedding_coeFn_of_finiteDimensional (fun _ hS ↦ hS.isVonNBounded 𝕜)
    sUnion_isCompact_eq_univ

theorem isUniformEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E] :
    IsUniformEmbedding ((↑) : (E →L_c[𝕜] Vᵤ) → (E → Vᵤ)) :=
  UniformConvergenceCLM.isUniformEmbedding_coeFn_of_finiteDimensional
    (fun _ hS ↦ hS.isVonNBounded 𝕜) sUnion_isCompact_eq_univ

end CompactConvergenceCLM
