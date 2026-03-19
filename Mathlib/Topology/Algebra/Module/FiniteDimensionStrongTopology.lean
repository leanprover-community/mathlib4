/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Module.StrongTopology
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Topology on `E →L[𝕜] F` when `E` is finite dimensional

When `E` is a finite dimensional T2 vector space over a complete nontrivially normed field,
then the topology of bounded convergence on `E →L[𝕜] F` coincides with the toplogy of
pointwise convergence.

TODO: Generalize this to `UniformConvergenceCLM`.
-/

@[expose] public section

open Module ContinuousLinearMap LinearMap Topology

variable {ι 𝕜 R E F : Type*} [Semiring R] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] [Module R F] [SMulCommClass 𝕜 R F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [T2Space E] [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [ContinuousConstSMul R F]

theorem Module.Basis.continuous_constrL [Finite ι] (b : Basis ι 𝕜 E) :
    Continuous (b.constrL : (ι → F) → (E →L[𝕜] F)) := by
  rcases nonempty_fintype ι
  letI Φ : (ι → F) →ₗ[𝕜] (E →L[𝕜] F) := ⟨⟨b.constrL, by simp [constrL]⟩, by simp [constrL]⟩
  apply continuous_of_continuous_uncurry Φ
  simp only [LinearMap.coe_mk, AddHom.coe_mk, b.constrL_apply, equivFun_apply, Φ, ← equivFunL_apply]
  fun_prop

variable (R) in
/-- `Basis.constrL` upgraded to a `ContinuousLinearEquiv`, where `E →L[𝕜] F` is endowed with
the topology of bounded convergence. -/
@[simps]
protected noncomputable def Module.Basis.constrCLE [Finite ι] (b : Basis ι 𝕜 E) :
    (ι → F) ≃L[R] (E →L[𝕜] F) :=
  { toFun := b.constrL
    invFun f i := f (b i)
    map_add' f g := toLinearMap_injective (map_add (b.constr R) f g)
    map_smul' c f := toLinearMap_injective (map_smul (b.constr R) c f)
    left_inv := b.constr R |>.left_inv
    right_inv _ := toLinearMap_injective (b.constr R |>.right_inv _)
    continuous_toFun := b.continuous_constrL
    continuous_invFun := continuous_pi fun i ↦ continuous_eval_const (b i) }

/-- If `E` is finite dimensional, the topology of bounded convergence on `E →L[𝕜] F`
identifies with the product topology. -/
theorem ContinuousLinearMap.isEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E] :
    IsEmbedding ((↑) : (E →L[𝕜] F) → (E → F)) := by
  let b : Basis _ 𝕜 E := Free.chooseBasis 𝕜 E
  have : Continuous (fun (f : E → F) i ↦ f (b i)) := continuous_pi fun i ↦ continuous_apply _
  exact .of_comp continuous_coeFun this (b.constrCLE 𝕜).symm.toHomeomorph.isEmbedding
