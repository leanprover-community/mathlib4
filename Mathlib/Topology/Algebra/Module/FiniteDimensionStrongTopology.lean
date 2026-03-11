/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Topology on `E →L[𝕜] F` when `E` is finite dimensional

When `E` is a finite dimensional T2 vector space over a complete nontrivially normed field,
then the topology of bounded convergence on `E →L[𝕜] F` coincides with the toplogy of
pointwise convergence.
-/

open Module ContinuousLinearMap LinearMap Topology

variable {ι 𝕜 R E F : Type*} [Semiring R] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] [Module R F] [SMulCommClass 𝕜 R F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [T2Space E] [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [ContinuousConstSMul R F]

theorem Module.Basis.continuous_constrL [Finite ι] (b : Basis ι 𝕜 E) :
    Continuous (b.constrL : (ι → F) → (E →L[𝕜] F)) := by
  rcases nonempty_fintype ι
  let coord (i : ι) : E →L[𝕜] 𝕜 := (.proj i ∘L (b.equivFunL : E →L[𝕜] (ι → 𝕜)))
  let Φ (i : ι) : F →L[𝕜] E →L[𝕜] F :=
    precomp F (coord i) ∘L (toSpanSingletonCLE : F ≃L[𝕜] 𝕜 →L[𝕜] F)
  have key : b.constrL = ∑ i : ι, Φ i ∘L (.proj i) := by
    ext
    simp [Φ, coord]
  exact key ▸ map_continuous _

variable (R) in
protected noncomputable def Module.Basis.constrLCLE [Finite ι] (b : Basis ι 𝕜 E) :
    (ι → F) ≃L[R] (E →L[𝕜] F) :=
  { toFun := b.constrL
    invFun f i := f (b i)
    map_add' f g := toLinearMap_injective (map_add (b.constr R) f g)
    map_smul' c f := toLinearMap_injective (map_smul (b.constr R) c f)
    left_inv := b.constr R |>.left_inv
    right_inv _ := toLinearMap_injective (b.constr R |>.right_inv _)
    continuous_toFun := b.continuous_constrL
    continuous_invFun := continuous_pi fun i ↦ continuous_eval_const (b i) }

theorem ContinuousLinearMap.isEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E] :
    IsEmbedding ((↑) : (E →L[𝕜] F) → (E → F)) := by
  let b : Basis _ 𝕜 E := Free.chooseBasis 𝕜 E
  have : Continuous (fun (f : E → F) i ↦ f (b i)) := continuous_pi fun i ↦ continuous_apply _
  exact .of_comp continuous_coeFun this (b.constrLCLE 𝕜).symm.toHomeomorph.isEmbedding
