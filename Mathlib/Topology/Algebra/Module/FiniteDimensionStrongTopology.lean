/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Topology on `E →L[𝕜] F` when `E` is finite dimensional

When `E` is a finite dimensional T2 vector space over a complete nontrivially normed field,
then the topology of bounded convergence on `E →L[𝕜] F` coincides with the toplogy of
pointwise convergence.

TODO: Generalize this to `UniformConvergenceCLM`.
-/

@[expose] public section

open Module ContinuousLinearMap LinearMap Topology Bornology

namespace UniformConvergenceCLM

variable {ι 𝕜 R E F V Vᵤ : Type*} [Semiring R] [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup V] [AddCommGroup Vᵤ]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 V] [Module 𝕜 Vᵤ]
  [Module R V] [SMulCommClass 𝕜 R V]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [UniformSpace Vᵤ] [IsUniformAddGroup Vᵤ]
  [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [ContinuousSMul 𝕜 V] [ContinuousSMul 𝕜 Vᵤ]
  [ContinuousConstSMul R V]
  [CompleteSpace 𝕜] [T2Space E] -- hypotheses for automatic continuity in finite dimension
  {𝔖 : Set (Set E)} {𝔗 : Set (Set F)}

open Basis in
theorem continuous_constrL [Finite ι] (b : Basis ι 𝕜 E)
    (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) :
    -- Without `id`, Lean sees through the type alias too much and infers the
    -- topology of `E →L[𝕜] V`...
    Continuous
      (id (b.constrL) : (ι → V) → (UniformConvergenceCLM (.id 𝕜) V 𝔖)) := by
  rcases nonempty_fintype ι
  letI Φ : (ι → V) →ₗ[𝕜] (E →L[𝕜] V) := ⟨⟨b.constrL, by simp [constrL]⟩, by simp [constrL]⟩
  -- This gets a bit painful because of the type alias
  suffices Continuous fun (p : _ × _) ↦ Φ p.1 p.2 by
    exact UniformConvergenceCLM.continuous_of_continuous_uncurry h𝔖 Φ this
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, b.constrL_apply, equivFun_apply, ← equivFunL_apply]
  fun_prop

variable (R) in
/-- `Basis.constrL` upgraded to a `ContinuousLinearEquiv`, between `ι → V`
and `E →L[𝕜] V` with the topology of `𝔖`-convergence. -/
@[simps]
protected noncomputable def constrCLE [Finite ι] (b : Basis ι 𝕜 E)
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ) :
    (ι → V) ≃L[R] (UniformConvergenceCLM (.id 𝕜) V 𝔖) :=
  have := UniformConvergenceCLM.continuousEvalConst (.id 𝕜) V _ h𝔖₂
  { toFun := b.constrL
    invFun f i := f (b i)
    map_add' f g := toLinearMap_injective (map_add (b.constr R) f g)
    map_smul' c f := toLinearMap_injective (map_smul (b.constr R) c f)
    left_inv := b.constr R |>.left_inv
    right_inv _ := toLinearMap_injective (b.constr R |>.right_inv _)
    continuous_toFun := UniformConvergenceCLM.continuous_constrL b h𝔖₁
    continuous_invFun := continuous_pi fun i ↦ continuous_eval_const (b i) }

/-- If `E` is finite dimensional, the topology of `𝔖`-convergence on `E →L[𝕜] F`
identifies with the product topology. -/
theorem isEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ) :
    IsEmbedding ((↑) : UniformConvergenceCLM (.id 𝕜) V 𝔖 → (E → V)) := by
  have := UniformConvergenceCLM.continuousEvalConst (.id 𝕜) V _ h𝔖₂
  let b : Basis _ 𝕜 E := Free.chooseBasis 𝕜 E
  have : Continuous (fun (f : E → V) i ↦ f (b i)) := continuous_pi fun i ↦ continuous_apply _
  exact .of_comp continuous_coeFun this
    (UniformConvergenceCLM.constrCLE 𝕜 b h𝔖₁ h𝔖₂).symm.toHomeomorph.isEmbedding

/-- If `E` is finite dimensional, the topology of `𝔖`-convergence on `E →L[𝕜] F`
identifies with the product topology. -/
theorem isUniformEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ) :
    IsUniformEmbedding ((↑) : UniformConvergenceCLM (.id 𝕜) Vᵤ 𝔖 → (E → Vᵤ)) :=
  let Φ : UniformConvergenceCLM (.id 𝕜) Vᵤ 𝔖 →ₗ[𝕜] (E → Vᵤ) := LinearMap.ltoFun _ _ _ _ ∘ₗ coeLM _
  AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := Φ)
    (isEmbedding_coeFn_of_finiteDimensional h𝔖₁ h𝔖₂)

/-- If `E` is finite dimensional, the topology of `𝔖`-convergence on `E →L[𝕜] F`
identifies with the product topology. -/
def flipOfFiniteDimensionalV2 [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ)
    (h𝔗₁ : ∀ t ∈ 𝔗, IsVonNBounded 𝕜 t) :
    (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔗) 𝔖) ≃L[𝕜]
      (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔖) 𝔗) :=
  letI step : (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔗) 𝔖) ≃ₗ[𝕜]
      (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔖) 𝔗) :=
    { toFun L := sorry
      invFun L :=
        have : ContinuousSMul 𝕜 (UniformConvergenceCLM (RingHom.id 𝕜) V 𝔗) :=
          continuousSMul _ _ _ h𝔗₁
        suffices E →ₗ[𝕜] (UniformConvergenceCLM (RingHom.id 𝕜) V 𝔗) from this.toContinuousLinearMap
        sorry
      map_add' := sorry
      map_smul' := sorry
      left_inv := sorry
      right_inv := sorry }
  sorry

/-- If `E` is finite dimensional, the topology of `𝔖`-convergence on `E →L[𝕜] F`
identifies with the product topology. -/
def flipOfBasis [Fintype ι] (b : Basis ι 𝕜 E)
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ)
    (h𝔗₁ : ∀ t ∈ 𝔗, IsVonNBounded 𝕜 t) :
    (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔗) 𝔖) ≃L[𝕜]
      (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔖) 𝔗) :=
  let Φ₁ :

/-- If `E` is finite dimensional, the topology of `𝔖`-convergence on `E →L[𝕜] F`
identifies with the product topology. -/
def flipOfFiniteDimensional [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ) :
    (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔗) 𝔖) →L[𝕜]
      (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔖) 𝔗) where
  toFun L :=
    { toFun f := LinearMap.toContinuousLinearMap ⟨⟨(L · f), fun _ _ ↦ by simp⟩, fun _ _ ↦ by simp⟩
      map_add' _ _ := by ext e; exact map_add (L e) _ _
      map_smul' _ _ := by ext e; exact map_smul (L e) _ _
      cont := by
        rw [isEmbedding_coeFn_of_finiteDimensional h𝔖₁ h𝔖₂ |>.continuous_iff, continuous_pi_iff]
        intro e
        exact (L e).continuous }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    let : UniformSpace V := IsTopologicalAddGroup.rightUniformSpace V
    have : IsUniformAddGroup V := isUniformAddGroup_of_addCommGroup
    have : ContinuousEvalConst (UniformConvergenceCLM (.id 𝕜) V 𝔖) E V :=
      continuousEvalConst _ _ _ h𝔖₂
    have : ContinuousEvalConst
        (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔗) 𝔖) E
        (UniformConvergenceCLM (.id 𝕜) V 𝔗) :=
      continuousEvalConst _ _ _ h𝔖₂
    let Φ : UniformConvergenceCLM (.id 𝕜) V 𝔖 →L[𝕜] E → V :=
      ⟨⟨⟨(↑), fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩, continuous_coeFun⟩
    have : IsUniformEmbedding Φ :=
      isUniformEmbedding_coeFn_of_finiteDimensional h𝔖₁ h𝔖₂
    have := isUniformEmbedding_postcomp (.id 𝕜) Φ this 𝔗
    have := isUniformEmbedding_coeFn (.id 𝕜) _ 𝔗 |>.comp this
    have := UniformOnFun.uniformEquivPiComm 𝔗 (fun e : E ↦ V) |>.isUniformEmbedding.comp this
    rw [this.isEmbedding.continuous_iff, continuous_pi_iff]
    intro e
    exact isEmbedding_coeFn (.id 𝕜) V 𝔗 |>.continuous.comp (continuous_eval_const e)

/-- If `E` is finite dimensional, the topology of `𝔖`-convergence on `E →L[𝕜] F`
identifies with the product topology. -/
def flipOfFiniteDimensionalCLE
    [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) (h𝔖₂ : ⋃₀ 𝔖 = .univ)
    (h𝔗₁ : ∀ t ∈ 𝔗, IsVonNBounded 𝕜 t) (h𝔗₂ : ⋃₀ 𝔗 = .univ) :
    (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔗) 𝔖) ≃L[𝕜]
      (UniformConvergenceCLM (.id 𝕜) (UniformConvergenceCLM (.id 𝕜) V 𝔖) 𝔗) :=
  .equivOfInverse (flipOfFiniteDimensional h𝔖₁ h𝔖₂) (flipOfFiniteDimensional h𝔗₁ h𝔗₂) _ _

end UniformConvergenceCLM

section ContinuousLinearMap

variable {ι 𝕜 R E F Fᵤ : Type*} [Semiring R] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup Fᵤ] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 Fᵤ]
  [Module R F] [SMulCommClass 𝕜 R F] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [UniformSpace Fᵤ] [IsUniformAddGroup Fᵤ]
  [T2Space E] [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [ContinuousSMul 𝕜 Fᵤ]
  [ContinuousConstSMul R F]

theorem Module.Basis.continuous_constrL [Finite ι] (b : Basis ι 𝕜 E) :
    Continuous (b.constrL : (ι → F) → (E →L[𝕜] F)) :=
  UniformConvergenceCLM.continuous_constrL b (fun _ ↦ id)

#lint

variable (R) in
/-- `Basis.constrL` upgraded to a `ContinuousLinearEquiv`, where `E →L[𝕜] F` is endowed with
the topology of bounded convergence. -/
@[simps! apply symm_apply]
protected noncomputable def Module.Basis.constrCLE [Finite ι] (b : Basis ι 𝕜 E) :
    (ι → F) ≃L[R] (E →L[𝕜] F) :=
  UniformConvergenceCLM.constrCLE R b (fun _ ↦ id) (sUnion_isVonNBounded_eq_univ)

/-- If `E` is finite dimensional, the topology of bounded convergence on `E →L[𝕜] F`
identifies with the product topology. -/
theorem ContinuousLinearMap.isEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E] :
    IsEmbedding ((↑) : (E →L[𝕜] F) → (E → F)) := by
  let b : Basis _ 𝕜 E := Free.chooseBasis 𝕜 E
  have : Continuous (fun (f : E → F) i ↦ f (b i)) := continuous_pi fun i ↦ continuous_apply _
  exact .of_comp continuous_coeFun this (b.constrCLE 𝕜).symm.toHomeomorph.isEmbedding

/-- If `E` is finite dimensional, the topology of bounded convergence on `E →L[𝕜] F`
identifies with the product topology. -/
theorem ContinuousLinearMap.isUniformEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E] :
    IsUniformEmbedding ((↑) : (E →L[𝕜] Fᵤ) → (E → Fᵤ)) :=
  let Φ : (E →L[𝕜] Fᵤ) →ₗ[𝕜] (E → Fᵤ) := LinearMap.ltoFun _ _ _ _ ∘ₗ coeLM _
  AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := Φ) isEmbedding_coeFn_of_finiteDimensional

end ContinuousLinearMap
