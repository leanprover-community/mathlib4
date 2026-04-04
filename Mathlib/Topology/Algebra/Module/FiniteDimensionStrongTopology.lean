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
and `E →L[𝕜] V` with the topology of `𝔖`-convergence. -/
@[simps]
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

/-- If `E` is finite dimensional, the topology of `𝔖`-convergence on `E →L[𝕜] F`
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

/-- If `E` is finite dimensional, the topology of `𝔖`-convergence on `E →L[𝕜] F`
identifies with the product topology. -/
theorem isUniformEmbedding_coeFn_of_finiteDimensional
    [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ) :
    IsUniformEmbedding ((↑) : (E →Lᵤ[𝕜, 𝔖] Vᵤ) → (E → Vᵤ)) :=
  let Φ : (E →Lᵤ[𝕜, 𝔖] Vᵤ) →ₗ[𝕜] (E → Vᵤ) := LinearMap.ltoFun _ _ _ _ ∘ₗ coeLM _
  AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := Φ)
    (isEmbedding_coeFn_of_finiteDimensional h𝔖₁ h𝔖₂)

/-- If `E` is finite dimensional, the topology of `𝔖`-convergence on `E →L[𝕜] F`
identifies with the product topology. -/
noncomputable def flipOfBasis [Fintype ι] (b : Basis ι 𝕜 E)
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ)
    (h𝔗₁ : ∀ t ∈ 𝔗, IsVonNBounded 𝕜 t) :
    (E →Lᵤ[𝕜, 𝔖] F →Lᵤ[𝕜, 𝔗] V) ≃L[𝕜] (F →Lᵤ[𝕜, 𝔗] E →Lᵤ[𝕜, 𝔖] V) :=
  have : ContinuousSMul 𝕜 (F →Lᵤ[𝕜, 𝔗] V) := continuousSMul _ _ _ h𝔗₁
  let A₀ : (ι → V) ≃L[𝕜] (E →Lᵤ[𝕜, 𝔖] V) :=
    UniformConvergenceCLM.constrCLE 𝕜 b h𝔖₁ h𝔖₂
  let A : (F →Lᵤ[𝕜, 𝔗] ι → V) ≃L[𝕜] (F →Lᵤ[𝕜, 𝔗] E →Lᵤ[𝕜, 𝔖] V) :=
    (ContinuousLinearEquiv.refl 𝕜 F).uniformConvergenceCLMCongr A₀ _ _ (fun _ ↦ Iff.rfl)
  let B : (ι → F →Lᵤ[𝕜, 𝔗] V) ≃L[𝕜] (E →Lᵤ[𝕜, 𝔖] F →Lᵤ[𝕜, 𝔗] V) :=
    UniformConvergenceCLM.constrCLE 𝕜 b h𝔖₁ h𝔖₂
  let Φ : (ι → F →Lᵤ[𝕜, 𝔗] V) ≃L[𝕜] (F →Lᵤ[𝕜, 𝔗] ι → V) :=
    UniformConvergenceCLM.piEquivL 𝕜 _ _
  B.symm.trans <| Φ.trans A

lemma flipOfBasis_apply [Fintype ι] (b : Basis ι 𝕜 E)
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ)
    (h𝔗₁ : ∀ t ∈ 𝔗, IsVonNBounded 𝕜 t)
    (T : E →Lᵤ[𝕜, 𝔖] F →Lᵤ[𝕜, 𝔗] V) (e : E) (f : F) :
    flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁ T f e = T e f := by
  let Tₗ : E →ₗ[𝕜] (F →ₗ[𝕜] V) := ContinuousLinearMap.coeLM 𝕜 ∘ₗ T.toLinearMap
  let Sₗ := (b.constr 𝕜).toLinearMap ∘ₗ LinearMap.pi ((b.constr 𝕜).symm.toLinearMap Tₗ)
  suffices Sₗ = Tₗ.flip from congr($this f e)
  ext f : 1
  refine b.ext fun i ↦ ?_
  simp_rw [Sₗ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Basis.constr_basis,
    LinearMap.pi_apply, Basis.constr_symm_apply, LinearMap.flip_apply]

lemma flipOfBasis_symm_apply [Fintype ι] (b : Basis ι 𝕜 E)
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ)
    (h𝔗₁ : ∀ t ∈ 𝔗, IsVonNBounded 𝕜 t)
    (S : F →Lᵤ[𝕜, 𝔗] E →Lᵤ[𝕜, 𝔖] V) (e : E) (f : F) :
    (flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁).symm S e f = S f e := by
  revert S
  rw [(flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁).surjective.forall]
  intro T
  simp [flipOfBasis_apply]

noncomputable def flipOfFiniteDimensional [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ)
    (h𝔗₁ : ∀ t ∈ 𝔗, IsVonNBounded 𝕜 t) :
    (E →Lᵤ[𝕜, 𝔖] F →Lᵤ[𝕜, 𝔗] V) ≃L[𝕜] (F →Lᵤ[𝕜, 𝔗] E →Lᵤ[𝕜, 𝔖] V) :=
  let b : Basis _ 𝕜 E := Free.chooseBasis 𝕜 E
  let φ (T : E →Lᵤ[𝕜, 𝔖] F →Lᵤ[𝕜, 𝔗] V) : F →Lᵤ[𝕜, 𝔗] E →Lᵤ[𝕜, 𝔖] V :=
    let φ₀ (T : E →Lᵤ[𝕜, 𝔖] F →Lᵤ[𝕜, 𝔗] V) (f : F) : E →Lᵤ[𝕜, 𝔖] V :=
      flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁ T f |>.copy (fun e ↦ T e f)
        (by ext e; exact (flipOfBasis_apply b h𝔖₁ h𝔖₂ h𝔗₁ T e f).symm)
    have φ₀_eq (T) : φ₀ T = flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁ T :=
      funext fun f ↦ ContinuousLinearMap.copy_eq _ _ _
    flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁ T |>.copy (fun f ↦ φ₀ T f) (φ₀_eq T)
  have φ_eq (T) : φ T = flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁ T :=
    ContinuousLinearMap.copy_eq _ _ _
  let ψ (S : F →Lᵤ[𝕜, 𝔗] E →Lᵤ[𝕜, 𝔖] V) : E →Lᵤ[𝕜, 𝔖] F →Lᵤ[𝕜, 𝔗] V :=
    let ψ₀ (S : F →Lᵤ[𝕜, 𝔗] E →Lᵤ[𝕜, 𝔖] V) (e : E) : F →Lᵤ[𝕜, 𝔗] V :=
      (flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁).symm S e |>.copy (fun f ↦ S f e)
        (by ext f; exact (flipOfBasis_symm_apply b h𝔖₁ h𝔖₂ h𝔗₁ S e f).symm)
    have ψ₀_eq (S) : ψ₀ S = (flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁).symm S :=
      funext fun f ↦ ContinuousLinearMap.copy_eq _ _ _
    (flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁).symm S |>.copy (fun e ↦ ψ₀ S e) (ψ₀_eq S)
  have ψ_eq (S) : ψ S = (flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁).symm S :=
    ContinuousLinearMap.copy_eq _ _ _
  { toFun := φ
    invFun := ψ
    map_add' _ _ := by simp [φ_eq]
    map_smul' _ _ := by simp [φ_eq]
    left_inv _ := by simp [φ_eq, ψ_eq]
    right_inv _ := by simp [φ_eq, ψ_eq]
    continuous_toFun :=
      (flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁).continuous_toFun.congr fun T ↦ .symm <| φ_eq T
    continuous_invFun :=
      (flipOfBasis b h𝔖₁ h𝔖₂ h𝔗₁).continuous_invFun.congr fun T ↦ .symm <| ψ_eq T }

@[simp]
lemma flipOfFiniteDimensional_apply [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ)
    (h𝔗₁ : ∀ t ∈ 𝔗, IsVonNBounded 𝕜 t)
    (T : E →Lᵤ[𝕜, 𝔖] F →Lᵤ[𝕜, 𝔗] V) (e : E) (f : F) :
    flipOfFiniteDimensional h𝔖₁ h𝔖₂ h𝔗₁ T f e = T e f :=
  rfl

@[simp]
lemma flipOfFiniteDimensional_symm_apply [FiniteDimensional 𝕜 E]
    (h𝔖₁ : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖₂ : ⋃₀ 𝔖 = .univ)
    (h𝔗₁ : ∀ t ∈ 𝔗, IsVonNBounded 𝕜 t)
    (S : F →Lᵤ[𝕜, 𝔗] E →Lᵤ[𝕜, 𝔖] V) (e : E) (f : F) :
    (flipOfFiniteDimensional h𝔖₁ h𝔖₂ h𝔗₁).symm S e f = S f e :=
  rfl

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
