/-
Copyright (c) 2026 Michał Pacholski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Pacholski
-/
module

public import Mathlib.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm
public import Mathlib.Topology.Algebra.GroupCompletion
/-!
# Nuclear operators

This file defines the canonical continuous linear map from the projective tensor product
`Y ⊗[𝕜] StrongDual 𝕜 X` to the space of continuous linear maps `X →L[𝕜] Y`.
It then uses the topological completion of this tensor product to define the space of
nuclear operators between normed spaces.

## Main definitions

* `TensorProduct.toContinuousLinearMap`: The canonical continuous linear map
  `Y ⊗[𝕜] StrongDual 𝕜 X →L[𝕜] (X →L[𝕜] Y)`.
* `ContinuousLinearMap.nuclearOperators`: The set of nuclear operators from `X` to `Y`,
  defined as the range of `toContinuousLinearMap` extended to the topological completion
  of the projective tensor product.

## References

* H. H. Schaefer, M. P. Wolff, *Topological Vector Spaces*
-/

@[expose] public section

open UniformSpace TensorProduct ContinuousLinearMap

universe u v

variable {𝕜 E E' F F' : Type*}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [CompleteSpace F']

namespace TensorProduct

/-- The canonical continuous linear map from the projective tensor product of `Y` and the
strong dual of `X` to the space of continuous linear maps from `X` to `Y`. -/
noncomputable def toContinuousLinearMap : F ⊗[𝕜] StrongDual 𝕜 E →L[𝕜] (E →L[𝕜] F) :=
  liftEquiv 𝕜 F (StrongDual 𝕜 E) (E →L[𝕜] F) (smulRightL 𝕜 E F).flip

end TensorProduct

namespace ContinuousLinearMap

variable (𝕜 E F) in
/-- The space of nuclear operators from `X` to `Y` between Banach spaces, defined as the
range of the canonical map `toContinuousLinearMap` extended to the completion of the
projective tensor product. -/
def nuclearOperators : Set (E →L[𝕜] F) :=
  Set.range (Completion.extension (toContinuousLinearMap : F ⊗[𝕜] StrongDual 𝕜 E →L[𝕜] (E →L[𝕜] F)))

omit [CompleteSpace F] in
theorem zero_mem_nuclearOperators :
    (0 : E →L[𝕜] F) ∈ nuclearOperators 𝕜 E F :=
  ⟨0, by
    have h_ext := UniformSpace.Completion.extension_coe toContinuousLinearMap.uniformContinuous
      (0 : F ⊗[𝕜] StrongDual 𝕜 E)
    apply Eq.trans (congr_arg _ (UniformSpace.Completion.coe_zero.symm))
    exact Eq.trans h_ext (map_zero toContinuousLinearMap)⟩

theorem comp_right_mem_nuclearOperators
    {S : E' →L[𝕜] F} (hS : S ∈ nuclearOperators 𝕜 E' F) (A : E →L[𝕜] E') :
    S.comp A ∈ nuclearOperators 𝕜 E F := by
  obtain ⟨x, rfl⟩ := hS
  let phiE := (toContinuousLinearMap : F ⊗[𝕜] StrongDual 𝕜 E →L[𝕜] (E →L[𝕜] F))
  let phiE' := (toContinuousLinearMap : F ⊗[𝕜] StrongDual 𝕜 E' →L[𝕜] (E' →L[𝕜] F))
  let precompA := (ContinuousLinearMap.compL 𝕜 E E' F).flip A
  let m := liftEquiv 𝕜 F (StrongDual 𝕜 E') (F ⊗[𝕜] StrongDual 𝕜 E) <|
    ((ContinuousLinearMap.compL 𝕜 (StrongDual 𝕜 E') (StrongDual 𝕜 E) _).flip
      ((ContinuousLinearMap.compL 𝕜 E E' 𝕜).flip A)).comp
    ((liftEquiv 𝕜 F (StrongDual 𝕜 E) _).symm (ContinuousLinearMap.id 𝕜 _))
  have h_dense : precompA.comp phiE' = phiE.comp m :=
    (liftEquiv 𝕜 F (StrongDual 𝕜 E') (E →L[𝕜] F)).symm.injective (by ext; rfl)
  use Completion.map m x
  refine Completion.induction_on x ?_ fun y ↦ ?_
  · exact isClosed_eq (Completion.continuous_extension.comp' Completion.continuous_map)
      (Completion.continuous_extension.clm_comp_const A)
  · rw [Completion.map_coe m.uniformContinuous, Completion.extension_coe phiE.uniformContinuous,
      Completion.extension_coe phiE'.uniformContinuous]
    exact (ContinuousLinearMap.ext_iff.1 h_dense y).symm

theorem comp_left_mem_nuclearOperators
    {S : E →L[𝕜] F'} (hS : S ∈ nuclearOperators 𝕜 E F') (B : F' →L[𝕜] F) :
    B.comp S ∈ nuclearOperators 𝕜 E F := by
  obtain ⟨x, rfl⟩ := hS
  let phiF := (toContinuousLinearMap : F ⊗[𝕜] StrongDual 𝕜 E →L[𝕜] (E →L[𝕜] F))
  let phiF' := (toContinuousLinearMap : F' ⊗[𝕜] StrongDual 𝕜 E →L[𝕜] (E →L[𝕜] F'))
  let postcompB := ContinuousLinearMap.compL 𝕜 E F' F B
  let m := liftEquiv 𝕜 F' (StrongDual 𝕜 E) (F ⊗[𝕜] StrongDual 𝕜 E) <|
    ((liftEquiv 𝕜 F (StrongDual 𝕜 E) _).symm (ContinuousLinearMap.id 𝕜 _)).comp B
  have h_dense : postcompB.comp phiF' = phiF.comp m := by
    apply (liftEquiv 𝕜 F' (StrongDual 𝕜 E) (E →L[𝕜] F)).symm.injective
    ext f g y
    exact B.map_smul (g y) f
  use Completion.map m x
  refine Completion.induction_on x ?_ fun y ↦ ?_
  · exact isClosed_eq (Completion.continuous_extension.comp' Completion.continuous_map)
      (postcompB.continuous.comp Completion.continuous_extension)
  · rw [Completion.map_coe m.uniformContinuous, Completion.extension_coe phiF.uniformContinuous,
      Completion.extension_coe phiF'.uniformContinuous]
    exact (ContinuousLinearMap.ext_iff.1 h_dense y).symm

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace Y] [AddCommGroup Y] [Module 𝕜 Y]

/-- A continuous linear map `T : X →L[𝕜] Y` between topological vector spaces is nuclear
if it factors through a nuclear operator between Banach spaces. -/
def IsNuclear (T : X →L[𝕜] Y) : Prop :=
  ∃ (E : Type u) (_ : SeminormedAddCommGroup E) (_ : NormedSpace 𝕜 E)
    (F : Type v) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F) (_ : CompleteSpace F)
    (A : X →L[𝕜] E) (B : F →L[𝕜] Y) (S : E →L[𝕜] F),
    S ∈ nuclearOperators 𝕜 E F ∧ T = B.comp (S.comp A)

/-- Any operator between Banach spaces that belongs to the set `nuclearOperators`
    is automatically `IsNuclear` under the generalized definition. -/
theorem isNuclear_iff_mem_nuclearOperators (T : E →L[𝕜] F) :
    IsNuclear T ↔ T ∈ nuclearOperators 𝕜 E F := by
  constructor
  · rintro ⟨E', _, _, F', _, _, _, A, B, S, hS, rfl⟩
    exact comp_left_mem_nuclearOperators (comp_right_mem_nuclearOperators hS A) B
  · intro hT
    use E, inferInstance, inferInstance
    use F, inferInstance, inferInstance, inferInstance
    use ContinuousLinearMap.id 𝕜 E, ContinuousLinearMap.id 𝕜 F, T
    simp [hT]

variable {X' : Type u} {Y' : Type v}
variable [TopologicalSpace X'] [AddCommGroup X'] [Module 𝕜 X']
variable [TopologicalSpace Y'] [AddCommGroup Y'] [Module 𝕜 Y']

-- Absorbs composition from the right
theorem IsNuclear.comp_right {T : X' →L[𝕜] Y} (hT : IsNuclear T) (A : X →L[𝕜] X') :
    IsNuclear (T.comp A) := by
  obtain ⟨E, hE1, hE2, F, hF1, hF2, hF3, A', B', S, hS, rfl⟩ := hT
  exact ⟨E, hE1, hE2, F, hF1, hF2, hF3, A'.comp A, B', S, hS, by ext; rfl⟩

theorem IsNuclear.comp_left {T : X →L[𝕜] Y'} (hT : IsNuclear T) (B : Y' →L[𝕜] Y) :
    IsNuclear (B.comp T) := by
  obtain ⟨E, hE1, hE2, F, hF1, hF2, hF3, A, B', S, hS, rfl⟩ := hT
  exact ⟨E, hE1, hE2, F, hF1, hF2, hF3, A, B.comp B', S, hS, by ext; rfl⟩

theorem IsNuclear.zero : IsNuclear (0 : X →L[𝕜] Y) := by
  use PUnit, inferInstance, inferInstance
  use PUnit, inferInstance, inferInstance, inferInstance
  use 0, 0, 0
  exact ⟨zero_mem_nuclearOperators, by ext; simp⟩

variable [IsTopologicalAddGroup Y] in
-- Closed under addition
theorem IsNuclear.add
    {T₁ T₂ : X →L[𝕜] Y} (h₁ : IsNuclear T₁) (h₂ : IsNuclear T₂) :
    IsNuclear (T₁ + T₂) := by
  obtain ⟨E1, hE1a, hE1b, F1, hF1a, hF1b, hF1c, A1, B1, S1, hS1, rfl⟩ := h₁
  obtain ⟨E2, hE2a, hE2b, F2, hF2a, hF2b, hF2c, A2, B2, S2, hS2, rfl⟩ := h₂
  let proj1 := ContinuousLinearMap.fst 𝕜 E1 E2
  let proj2 := ContinuousLinearMap.snd 𝕜 E1 E2
  let inj1 := ContinuousLinearMap.inl 𝕜 F1 F2
  let inj2 := ContinuousLinearMap.inr 𝕜 F1 F2
  obtain ⟨x1, hx1⟩ := comp_left_mem_nuclearOperators
    (comp_right_mem_nuclearOperators hS1 proj1) inj1
  obtain ⟨x2, hx2⟩ := comp_left_mem_nuclearOperators
    (comp_right_mem_nuclearOperators hS2 proj2) inj2
  let phi : (F1 × F2) ⊗[𝕜] StrongDual 𝕜 (E1 × E2) →L[𝕜] (E1 × E2 →L[𝕜] F1 × F2) :=
    toContinuousLinearMap
  refine ⟨E1 × E2, inferInstance, inferInstance,
    F1 × F2, inferInstance, inferInstance, inferInstance,
    A1.prod A2, B1.coprod B2, inj1.comp (S1.comp proj1) + inj2.comp (S2.comp proj2),
    ⟨x1 + x2, ?_⟩, ?_⟩
  · have ext_add : ∀ x y, Completion.extension phi (x + y) = Completion.extension phi x +
        Completion.extension phi y := by
      intro x y
      refine Completion.induction_on₂ x y
        (isClosed_eq (Completion.continuous_extension.comp continuous_add)
        ((Completion.continuous_extension.comp continuous_fst).add
        (Completion.continuous_extension.comp continuous_snd))) fun a b ↦ ?_
      rw [← Completion.coe_add, Completion.extension_coe phi.uniformContinuous,
        Completion.extension_coe phi.uniformContinuous,
        Completion.extension_coe phi.uniformContinuous, map_add]
    rw [ext_add, hx1, hx2]
  · ext x
    simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]
    change B1 (S1 (A1 x)) + B2 (S2 (A2 x)) = (B1 (S1 (A1 x)) + B2 0) + (B1 0 + B2 (S2 (A2 x)))
    simp

variable [ContinuousSMul 𝕜 Y] in
-- Closed under scalar multiplication
theorem IsNuclear.smul
    {T : X →L[𝕜] Y} (hT : IsNuclear T) (c : 𝕜) :
    IsNuclear (c • T) := by
  obtain ⟨E, hE1, hE2, F, hF1, hF2, hF3, A, B, S, hS, rfl⟩ := hT
  exact ⟨E, hE1, hE2, F, hF1, hF2, hF3, A, c • B, S, hS, by ext; rfl⟩

end ContinuousLinearMap
