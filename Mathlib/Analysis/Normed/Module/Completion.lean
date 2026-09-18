/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.UniformField

/-!
# Normed space structure on the completion of a normed space

If `E` is a normed space over `𝕜`, then so is `UniformSpace.Completion E`. In this file we provide
necessary instances and define `UniformSpace.Completion.toComplₗᵢ` - coercion
`E → UniformSpace.Completion E` as a bundled linear isometry.

We also show that if `A` is a normed algebra over `𝕜`, then so is `UniformSpace.Completion A`.

TODO: Generalise the results here from the concrete `completion` to any `AbstractCompletion`.
-/

@[expose] public section


noncomputable section

namespace UniformSpace

namespace Completion

variable (𝕜 E : Type*)

instance [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    NormedSpace 𝕜 (Completion E) where
  norm_smul_le := norm_smul_le

section Module

variable {𝕜 E}
variable [Semiring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [UniformContinuousConstSMul 𝕜 E]

/-- Embedding of a normed space to its completion as a linear isometry. -/
def toComplₗᵢ : E →ₗᵢ[𝕜] Completion E :=
  { toComplL with norm_map' := norm_coe }

@[simp]
theorem coe_toComplₗᵢ : ⇑(toComplₗᵢ : E →ₗᵢ[𝕜] Completion E) = ((↑) : E → Completion E) :=
  rfl

@[simp] lemma toContinuousLinearMap_toComplₗᵢ :
    (toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).toContinuousLinearMap = toComplL := rfl

@[simp]
theorem norm_toComplL {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E] : ‖(toComplL : E →L[𝕜] Completion E)‖ = 1 :=
  (toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap

end Module

section Algebra

variable (A : Type*)

instance [SeminormedRing A] : NormedRing (Completion A) where
  __ : NormedAddCommGroup (Completion A) := inferInstance
  __ : Ring (Completion A) := inferInstance
  norm_mul_le x y := by
    induction x, y using induction_on₂ with
    | hp => apply isClosed_le <;> fun_prop
    | ih x y => simpa only [← coe_mul, norm_coe] using norm_mul_le x y

instance [SeminormedCommRing A] : NormedCommRing (Completion A) where
  __ : CommRing (Completion A) := inferInstance
  __ : NormedRing (Completion A) := inferInstance

instance [NormedField 𝕜] [SeminormedCommRing A] [NormedAlgebra 𝕜 A] :
    NormedAlgebra 𝕜 (Completion A) where
  norm_smul_le := norm_smul_le

instance [NormedField A] [CompletableTopField A] :
    NormedField (UniformSpace.Completion A) where
  __ : NormedCommRing (Completion A) := inferInstance
  __ : Field (Completion A) := inferInstance
  norm_mul x y := induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) (by simp [← coe_mul])

end Algebra

end Completion

end UniformSpace

/-!
# Real scalars on a complete normed `ℚ`-algebra

A complete normed ring `𝔸` with a `NormedAlgebra ℚ 𝔸` structure carries a `NormedAlgebra ℝ 𝔸`
structure, and that structure is unique.
-/

section Real

variable (𝔸 : Type*) [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

private lemma uniformContinuous_algebraMap : UniformContinuous (algebraMap ℚ 𝔸) := by
  have h : ⇑(algebraMap ℚ 𝔸) =
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℚ ℚ) (1 : 𝔸)) := by
    ext; simp [Algebra.algebraMap_eq_smul_one]
  exact h ▸ (ContinuousLinearMap.smulRight ..).uniformContinuous

/-- Extend normed algebras over `ℚ` to normed algebras over `ℝ` on Banach algebras. -/
@[no_expose]
abbrev normedAlgebraReal [CompleteSpace 𝔸] : NormedAlgebra ℝ 𝔸 where
  __ := (IsDenseInducing.extendRingHom (i := Rat.castHom ℝ)
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (uniformContinuous_algebraMap 𝔸)).toAlgebra' fun r x ↦ by
      let ue := Rat.isUniformEmbedding_coe_real.isUniformInducing
      have : Continuous (IsDenseInducing.extendRingHom (i := Rat.castHom ℝ)
        ue Rat.denseRange_cast (uniformContinuous_algebraMap 𝔸)) :=
        (uniformContinuous_uniformly_extend ue Rat.denseRange_cast
          (uniformContinuous_algebraMap 𝔸)).continuous
      refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r ?_ fun a ↦ ?_
      · exact isClosed_eq (by fun_prop) (by fun_prop)
      · change (ue.isDenseInducing Rat.denseRange_cast).extend (algebraMap ℚ 𝔸) a * x =
          x * (ue.isDenseInducing Rat.denseRange_cast).extend (algebraMap ℚ 𝔸) a
        rw [(ue.isDenseInducing Rat.denseRange_cast).extend_eq (by fun_prop), Algebra.commutes']
  norm_smul_le r x := by
    let ue := Rat.isUniformEmbedding_coe_real.isUniformInducing
    have : Continuous (IsDenseInducing.extendRingHom (i := Rat.castHom ℝ)
      ue Rat.denseRange_cast (uniformContinuous_algebraMap 𝔸)) :=
      (uniformContinuous_uniformly_extend ue Rat.denseRange_cast
        (uniformContinuous_algebraMap 𝔸)).continuous
    refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r ?_ fun a ↦ ?_
    · simpa only [Algebra.smul_def, algebraMap] using isClosed_le (by fun_prop) (by fun_prop)
    · simp only [Algebra.smul_def, algebraMap, Rat.norm_cast_real]
      change ‖(ue.isDenseInducing Rat.denseRange_cast).extend (algebraMap ℚ 𝔸) a * x‖ ≤ _
      rw [(ue.isDenseInducing Rat.denseRange_cast).extend_eq (by fun_prop), ← Algebra.smul_def]
      exact norm_smul_le a x

/-- A complete normed `ℚ`-algebra carries a unique `NormedAlgebra ℝ` structure. -/
noncomputable instance [CompleteSpace 𝔸] : Unique (NormedAlgebra ℝ 𝔸) where
  default := normedAlgebraReal 𝔸
  uniq h := by
    have : Continuous (algebraMap ℝ 𝔸) := by fun_prop
    let ue := Rat.isUniformEmbedding_coe_real.isUniformInducing
    have : Continuous (IsDenseInducing.extendRingHom (i := Rat.castHom ℝ)
      ue Rat.denseRange_cast (uniformContinuous_algebraMap 𝔸)) :=
      (uniformContinuous_uniformly_extend ue Rat.denseRange_cast
        (uniformContinuous_algebraMap 𝔸)).continuous
    rcases h with @⟨P, hP⟩
    congr; ext r x
    rw [Algebra.smul_def, @Algebra.smul_def _ _ _ _ (normedAlgebraReal 𝔸).toAlgebra]
    refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r ?_ fun a ↦ ?_
    · exact isClosed_eq (by fun_prop) (by simp only [algebraMap]; fun_prop)
    · rw [← eq_ratCast (algebraMap ℚ ℝ), ← IsScalarTower.rat.algebraMap_apply,
        ← @(@IsScalarTower.rat _ _ _ _ (normedAlgebraReal 𝔸).toModule _ _).algebraMap_apply]

end Real
