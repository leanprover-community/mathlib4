/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Analysis.Seminorm

open TopologicalSpace SeminormFamily
open scoped BoundedContinuousFunction Topology

variable (𝕜 E F : Type _) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {n : ℕ∞}

structure BoundedContDiffMap (n : ℕ∞) : Type _ where
  protected toFun : E → F
  protected contDiff' : ContDiff 𝕜 n toFun
  protected bounded' : ∀ i : ℕ, i ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 i toFun x‖ ≤ C

notation:25 E " →ᵇ[" 𝕜 ", " n "] " F => BoundedContDiffMap 𝕜 E F n

class BoundedContDiffMapClass (B : Type _) (𝕜 E F : outParam <| Type _) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (n : outParam ℕ∞) extends FunLike B E (fun _ ↦ F) where
  protected contDiff (f : B) : ContDiff 𝕜 n f
  protected bounded (f : B) : ∀ ⦃i : ℕ⦄, i ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 i f x‖ ≤ C

namespace BoundedContDiffMap

instance toBoundedContDiffMapClass : BoundedContDiffMapClass (E →ᵇ[𝕜, n] F) 𝕜 E F n where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  contDiff f := f.contDiff'
  bounded f := f.bounded'

variable {𝕜 E F}

protected theorem contDiff (f : E →ᵇ[𝕜, n] F) : ContDiff 𝕜 n f := f.contDiff'
protected theorem bounded (f : E →ᵇ[𝕜, n] F) :
    ∀ i : ℕ, i ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 i f x‖ ≤ C :=
  f.bounded'


@[simp]
theorem toFun_eq_coe {f : E →ᵇ[𝕜, n] F} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.apply (f : E →ᵇ[𝕜, n] F) : E →F  := f

-- this must come after the coe_to_fun definition
initialize_simps_projections BoundedContDiffMap (toFun → apply)

@[ext]
theorem ext {f g : E →ᵇ[𝕜, n] F} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h

/-- Copy of a `BoundedContDiffMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : E →ᵇ[𝕜, n] F) (f' : E → F) (h : f' = f) : E →ᵇ[𝕜, n] F where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  bounded' := h.symm ▸ f.bounded

@[simp]
theorem coe_copy (f : E →ᵇ[𝕜, n] F) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : E →ᵇ[𝕜, n] F) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h

instance : AddCommGroup (E →ᵇ[𝕜, n] F) where
  add f g := BoundedContDiffMap.mk (f + g) (f.contDiff.add g.contDiff) fun i hi ↦ by
    rcases f.bounded i hi with ⟨Cf, hCf⟩; rcases g.bounded i hi with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun x ↦ ?_⟩
    rw [iteratedFDeriv_add_apply (f.contDiff.of_le hi) (g.contDiff.of_le hi)]
    exact norm_add_le_of_le (hCf x) (hCg x)
  add_assoc f₁ f₂ f₃ := by ext; exact add_assoc _ _ _
  add_comm f g := by ext; exact add_comm _ _
  zero := BoundedContDiffMap.mk 0 contDiff_zero_fun fun i _ ↦ by
    refine ⟨0, fun x ↦ ?_⟩
    rw [Pi.zero_def, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
  zero_add f := by ext; exact zero_add _
  add_zero f := by ext; exact add_zero _
  neg f := BoundedContDiffMap.mk (-f) (f.contDiff.neg) fun i hi ↦ by
    simpa only [iteratedFDeriv_neg_apply, norm_neg] using (f.bounded i hi)
  add_left_neg f := by ext; exact add_left_neg _

instance : Module 𝕜 (E →ᵇ[𝕜, n] F) where
  smul c f := BoundedContDiffMap.mk (c • (f : E → F)) (f.contDiff.const_smul c) fun i hi ↦ by
    rcases f.bounded i hi with ⟨B, hB⟩
    refine ⟨‖c‖ * B, fun x ↦ ?_⟩
    rw [iteratedFDeriv_const_smul_apply (f.contDiff.of_le hi), norm_smul]
    exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
  one_smul f := by ext; exact one_smul _ _
  mul_smul c₁ c₂ f := by ext; exact mul_smul _ _ _
  smul_zero c := by ext; exact smul_zero _
  smul_add c f g := by ext; exact smul_add _ _ _
  add_smul c₁ c₂ f := by ext; exact add_smul _ _ _
  zero_smul f := by ext; exact zero_smul _ _

noncomputable def iteratedFDerivₗ (i : ℕ) :
    (E →ᵇ[𝕜, n] F) →ₗ[𝕜] (E →ᵇ (E [×i]→L[𝕜] F)) :=
  if hi : i ≤ n then
  { toFun := fun f ↦ .ofNormedAddCommGroup (iteratedFDeriv 𝕜 i f)
      (f.contDiff.continuous_iteratedFDeriv hi) (f.bounded i hi).choose
      (fun x ↦ (f.bounded i hi).choose_spec x),
    map_add' := by
      intro f g
      ext : 1
      exact iteratedFDeriv_add_apply (f.contDiff.of_le hi) (g.contDiff.of_le hi),
    map_smul' := by
      intro c f
      ext : 1
      exact iteratedFDeriv_const_smul_apply (f.contDiff.of_le hi) }
  else 0

@[simp]
theorem iteratedFDerivₗ_apply (i : ℕ) (f : E →ᵇ[𝕜, n] F) (x : E) :
    BoundedContDiffMap.iteratedFDerivₗ i f x = if i ≤ n then iteratedFDeriv 𝕜 i f x else 0 := by
  rw [BoundedContDiffMap.iteratedFDerivₗ]
  split_ifs <;> rfl

theorem iteratedFDerivₗ_of_gt {i : ℕ} (hin : i > n) :
    (BoundedContDiffMap.iteratedFDerivₗ i : (E →ᵇ[𝕜, n] F) →ₗ[𝕜] (E →ᵇ (E [×i]→L[𝕜] F))) = 0 :=
  dif_neg (not_le_of_gt hin)

section Topology

instance : TopologicalSpace (E →ᵇ[𝕜, n] F) :=
  ⨅ (i : ℕ), induced (BoundedContDiffMap.iteratedFDerivₗ i) inferInstance

noncomputable instance : UniformSpace (E →ᵇ[𝕜, n] F) := .replaceTopology
  (⨅ (i : ℕ), UniformSpace.comap (BoundedContDiffMap.iteratedFDerivₗ i) inferInstance)
  toTopologicalSpace_iInf.symm

protected theorem BoundedContDiffMap.uniformSpace_eq_iInf :
    (instUniformSpaceBoundedContDiffMap : UniformSpace (E →ᵇ[𝕜, n] F)) =
    ⨅ (i : ℕ), UniformSpace.comap (BoundedContDiffMap.iteratedFDerivₗ i) inferInstance :=
  UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm

instance : UniformAddGroup (E →ᵇ[𝕜, n] F) := by
  rw [BoundedContDiffMap.uniformSpace_eq_iInf]
  refine uniformAddGroup_iInf (fun i ↦ ?_)
  exact uniformAddGroup_comap _

noncomputable def iteratedFDerivL (i : ℕ) :
    (E →ᵇ[𝕜, n] F) →L[𝕜] (E →ᵇ (E [×i]→L[𝕜] F)) :=
  { BoundedContDiffMap.iteratedFDerivₗ i with
    cont := continuous_iInf_dom continuous_induced_dom }

@[simp]
theorem iteratedFDerivL_apply (i : ℕ) (f : E →ᵇ[𝕜, n] F) (x : E) :
    BoundedContDiffMap.iteratedFDerivL i f x = if i ≤ n then iteratedFDeriv 𝕜 i f x else 0 := by
  simp [BoundedContDiffMap.iteratedFDerivL]

theorem iteratedFDerivL_of_gt {i : ℕ} (hin : i > n) :
    (BoundedContDiffMap.iteratedFDerivL i : (E →ᵇ[𝕜, n] F) →L[𝕜] (E →ᵇ (E [×i]→L[𝕜] F))) = 0 :=
  ContinuousLinearMap.coe_injective (BoundedContDiffMap.iteratedFDerivₗ_of_gt hin)

/-- This is mostly for dot notation. Should I keep it? -/
protected noncomputable abbrev iteratedFDeriv (i : ℕ) (f : E →ᵇ[𝕜, n] F) : E →ᵇ (E [×i]→L[𝕜] F) :=
  BoundedContDiffMap.iteratedFDerivL i f

protected theorem continuous_iff {X : Type _} [TopologicalSpace X] (φ : X → E →ᵇ[𝕜, n] F) :
  Continuous φ ↔ ∀ (i : ℕ) (_ : ↑i ≤ n), Continuous
    ((BoundedContDiffMap.iteratedFDeriv i) ∘ φ) :=
⟨ fun hφ i _ ↦ (BoundedContDiffMap.iteratedFDerivL i).continuous.comp hφ,
  fun h ↦ continuous_iInf_rng.mpr fun i ↦ continuous_induced_rng.mpr <| by
    by_cases hin : i ≤ n
    · exact h i hin
    · simpa [iteratedFDerivₗ_of_gt (lt_of_not_ge hin)] using continuous_zero ⟩

protected noncomputable def BoundedContDiffMap.seminorm (i : ℕ) : Seminorm 𝕜 (E →ᵇ[𝕜, n] F) :=
  (normSeminorm 𝕜 <| E →ᵇ (E [×i]→L[𝕜] F)).comp (BoundedContDiffMap.iteratedFDerivₗ i)

protected noncomputable def BoundedContDiffMap.seminorm' (i : ℕ) : Seminorm 𝕜 (E →ᵇ[𝕜, n] F) :=
  (Finset.Iic i).sup fun j ↦
    (normSeminorm 𝕜 <| E →ᵇ (E [×j]→L[𝕜] F)).comp (BoundedContDiffMap.iteratedFDerivₗ j)

theorem BoundedContDiffMap.withSeminorms :
    WithSeminorms (BoundedContDiffMap.seminorm : SeminormFamily 𝕜 (E →ᵇ[𝕜, n] F) ℕ) := by
  let p : SeminormFamily 𝕜 (E →ᵇ[𝕜, n] F) ((_ : ℕ) × Fin 1) :=
    SeminormFamily.sigma fun i ↦ fun _ ↦
      (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[𝕜] F))).comp (BoundedContDiffMap.iteratedFDerivₗ i)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
  exact this.congr_equiv (Equiv.sigmaUnique _ _).symm

theorem BoundedContDiffMap.withSeminorms' :
    WithSeminorms (BoundedContDiffMap.seminorm' : SeminormFamily 𝕜 (E →ᵇ[𝕜, n] F) ℕ) :=
  BoundedContDiffMap.withSeminorms.partial_sups

end Topology

section fderiv

noncomputable def fderivL (n : ℕ∞) : (E →ᵇ[𝕜, n+1] F) →L[𝕜] (E →ᵇ[𝕜, n] (E →L[𝕜] F)) where
  toFun f :=
  { toFun := fderiv 𝕜 f
    contDiff' := f.contDiff.fderiv_right le_rfl
    bounded' := fun i hin ↦ by
      rcases f.bounded (i+1) (add_le_add_right hin 1) with ⟨C, hC⟩
      refine ⟨C, fun x ↦ ?_⟩
      rw [norm_iteratedFDeriv_fderiv]
      exact hC x }
  map_add' f₁ f₂ := sorry
  map_smul' := sorry
  cont := sorry

end fderiv

end BoundedContDiffMap
