/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Sets.Compacts

open TopologicalSpace SeminormFamily Set Function
open scoped BoundedContinuousFunction Topology

variable (𝕜 E F : Type _) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {n : ℕ∞} {K : Compacts E}

structure ContDiffMapSupportedIn (n : ℕ∞) (K : Compacts E) : Type _ where
  protected toFun : E → F
  protected contDiff' : ContDiff 𝕜 n toFun
  protected zero_on_compl' : EqOn toFun 0 Kᶜ

scoped[Distributions] notation "𝓓[" 𝕜 "]^" n "_"K"⟮" E ", " F "⟯" =>
  ContDiffMapSupportedIn 𝕜 E F n K

scoped[Distributions] notation "𝓓[" 𝕜 "]_"K"⟮" E ", " F "⟯" =>
  ContDiffMapSupportedIn 𝕜 E F ⊤ K

scoped[Distributions] notation "𝓓^" n "_"K"⟮" E ", " F "⟯" =>
  ContDiffMapSupportedIn ℝ E F n K

scoped[Distributions] notation "𝓓_"K"⟮" E ", " F "⟯" =>
  ContDiffMapSupportedIn ℝ E F ⊤ K

open Distributions

class ContDiffMapSupportedInClass (B : Type _) (𝕜 E F : outParam <| Type _)
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜 F] (n : outParam ℕ∞) (K : outParam <| Compacts E)
    extends FunLike B E (fun _ ↦ F) where
  protected contDiff (f : B) : ContDiff 𝕜 n f
  protected zero_on_compl (f : B) : EqOn f 0 Kᶜ

namespace ContDiffMapSupportedIn

instance toContDiffMapSupportedInClass :
    ContDiffMapSupportedInClass 𝓓[𝕜]^(n)_(K)⟮E, F⟯ 𝕜 E F n K where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  contDiff f := f.contDiff'
  zero_on_compl f := f.zero_on_compl'

variable {𝕜 E F}

protected theorem contDiff (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) : ContDiff 𝕜 n f := f.contDiff'
protected theorem zero_on_compl (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) : EqOn f 0 Kᶜ :=
  f.zero_on_compl'

@[simp]
theorem toFun_eq_coe {f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.apply (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) : E →F  := f

-- this must come after the coe_to_fun definition
initialize_simps_projections ContDiffMapSupportedIn (toFun → apply)

@[ext]
theorem ext {f g : 𝓓[𝕜]^(n)_(K)⟮E, F⟯} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h

/-- Copy of a `BoundedContDiffMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) (f' : E → F) (h : f' = f) : 𝓓[𝕜]^(n)_(K)⟮E, F⟯ where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  zero_on_compl' := h.symm ▸ f.zero_on_compl

@[simp]
theorem coe_copy (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h

instance : AddCommGroup (𝓓[𝕜]^(n)_(K)⟮E, F⟯) where
  add f g := ContDiffMapSupportedIn.mk (f + g) (f.contDiff.add g.contDiff) <| by
    rw [← add_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl
  add_assoc f₁ f₂ f₃ := by ext; exact add_assoc _ _ _
  add_comm f g := by ext; exact add_comm _ _
  zero := ContDiffMapSupportedIn.mk 0 contDiff_zero_fun fun _ _ ↦ rfl
  zero_add f := by ext; exact zero_add _
  add_zero f := by ext; exact add_zero _
  neg f := ContDiffMapSupportedIn.mk (-f) (f.contDiff.neg) <| by
    rw [← neg_zero]
    exact f.zero_on_compl.comp_left
  add_left_neg f := by ext; exact add_left_neg _

instance : Module 𝕜 (𝓓[𝕜]^(n)_(K)⟮E, F⟯) where
  smul c f := ContDiffMapSupportedIn.mk (c • (f : E → F)) (f.contDiff.const_smul c) <| by
    rw [← smul_zero c]
    exact f.zero_on_compl.comp_left
  one_smul f := by ext; exact one_smul _ _
  mul_smul c₁ c₂ f := by ext; exact mul_smul _ _ _
  smul_zero c := by ext; exact smul_zero _
  smul_add c f g := by ext; exact smul_add _ _ _
  add_smul c₁ c₂ f := by ext; exact add_smul _ _ _
  zero_smul f := by ext; exact zero_smul _ _

protected theorem support_subset (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) : support f ⊆ K :=
  support_subset_iff'.mpr f.zero_on_compl

protected theorem tsupport_subset (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) : tsupport f ⊆ K :=
  closure_minimal f.support_subset K.2.isClosed

protected theorem hasCompactSupport (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) : HasCompactSupport f :=
  HasCompactSupport.intro K.2 f.zero_on_compl

protected def of_support_subset {f : E → F} (hf : ContDiff 𝕜 n f) (hsupp : support f ⊆ K) :
    𝓓[𝕜]^(n)_(K)⟮E, F⟯ where
  toFun := f
  contDiff' := hf
  zero_on_compl' := support_subset_iff'.mp hsupp

protected theorem bounded (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) :
    ∃ C, ∀ x, ‖f x‖ ≤ C :=
  f.contDiff.continuous.bounded_above_of_compact_support f.hasCompactSupport

#check HasCompactSupport.iteratedFDeriv

protected theorem support_iteratedFDeriv_subset (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) {i : ℕ} (hi : i ≤ n) :
    support (iteratedFDeriv 𝕜 i f) ⊆ K := by
  rw [support_subset_iff']

protected theorem tsupport_subset (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) : tsupport f ⊆ K :=
  closure_minimal f.support_subset K.2.isClosed

protected theorem hasCompactSupport (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) : HasCompactSupport f :=
  HasCompactSupport.intro K.2 f.zero_on_compl

protected theorem bounded (f : 𝓓[𝕜]^(n)_(K)⟮E, F⟯) {i : ℕ} (hi : i ≤ n) :
    ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 i f x‖ ≤ C := by
  refine Continuous.bounded_

noncomputable def iteratedFDerivₗ (i : ℕ) :
    𝓓[𝕜]^(n)_(K)⟮E, F⟯ →ₗ[𝕜] (E →ᵇ (E [×i]→L[𝕜] F)) :=
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
    iteratedFDerivₗ i f x = if i ≤ n then iteratedFDeriv 𝕜 i f x else 0 := by
  rw [iteratedFDerivₗ]
  split_ifs <;> rfl

@[simp]
theorem iteratedFDerivₗ_apply_of_le {i : ℕ} (hin : i ≤ n) (f : E →ᵇ[𝕜, n] F) (x : E) :
    iteratedFDerivₗ i f x = iteratedFDeriv 𝕜 i f x := by
  rw [iteratedFDerivₗ_apply]
  exact dif_pos hin

theorem iteratedFDerivₗ_of_gt {i : ℕ} (hin : i > n) :
    (iteratedFDerivₗ i : (E →ᵇ[𝕜, n] F) →ₗ[𝕜] (E →ᵇ (E [×i]→L[𝕜] F))) = 0 :=
  dif_neg (not_le_of_gt hin)

theorem iteratedFDerivₗ_apply_of_gt {i : ℕ} (hin : i > n) (f : E →ᵇ[𝕜, n] F) (x : E) :
    (iteratedFDerivₗ i f x) = 0 := by
  rw [iteratedFDerivₗ_apply]
  exact dif_neg (not_le_of_gt hin)

section Topology

instance : TopologicalSpace (E →ᵇ[𝕜, n] F) :=
  ⨅ (i : ℕ), induced (iteratedFDerivₗ i) inferInstance

noncomputable instance : UniformSpace (E →ᵇ[𝕜, n] F) := .replaceTopology
  (⨅ (i : ℕ), UniformSpace.comap (iteratedFDerivₗ i) inferInstance)
  toTopologicalSpace_iInf.symm

protected theorem BoundedContDiffMap.uniformSpace_eq_iInf :
    (instUniformSpaceBoundedContDiffMap : UniformSpace (E →ᵇ[𝕜, n] F)) =
    ⨅ (i : ℕ), UniformSpace.comap (iteratedFDerivₗ i) inferInstance :=
  UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm

instance : UniformAddGroup (E →ᵇ[𝕜, n] F) := by
  rw [BoundedContDiffMap.uniformSpace_eq_iInf]
  refine uniformAddGroup_iInf (fun i ↦ ?_)
  exact uniformAddGroup_comap _

noncomputable def iteratedFDerivL (i : ℕ) :
    (E →ᵇ[𝕜, n] F) →L[𝕜] (E →ᵇ (E [×i]→L[𝕜] F)) :=
  { iteratedFDerivₗ i with
    cont := continuous_iInf_dom continuous_induced_dom }

@[simp]
theorem iteratedFDerivL_apply (i : ℕ) (f : E →ᵇ[𝕜, n] F) (x : E) :
    iteratedFDerivL i f x = if i ≤ n then iteratedFDeriv 𝕜 i f x else 0 := by
  simp [iteratedFDerivL]

@[simp]
theorem iteratedFDerivL_apply_of_le {i : ℕ} (hin : i ≤ n) (f : E →ᵇ[𝕜, n] F) (x : E) :
    iteratedFDerivL i f x = iteratedFDeriv 𝕜 i f x := by
  rw [iteratedFDerivL_apply]
  exact dif_pos hin

theorem iteratedFDerivL_of_gt {i : ℕ} (hin : i > n) :
    (iteratedFDerivL i : (E →ᵇ[𝕜, n] F) →L[𝕜] (E →ᵇ (E [×i]→L[𝕜] F))) = 0 :=
  ContinuousLinearMap.coe_injective (iteratedFDerivₗ_of_gt hin)

theorem iteratedFDerivL_apply_of_gt {i : ℕ} (hin : i > n) (f : E →ᵇ[𝕜, n] F) (x : E) :
    (iteratedFDerivL i f x) = 0 := by
  rw [iteratedFDerivL_apply]
  exact dif_neg (not_le_of_gt hin)

/-- This is mostly for dot notation. Should I keep it? -/
protected noncomputable abbrev iteratedFDeriv (i : ℕ) (f : E →ᵇ[𝕜, n] F) : E →ᵇ (E [×i]→L[𝕜] F) :=
  iteratedFDerivL i f

protected theorem continuous_iff {X : Type _} [TopologicalSpace X] (φ : X → E →ᵇ[𝕜, n] F) :
  Continuous φ ↔ ∀ (i : ℕ) (_ : ↑i ≤ n), Continuous
    ((BoundedContDiffMap.iteratedFDeriv i) ∘ φ) :=
⟨ fun hφ i _ ↦ (iteratedFDerivL i).continuous.comp hφ,
  fun h ↦ continuous_iInf_rng.mpr fun i ↦ continuous_induced_rng.mpr <| by
    by_cases hin : i ≤ n
    · exact h i hin
    · simpa [iteratedFDerivₗ_of_gt (lt_of_not_ge hin)] using continuous_zero ⟩

variable (𝕜 E F n)

protected noncomputable def seminorm (i : ℕ) : Seminorm 𝕜 (E →ᵇ[𝕜, n] F) :=
  (normSeminorm 𝕜 <| E →ᵇ (E [×i]→L[𝕜] F)).comp (iteratedFDerivₗ i)

protected noncomputable def seminorm' (i : ℕ) : Seminorm 𝕜 (E →ᵇ[𝕜, n] F) :=
  (Finset.Iic i).sup (BoundedContDiffMap.seminorm 𝕜 E F n)

protected theorem withSeminorms :
    WithSeminorms (BoundedContDiffMap.seminorm 𝕜 E F n) := by
  let p : SeminormFamily 𝕜 (E →ᵇ[𝕜, n] F) ((_ : ℕ) × Fin 1) :=
    SeminormFamily.sigma fun i ↦ fun _ ↦
      (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[𝕜] F))).comp (BoundedContDiffMap.iteratedFDerivₗ i)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
  exact this.congr_equiv (Equiv.sigmaUnique _ _).symm

protected theorem withSeminorms' :
    WithSeminorms (BoundedContDiffMap.seminorm' 𝕜 E F n) :=
  (BoundedContDiffMap.withSeminorms 𝕜 E F n).partial_sups

variable {𝕜 E F n}

protected theorem seminorm_apply (i : ℕ) (f : E →ᵇ[𝕜, n] F) :
    BoundedContDiffMap.seminorm 𝕜 E F n i f = ‖f.iteratedFDeriv i‖ :=
  rfl

protected theorem seminorm_eq_bot {i : ℕ} (hin : n < i) :
    BoundedContDiffMap.seminorm 𝕜 E F n i = ⊥ := by
  ext f
  rw [BoundedContDiffMap.seminorm_apply, BoundedContDiffMap.iteratedFDeriv,
      iteratedFDerivL_of_gt hin, ContinuousLinearMap.zero_apply, norm_zero]
  rfl

end Topology

section fderiv

noncomputable def fderivₗ' (n : ℕ∞) : (E →ᵇ[𝕜, n+1] F) →ₗ[𝕜] (E →ᵇ[𝕜, n] (E →L[𝕜] F)) where
  toFun f :=
  { toFun := fderiv 𝕜 f
    contDiff' := f.contDiff.fderiv_right le_rfl
    bounded' := fun i hin ↦ by
      rcases f.bounded (i+1) (add_le_add_right hin 1) with ⟨C, hC⟩
      refine ⟨C, fun x ↦ ?_⟩
      rw [norm_iteratedFDeriv_fderiv]
      exact hC x }
  map_add' f₁ f₂ := by
    ext : 1
    exact fderiv_add
      (f₁.contDiff.differentiable le_add_self).differentiableAt
      (f₂.contDiff.differentiable le_add_self).differentiableAt
  map_smul' c f := by
    ext : 1
    exact fderiv_const_smul (f.contDiff.differentiable le_add_self).differentiableAt c

@[simp]
theorem fderivₗ'_apply (n : ℕ∞) (f : E →ᵇ[𝕜, n+1] F) (x : E) :
    fderivₗ' n f x = fderiv 𝕜 f x :=
  rfl

theorem seminorm_fderivₗ' (i : ℕ) (f : E →ᵇ[𝕜, n+1] F) :
    BoundedContDiffMap.seminorm 𝕜 E (E →L[𝕜] F) n i (fderivₗ' n f) =
      BoundedContDiffMap.seminorm 𝕜 E F (n+1) (i+1) f := by
  rw [BoundedContDiffMap.seminorm_apply, BoundedContDiffMap.seminorm_apply,
      BoundedContinuousFunction.norm_eq_of_nonempty, BoundedContinuousFunction.norm_eq_of_nonempty]
  refine congr_arg _ (Set.ext fun C ↦ forall_congr' fun x ↦ iff_of_eq <| congrArg₂ _ ?_ rfl)
  rcases le_or_gt (i : ℕ∞) n with (hin|hin)
  · have hin' : (i + 1 : ℕ) ≤ n + 1 := add_le_add_right hin _
    rw [iteratedFDerivL_apply_of_le hin, iteratedFDerivL_apply_of_le hin',
        ← norm_iteratedFDeriv_fderiv]
    rfl
  · have hin' : (i + 1 : ℕ) > n + 1 := WithTop.add_lt_add_right WithTop.one_ne_top hin
    rw [iteratedFDerivL_apply_of_gt hin, iteratedFDerivL_apply_of_gt hin', norm_zero, norm_zero]

noncomputable def fderivL' (n : ℕ∞) : (E →ᵇ[𝕜, n+1] F) →L[𝕜] (E →ᵇ[𝕜, n] (E →L[𝕜] F)) where
  toLinearMap := fderivₗ' n
  cont := by
    refine Seminorm.continuous_from_bounded  (τ₁₂ := RingHom.id 𝕜)
      (BoundedContDiffMap.withSeminorms 𝕜 E F (n+1))
      (BoundedContDiffMap.withSeminorms 𝕜 E (E →L[𝕜] F) n) ?_ ?_
    refine fun i ↦ ⟨{i+1}, 1, fun f ↦ ?_⟩
    rw [Finset.sup_singleton, one_smul]
    exact (seminorm_fderivₗ' i f).le

@[simp]
theorem fderivL'_apply (n : ℕ∞) (f : E →ᵇ[𝕜, n+1] F) (x : E) :
    fderivL' n f x = fderiv 𝕜 f x :=
  rfl

section infinite

noncomputable def fderivₗ : (E →ᵇ[𝕜, ⊤] F) →ₗ[𝕜] (E →ᵇ[𝕜, ⊤] (E →L[𝕜] F)) :=
  fderivₗ' ⊤

@[simp]
theorem fderivₗ_apply (f : E →ᵇ[𝕜, ⊤] F) (x : E) : fderivₗ f x = fderiv 𝕜 f x :=
  rfl

noncomputable def fderivL : (E →ᵇ[𝕜, ⊤] F) →L[𝕜] (E →ᵇ[𝕜, ⊤] (E →L[𝕜] F)) :=
  fderivL' ⊤

@[simp]
theorem fderivL_apply (n : ℕ∞) (f : E →ᵇ[𝕜, n+1] F) (x : E) :
    fderivL' n f x = fderiv 𝕜 f x :=
  rfl

end infinite

end fderiv

section finite

variable {n : ℕ}

protected theorem withSeminorms_of_finite : WithSeminorms
    (fun _ : Fin 1 ↦ (BoundedContDiffMap.seminorm' 𝕜 E F n n)) := by
  refine (BoundedContDiffMap.withSeminorms 𝕜 E F n).congr ?_ ?_
  · intro _
    use Finset.Iic n, 1
    rw [one_smul]
    rfl
  · intro i
    use {0}, 1
    rw [one_smul, Finset.sup_singleton, Seminorm.comp_id]
    rcases le_or_gt i n with (hin|hin)
    · rw [← Finset.mem_Iic] at hin
      exact Finset.le_sup (α := Seminorm 𝕜 (E →ᵇ[𝕜, n] F)) hin
    · rw [BoundedContDiffMap.seminorm_eq_bot (by exact_mod_cast hin)]
      exact bot_le

end finite

end BoundedContDiffMap

instance {E F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F] :
    LocallyConvexSpace ℝ (E →ᵇ[ℝ, n] F) :=
  locallyConvexSpace_iInf fun _ ↦ locallyConvexSpace_induced _
