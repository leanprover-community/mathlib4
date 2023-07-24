/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Sets.Compacts

open TopologicalSpace SeminormFamily Set Function Seminorm
open scoped BoundedContinuousFunction Topology NNReal

-- Think `𝕜 = ℝ` or `𝕜 = ℂ`
variable (𝕜 E F : Type _) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  {n : ℕ∞} {K : Compacts E}

structure ContDiffMapSupportedIn (n : ℕ∞) (K : Compacts E) : Type _ where
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected zero_on_compl' : EqOn toFun 0 Kᶜ

scoped[Distributions] notation "𝓓^{" n "}_{"K"}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F n K

scoped[Distributions] notation "𝓓_{"K"}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F ⊤ K

open Distributions

class ContDiffMapSupportedInClass (B : Type _) (E F : outParam <| Type _)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    extends FunLike B E (fun _ ↦ F) where
  map_contDiff (f : B) : ContDiff ℝ n f
  map_zero_on_compl (f : B) : EqOn f 0 Kᶜ

open ContDiffMapSupportedInClass

instance (B : Type _) (E F : outParam <| Type _)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type _) (E F : outParam <| Type _)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    have := HasCompactSupport.intro K.2 (map_zero_on_compl f)
    rcases (map_continuous f).bounded_above_of_compact_support this with ⟨C, hC⟩
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)

namespace ContDiffMapSupportedIn

instance toContDiffMapSupportedInClass :
    ContDiffMapSupportedInClass 𝓓^{n}_{K}(E, F) E F n K where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_zero_on_compl f := f.zero_on_compl'

variable {E F}

protected theorem contDiff (f : 𝓓^{n}_{K}(E, F)) : ContDiff ℝ n f := map_contDiff f
protected theorem zero_on_compl (f : 𝓓^{n}_{K}(E, F)) : EqOn f 0 Kᶜ :=
  map_zero_on_compl f

@[simp]
theorem toFun_eq_coe {f : 𝓓^{n}_{K}(E, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.apply (f : 𝓓^{n}_{K}(E, F)) : E →F  := f

-- this must come after the coe_to_fun definition
initialize_simps_projections ContDiffMapSupportedIn (toFun → apply)

@[ext]
theorem ext {f g : 𝓓^{n}_{K}(E, F)} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h

/-- Copy of a `BoundedContDiffMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}_{K}(E, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  zero_on_compl' := h.symm ▸ f.zero_on_compl

@[simp]
theorem coe_copy (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h

instance : AddCommGroup 𝓓^{n}_{K}(E, F) where
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

instance [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}_{K}(E, F) where
  smul c f := ContDiffMapSupportedIn.mk (c • (f : E → F)) (f.contDiff.const_smul c) <| by
    rw [← smul_zero c]
    exact f.zero_on_compl.comp_left
  one_smul f := by ext; exact one_smul _ _
  mul_smul c₁ c₂ f := by ext; exact mul_smul _ _ _
  smul_zero c := by ext; exact smul_zero _
  smul_add c f g := by ext; exact smul_add _ _ _
  add_smul c₁ c₂ f := by ext; exact add_smul _ _ _
  zero_smul f := by ext; exact zero_smul _ _

@[simp]
lemma coe_add (f g : 𝓓^{n}_{K}(E, F)) : (f + g : 𝓓^{n}_{K}(E, F)) = (f : E → F) + g :=
  rfl

@[simp]
lemma add_apply (f g : 𝓓^{n}_{K}(E, F)) (x : E) : (f + g) x = f x + g x :=
  rfl

@[simp]
lemma coe_smul [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}_{K}(E, F)) : (c • f : 𝓓^{n}_{K}(E, F)) = c • (f : E → F) :=
  rfl

@[simp]
lemma smul_apply [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}_{K}(E, F)) (x : E) : (c • f) x = c • (f x) :=
  rfl

protected theorem support_subset (f : 𝓓^{n}_{K}(E, F)) : support f ⊆ K :=
  support_subset_iff'.mpr f.zero_on_compl

protected theorem tsupport_subset (f : 𝓓^{n}_{K}(E, F)) : tsupport f ⊆ K :=
  closure_minimal f.support_subset K.2.isClosed

protected theorem hasCompactSupport (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  HasCompactSupport.intro K.2 f.zero_on_compl

protected def of_support_subset {f : E → F} (hf : ContDiff ℝ n f) (hsupp : support f ⊆ K) :
    𝓓^{n}_{K}(E, F) where
  toFun := f
  contDiff' := hf
  zero_on_compl' := support_subset_iff'.mp hsupp

protected theorem bounded_iteratedFDeriv (f : 𝓓^{n}_{K}(E, F)) {i : ℕ} (hi : i ≤ n) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  refine Continuous.bounded_above_of_compact_support (f.contDiff.continuous_iteratedFDeriv hi)
    (f.hasCompactSupport.iteratedFDeriv i)

noncomputable def to_bcfₗ : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ F  where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_to_bcfₗ (f : 𝓓^{n}_{K}(E, F)) :
    to_bcfₗ 𝕜 f = f :=
  rfl

@[simp]
theorem to_bcfₗ_apply (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    to_bcfₗ 𝕜 f x = f x :=
  rfl

protected noncomputable def iteratedFDeriv (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    𝓓^{n-i}_{K}(E, E [×i]→L[ℝ] F) :=
  if hi : i ≤ n then .of_support_subset
    sorry
    ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
  else 0

@[simp]
lemma iteratedFDeriv_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    f.iteratedFDeriv i x = if i ≤ n then iteratedFDeriv ℝ i f x else 0 := by
  rw [ContDiffMapSupportedIn.iteratedFDeriv]
  split_ifs <;> rfl

@[simp]
lemma iteratedFDeriv_apply_of_le {i : ℕ} (hin : i ≤ n) (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    f.iteratedFDeriv i x = iteratedFDeriv ℝ i f x := by
  rw [iteratedFDeriv_apply]
  exact dif_pos hin

lemma iteratedFDeriv_apply_of_gt {i : ℕ} (hin : i > n) (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    f.iteratedFDeriv i x = 0 := by
  rw [iteratedFDeriv_apply]
  exact dif_neg (not_le_of_gt hin)

lemma iteratedFDeriv_of_gt {i : ℕ} (hin : i > n) (f : 𝓓^{n}_{K}(E, F)) :
    f.iteratedFDeriv i = 0 := by
  ext x
  rw [iteratedFDeriv_apply_of_gt hin]
  rfl

@[simps]
noncomputable def iteratedFDerivₗ (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n-i}_{K}(E, E [×i]→L[ℝ] F) where
  toFun f := f.iteratedFDeriv i
  map_add' f g := by
    ext : 1
    simp only [iteratedFDeriv_apply, add_apply]
    split_ifs with hin
    · exact iteratedFDeriv_add_apply (f.contDiff.of_le hin) (g.contDiff.of_le hin)
    · rw [add_zero]
  map_smul' c f := by
    ext : 1
    simp only [iteratedFDeriv_apply, RingHom.id_apply, smul_apply]
    split_ifs with hin
    · exact iteratedFDeriv_const_smul_apply (f.contDiff.of_le hin)
    · rw [smul_zero]

/-- The composition of `ContDiffMapSupportedIn.to_bcfₗ` and
`ContDiffMapSupportedIn.iteratedFDerivₗ`. We define this as a separate `abbrev` because this family
of maps is used a lot for defining and using the topology on `ContDiffMapSupportedIn`, and Lean
takes a long time to infer the type of `to_bcfₗ 𝕜 ∘ₗ iteratedFDerivₗ 𝕜 i`. -/
noncomputable def iteratedFDeriv_to_bcfₗ (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F) :=
  to_bcfₗ 𝕜 ∘ₗ iteratedFDerivₗ 𝕜 i

section Topology

set_option profiler true in
set_option trace.Meta.synthInstance true in
instance topologicalSpace : TopologicalSpace 𝓓^{n}_{K}(E, F) :=
  ⨅ (i : ℕ), induced (iteratedFDeriv_to_bcfₗ ℝ i) inferInstance

noncomputable instance uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F) := .replaceTopology
  (⨅ (i : ℕ), UniformSpace.comap (iteratedFDeriv_to_bcfₗ ℝ i) inferInstance)
  toTopologicalSpace_iInf.symm

protected theorem uniformSpace_eq_iInf : (uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F)) =
    ⨅ (i : ℕ), UniformSpace.comap (iteratedFDeriv_to_bcfₗ ℝ i)
      inferInstance :=
  UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm

instance : UniformAddGroup 𝓓^{n}_{K}(E, F) := by
  rw [ContDiffMapSupportedIn.uniformSpace_eq_iInf]
  refine uniformAddGroup_iInf (fun i ↦ ?_)
  exact uniformAddGroup_comap _

instance : ContinuousSMul 𝕜 𝓓^{n}_{K}(E, F) := by
  refine continuousSMul_iInf (fun i ↦ continuousSMul_induced (iteratedFDeriv_to_bcfₗ 𝕜 i))

instance : LocallyConvexSpace ℝ 𝓓^{n}_{K}(E, F) :=
  locallyConvexSpace_iInf fun _ ↦ locallyConvexSpace_induced _

lemma continuous_iff_comp [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ ∀ i, Continuous (iteratedFDeriv_to_bcfₗ ℝ i ∘ φ) := by
  simp_rw [continuous_iInf_rng, continuous_induced_rng]

variable (E F n K)

protected noncomputable def seminorm (i : ℕ) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (normSeminorm 𝕜 <| E →ᵇ (E [×i]→L[ℝ] F)).comp (iteratedFDeriv_to_bcfₗ 𝕜 i)

protected noncomputable def seminorm' (i : ℕ) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm 𝕜 E F n K)

protected theorem withSeminorms :
    WithSeminorms (ContDiffMapSupportedIn.seminorm 𝕜 E F n K) := by
  let p : SeminormFamily 𝕜 𝓓^{n}_{K}(E, F) ((_ : ℕ) × Fin 1) :=
    SeminormFamily.sigma fun i ↦ fun _ ↦
      (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (iteratedFDeriv_to_bcfₗ 𝕜 i)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
  exact this.congr_equiv (Equiv.sigmaUnique _ _).symm

protected theorem withSeminorms' :
    WithSeminorms (ContDiffMapSupportedIn.seminorm' 𝕜 E F n K) :=
  (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).partial_sups

variable {E F n K}

protected theorem seminorm_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.seminorm 𝕜 E F n K i f =
      ‖(f.iteratedFDeriv i : E →ᵇ (E [×i]→L[ℝ] F))‖ :=
  rfl

protected theorem seminorm_eq_bot {i : ℕ} (hin : n < i) :
    ContDiffMapSupportedIn.seminorm 𝕜 E F n K i = ⊥ := by
  ext f
  rw [ContDiffMapSupportedIn.seminorm_apply,
      iteratedFDeriv_of_gt hin]
  exact norm_zero

noncomputable def to_bcfL' : 𝓓^{n}_{K}(E, F) →L[𝕜] E →ᵇ F :=
  { to_bcfₗ 𝕜 with
    cont := show Continuous (to_bcfₗ 𝕜) by
      refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
        (norm_withSeminorms 𝕜 _) _ (fun _ ↦ ⟨{0}, 1, fun f ↦ ?_⟩)
      rw [Seminorm.comp_apply, coe_normSeminorm, coe_to_bcfₗ, one_smul, Finset.sup_singleton,
          ContDiffMapSupportedIn.seminorm_apply,
          BoundedContinuousFunction.norm_le_of_nonempty]
      refine fun x ↦ le_trans ?_ (BoundedContinuousFunction.norm_coe_le_norm _ x)
      rw [BoundedContinuousMapClass.coe_toBoundedContinuousFunction,
          BoundedContinuousMapClass.coe_toBoundedContinuousFunction,
          iteratedFDeriv_apply_of_le, norm_iteratedFDeriv_zero]
      positivity }

set_option profiler true in
set_option trace.Meta.synthInstance true in
lemma test (f : 𝓓^{n}_{K}(E, F)) : ‖iteratedFDeriv_to_bcfₗ 𝕜 0 f‖ = 0 :=
  sorry

#exit


noncomputable def to_bcfL : 𝓓^{n}_{K}(E, F) →L[𝕜] E →ᵇ F :=
  { to_bcfₗ 𝕜 with
    cont := show Continuous (to_bcfₗ 𝕜) by
      refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
        (norm_withSeminorms 𝕜 _) _
        (fun _ ↦ ⟨{0}, 1, fun f ↦ BoundedContinuousFunction.norm_le_of_nonempty.mpr fun x ↦ ?_⟩)
      calc  ‖to_bcfₗ 𝕜 f x‖
        _ = ‖f x‖ := by rw [coe_to_bcfₗ, BoundedContinuousMapClass.coe_toBoundedContinuousFunction]
        _ = ‖iteratedFDeriv ℝ 0 f x‖ := sorry
        _ ≤ ‖iteratedFDeriv_to_bcfₗ 𝕜 0 f‖ := sorry
        _ = ContDiffMapSupportedIn.seminorm 𝕜 E F n K 0 f := sorry
        _ = ((1 : ℝ≥0) • (Finset.sup {0} <| ContDiffMapSupportedIn.seminorm 𝕜 E F n K)) f := sorry }
      --rw [Seminorm.comp_apply, coe_normSeminorm, coe_to_bcfₗ, one_smul, Finset.sup_singleton,
      --    ContDiffMapSupportedIn.seminorm_apply,
      --    BoundedContinuousFunction.norm_le_of_nonempty]
      --refine fun x ↦ le_trans ?_ (BoundedContinuousFunction.norm_coe_le_norm _ x)
      --rw [BoundedContinuousMapClass.coe_toBoundedContinuousFunction,
      --    BoundedContinuousMapClass.coe_toBoundedContinuousFunction,
      --    iteratedFDeriv_apply_of_le, norm_iteratedFDeriv_zero]
      --positivity }

#exit

@[simps!]
noncomputable def iteratedFDerivL (i : ℕ) :
    𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{n-i}_{K}(E, E [×i]→L[ℝ] F) :=
  { iteratedFDerivₗ 𝕜 i with
    cont := show Continuous (iteratedFDerivₗ 𝕜 i) by
      rcases le_or_gt (↑i) n with (hin|hin)
      · refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms 𝕜 E _ _ K)
          (ContDiffMapSupportedIn.withSeminorms 𝕜 E _ _ K) _ (fun k ↦ ⟨{k+i}, 1, fun f ↦ ?_⟩)
        rw [Seminorm.comp_apply, one_smul, Finset.sup_singleton,
            ContDiffMapSupportedIn.seminorm_apply,
            ContDiffMapSupportedIn.seminorm_apply,
            BoundedContinuousFunction.norm_le_of_nonempty]
        refine fun x ↦ le_trans ?_ (BoundedContinuousFunction.norm_coe_le_norm _ x)
        rw [BoundedContinuousMapClass.coe_toBoundedContinuousFunction,
            BoundedContinuousMapClass.coe_toBoundedContinuousFunction,
            iteratedFDeriv_apply_of_le] }

#exit

@[simp]
theorem iteratedFDerivL_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    iteratedFDerivL i f x = if i ≤ n then iteratedFDeriv ℝ i f x else 0 := by
  simp [iteratedFDerivL]

@[simp]
theorem iteratedFDerivL_apply_of_le {i : ℕ} (hin : i ≤ n) (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    iteratedFDerivL i f x = iteratedFDeriv ℝ i f x := by
  rw [iteratedFDerivL_apply]
  exact dif_pos hin

theorem iteratedFDerivL_of_gt {i : ℕ} (hin : i > n) :
    (iteratedFDerivL i : 𝓓^{n}_{K}(E, F) →L[ℝ] (E →ᵇ (E [×i]→L[ℝ] F))) = 0 :=
  ContinuousLinearMap.coe_injective (iteratedFDerivₗ_of_gt hin)

theorem iteratedFDerivL_apply_of_gt {i : ℕ} (hin : i > n) (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    (iteratedFDerivL i f x) = 0 := by
  rw [iteratedFDerivL_apply]
  exact dif_neg (not_le_of_gt hin)

/-- This is mostly for dot notation. Should I keep it? -/
protected noncomputable abbrev iteratedFDeriv (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    E →ᵇ (E [×i]→L[ℝ] F) :=
  iteratedFDerivL i f

protected theorem continuous_iff {X : Type _} [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
  Continuous φ ↔ ∀ (i : ℕ) (_ : ↑i ≤ n), Continuous
    ((ContDiffMapSupportedIn.iteratedFDeriv i) ∘ φ) :=
⟨ fun hφ i _ ↦ (iteratedFDerivL i).continuous.comp hφ,
  fun h ↦ continuous_iInf_rng.mpr fun i ↦ continuous_induced_rng.mpr <| by
    by_cases hin : i ≤ n
    · exact h i hin
    · simpa [iteratedFDerivₗ_of_gt (lt_of_not_ge hin)] using continuous_zero ⟩

variable (E F n K)

protected noncomputable def seminorm (i : ℕ) : Seminorm ℝ 𝓓^{n}_{K}(E, F) :=
  (normSeminorm ℝ <| E →ᵇ (E [×i]→L[ℝ] F)).comp (iteratedFDerivₗ i)

protected noncomputable def seminorm' (i : ℕ) : Seminorm ℝ 𝓓^{n}_{K}(E, F) :=
  (Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm E F n K)

protected theorem withSeminorms :
    WithSeminorms (ContDiffMapSupportedIn.seminorm E F n K) := by
  let p : SeminormFamily ℝ 𝓓^{n}_{K}(E, F) ((_ : ℕ) × Fin 1) :=
    SeminormFamily.sigma fun i ↦ fun _ ↦
      (normSeminorm ℝ (E →ᵇ (E [×i]→L[ℝ] F))).comp (iteratedFDerivₗ i)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
  exact this.congr_equiv (Equiv.sigmaUnique _ _).symm

protected theorem withSeminorms' :
    WithSeminorms (ContDiffMapSupportedIn.seminorm' E F n K) :=
  (ContDiffMapSupportedIn.withSeminorms E F n K).partial_sups

variable {E F n K}

protected theorem seminorm_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.seminorm E F n K i f = ‖f.iteratedFDeriv i‖ :=
  rfl

protected theorem seminorm_eq_bot {i : ℕ} (hin : n < i) :
    ContDiffMapSupportedIn.seminorm E F n K i = ⊥ := by
  ext f
  rw [ContDiffMapSupportedIn.seminorm_apply, ContDiffMapSupportedIn.iteratedFDeriv,
      iteratedFDerivL_of_gt hin, ContinuousLinearMap.zero_apply, norm_zero]
  rfl

end Topology

section fderiv

open Distributions

noncomputable def fderivₗ' (n : ℕ∞) : 𝓓^(n+1)_(K)(E, F) →ₗ[ℝ] 𝓓^{n}_{K}(E, E →L[ℝ] F) where
  toFun f := .of_support_subset (f.contDiff.fderiv_right le_rfl)
    ((support_fderiv_subset ℝ).trans f.tsupport_subset)
  map_add' f₁ f₂ := by
    ext : 1
    exact fderiv_add
      (f₁.contDiff.differentiable le_add_self).differentiableAt
      (f₂.contDiff.differentiable le_add_self).differentiableAt
  map_smul' c f := by
    ext : 1
    exact fderiv_const_smul (f.contDiff.differentiable le_add_self).differentiableAt c

@[simp]
theorem fderivₗ'_apply (n : ℕ∞) (f : 𝓓^(n+1)_(K)(E, F)) (x : E) :
    fderivₗ' n f x = fderiv ℝ f x :=
  rfl

theorem seminorm_fderivₗ' (i : ℕ) (f : 𝓓^(n+1)_(K)(E, F)) :
    ContDiffMapSupportedIn.seminorm E (E →L[ℝ] F) n K i (fderivₗ' n f) =
      ContDiffMapSupportedIn.seminorm E F (n+1) K (i+1) f := by
  rw [ContDiffMapSupportedIn.seminorm_apply, ContDiffMapSupportedIn.seminorm_apply,
      BoundedContinuousFunction.norm_eq_of_nonempty, BoundedContinuousFunction.norm_eq_of_nonempty]
  refine congr_arg _ (Set.ext fun C ↦ forall_congr' fun x ↦ iff_of_eq <| congrArg₂ _ ?_ rfl)
  rcases le_or_gt (i : ℕ∞) n with (hin|hin)
  · have hin' : (i + 1 : ℕ) ≤ n + 1 := add_le_add_right hin _
    rw [iteratedFDerivL_apply_of_le hin, iteratedFDerivL_apply_of_le hin',
        ← norm_iteratedFDeriv_fderiv]
    rfl
  · have hin' : (i + 1 : ℕ) > n + 1 := WithTop.add_lt_add_right WithTop.one_ne_top hin
    rw [iteratedFDerivL_apply_of_gt hin, iteratedFDerivL_apply_of_gt hin', norm_zero, norm_zero]

noncomputable def fderivL' (n : ℕ∞) : 𝓓^(n+1)_(K)(E, F) →L[ℝ] 𝓓^{n}_{K}(E, E →L[ℝ] F) where
  toLinearMap := fderivₗ' n
  cont := by
    refine Seminorm.continuous_from_bounded  (τ₁₂ := RingHom.id ℝ)
      (ContDiffMapSupportedIn.withSeminorms E F (n+1) K)
      (ContDiffMapSupportedIn.withSeminorms E (E →L[ℝ] F) n K) ?_ ?_
    refine fun i ↦ ⟨{i+1}, 1, fun f ↦ ?_⟩
    rw [Finset.sup_singleton, one_smul]
    exact (seminorm_fderivₗ' i f).le

@[simp]
theorem fderivL'_apply (n : ℕ∞) (f : 𝓓^(n+1)_(K)(E, F)) (x : E) :
    fderivL' n f x = fderiv ℝ f x :=
  rfl

section infinite

noncomputable def fderivₗ : 𝓓_(K)(E, F) →ₗ[ℝ] 𝓓_(K)(E, E →L[ℝ] F) :=
  fderivₗ' ⊤

@[simp]
theorem fderivₗ_apply (f : 𝓓_(K)(E, F)) (x : E) : fderivₗ f x = fderiv ℝ f x :=
  rfl

noncomputable def fderivL : 𝓓_(K)(E, F) →L[ℝ] (𝓓_(K)(E, E →L[ℝ] F)) :=
  fderivL' ⊤

@[simp]
theorem fderivL_apply (f : 𝓓_(K)(E, F)) (x : E) :
    fderivL f x = fderiv ℝ f x :=
  rfl

end infinite

end fderiv

section finite

variable {n : ℕ}

protected theorem withSeminorms_of_finite : WithSeminorms
    (fun _ : Fin 1 ↦ (ContDiffMapSupportedIn.seminorm' E F n K n)) := by
  refine (ContDiffMapSupportedIn.withSeminorms E F n K).congr ?_ ?_
  · intro _
    use Finset.Iic n, 1
    rw [one_smul]
    rfl
  · intro i
    use {0}, 1
    rw [one_smul, Finset.sup_singleton, Seminorm.comp_id]
    rcases le_or_gt i n with (hin|hin)
    · rw [← Finset.mem_Iic] at hin
      exact Finset.le_sup (α := Seminorm ℝ 𝓓^{n}_{K}(E, F)) hin
    · rw [ContDiffMapSupportedIn.seminorm_eq_bot (by exact_mod_cast hin)]
      exact bot_le

end finite

end ContDiffMapSupportedIn

instance {E F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {K : Compacts E} : LocallyConvexSpace ℝ 𝓓^{n}_{K}(E, F) :=
  locallyConvexSpace_iInf fun _ ↦ locallyConvexSpace_induced _
