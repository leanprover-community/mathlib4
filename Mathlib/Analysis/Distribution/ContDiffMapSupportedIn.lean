/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Sets.Compacts

/-!

-/

open TopologicalSpace SeminormFamily Set Function Seminorm UniformSpace
open scoped BoundedContinuousFunction Topology NNReal

-- Think `𝕜 = ℝ` or `𝕜 = ℂ`
variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
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

class ContDiffMapSupportedInClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  map_zero_on_compl (f : B) : EqOn f 0 Kᶜ

open ContDiffMapSupportedInClass

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*) (E F : outParam <| Type*)
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
  DFunLike.ext _ _ h

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
  DFunLike.ext' h

theorem _root_.Set.EqOn.comp_left₂ {α β δ γ} {op : α → β → δ} {a₁ a₂ : γ → α} {b₁ b₂ : γ → β} {s : Set γ}
    (ha : s.EqOn a₁ a₂) (hb : s.EqOn b₁ b₂) :
    s.EqOn (fun x ↦ op (a₁ x) (b₁ x)) (fun x ↦ op (a₂ x) (b₂ x)) := fun _ hx =>
  congr_arg₂ _ (ha hx) (hb hx)

instance : Zero 𝓓^{n}_{K}(E, F) where
  zero := ContDiffMapSupportedIn.mk 0 contDiff_zero_fun fun _ _ ↦ rfl

instance : Add 𝓓^{n}_{K}(E, F) where
  add f g := ContDiffMapSupportedIn.mk (f + g) (f.contDiff.add g.contDiff) <| by
    rw [← add_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

instance : Neg 𝓓^{n}_{K}(E, F) where
  neg f := ContDiffMapSupportedIn.mk (-f) (f.contDiff.neg) <| by
    rw [← neg_zero]
    exact f.zero_on_compl.comp_left

-- TODO: actually think about nsmul and zsmul
instance : AddCommGroup 𝓓^{n}_{K}(E, F) where
  add_assoc f₁ f₂ f₃ := by ext; exact add_assoc _ _ _
  add_comm f g := by ext; exact add_comm _ _
  zero_add f := by ext; exact zero_add _
  add_zero f := by ext; exact add_zero _
  neg_add_cancel f := by ext; exact neg_add_cancel _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
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
lemma coe_zero : (0 : 𝓓^{n}_{K}(E, F)) = (0 : E → F) :=
  rfl

@[simp]
lemma zero_apply (x : E) : (0 : 𝓓^{n}_{K}(E, F)) x = 0 :=
  rfl

@[simp]
lemma coe_add (f g : 𝓓^{n}_{K}(E, F)) : (f + g : 𝓓^{n}_{K}(E, F)) = (f : E → F) + g :=
  rfl

@[simp]
lemma add_apply (f g : 𝓓^{n}_{K}(E, F)) (x : E) : (f + g) x = f x + g x :=
  rfl

@[simp]
lemma coe_smul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}_{K}(E, F)) : (c • f : 𝓓^{n}_{K}(E, F)) = c • (f : E → F) :=
  rfl

@[simp]
lemma smul_apply {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
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
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C :=
  Continuous.bounded_above_of_compact_support
    (f.contDiff.continuous_iteratedFDeriv <| (WithTop.le_coe rfl).mpr hi)
    (f.hasCompactSupport.iteratedFDeriv i)

@[simps]
noncomputable def to_bcfₗ : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ F  where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def iteratedFDeriv' (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    𝓓^{n-i}_{K}(E, E [×i]→L[ℝ] F) :=
  if hi : i ≤ n then .of_support_subset
    (f.contDiff.iteratedFDeriv_right <| sorry)--(tsub_add_cancel_of_le hi).le)
    ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
  else 0

@[simp]
lemma iteratedFDeriv'_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    f.iteratedFDeriv' i x = if i ≤ n then iteratedFDeriv ℝ i f x else 0 := by
  rw [ContDiffMapSupportedIn.iteratedFDeriv']
  split_ifs <;> rfl

@[simp]
lemma coe_iteratedFDeriv'_of_le {i : ℕ} (hin : i ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    f.iteratedFDeriv' i = iteratedFDeriv ℝ i f := by
  ext : 1
  rw [iteratedFDeriv'_apply]
  exact dif_pos hin

@[simp]
lemma coe_iteratedFDeriv'_of_gt {i : ℕ} (hin : i > n) (f : 𝓓^{n}_{K}(E, F)) :
    f.iteratedFDeriv' i = 0 := by
  ext : 1
  rw [iteratedFDeriv'_apply]
  exact dif_neg (not_le_of_gt hin)

lemma iteratedFDeriv'_add (i : ℕ) {f g : 𝓓^{n}_{K}(E, F)} :
    (f + g).iteratedFDeriv' i = f.iteratedFDeriv' i + g.iteratedFDeriv' i := by
  ext : 1
  simp only [iteratedFDeriv'_apply, add_apply]
  split_ifs with hin
  · exact iteratedFDeriv_add_apply sorry sorry--(f.contDiff.of_le hin) (g.contDiff.of_le hin)
  · rw [add_zero]

lemma iteratedFDeriv'_smul (i : ℕ) {c : 𝕜} {f : 𝓓^{n}_{K}(E, F)} :
    (c • f).iteratedFDeriv' i = c • f.iteratedFDeriv' i := by
  ext : 1
  simp only [iteratedFDeriv'_apply, RingHom.id_apply, smul_apply]
  split_ifs with hin
  · exact iteratedFDeriv_const_smul_apply sorry -- (f.contDiff.of_le hin)
  · rw [smul_zero]

@[simps]
noncomputable def iteratedFDerivₗ' (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n-i}_{K}(E, E [×i]→L[ℝ] F) where
  toFun f := f.iteratedFDeriv' i
  map_add' _ _ := iteratedFDeriv'_add i
  map_smul' _ _ := iteratedFDeriv'_smul 𝕜 i

lemma iteratedFDeriv'_zero (i : ℕ)  :
    (0 : 𝓓^{n}_{K}(E, F)).iteratedFDeriv' i = 0 :=
  map_zero (iteratedFDerivₗ' ℝ i)

/-- The composition of `ContDiffMapSupportedIn.to_bcfₗ` and
`ContDiffMapSupportedIn.iteratedFDerivₗ`. We define this as a separate `abbrev` because this family
of maps is used a lot for defining and using the topology on `ContDiffMapSupportedIn`, and Lean
takes a long time to infer the type of `to_bcfₗ 𝕜 ∘ₗ iteratedFDerivₗ 𝕜 i`. -/
noncomputable def iteratedFDeriv_to_bcfₗ (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F) :=
  to_bcfₗ 𝕜 ∘ₗ iteratedFDerivₗ' 𝕜 i

section Topology

instance topologicalSpace : TopologicalSpace 𝓓^{n}_{K}(E, F) :=
  ⨅ (i : ℕ), induced (iteratedFDeriv_to_bcfₗ ℝ i) inferInstance

noncomputable instance uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F) := .replaceTopology
  (⨅ (i : ℕ), UniformSpace.comap (iteratedFDeriv_to_bcfₗ ℝ i) inferInstance)
  toTopologicalSpace_iInf.symm

protected theorem uniformSpace_eq_iInf : (uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F)) =
    ⨅ (i : ℕ), UniformSpace.comap (iteratedFDeriv_to_bcfₗ ℝ i)
      inferInstance :=
  UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm

instance : IsUniformAddGroup 𝓓^{n}_{K}(E, F) := by
  rw [ContDiffMapSupportedIn.uniformSpace_eq_iInf]
  refine isUniformAddGroup_iInf (fun i ↦ ?_)
  exact IsUniformAddGroup.comap _

instance : ContinuousSMul 𝕜 𝓓^{n}_{K}(E, F) := by
  refine continuousSMul_iInf (fun i ↦ continuousSMul_induced (iteratedFDeriv_to_bcfₗ 𝕜 i))

instance : LocallyConvexSpace ℝ 𝓓^{n}_{K}(E, F) :=
  locallyConvexSpace_iInf fun _ ↦ locallyConvexSpace_induced _

lemma continuous_iff_comp {X} [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
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

@[simp]
protected theorem seminorm_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.seminorm 𝕜 E F n K i f =
      ‖(f.iteratedFDeriv' i : E →ᵇ (E [×i]→L[ℝ] F))‖ :=
  rfl

protected theorem seminorm_eq_bot {i : ℕ} (hin : n < i) :
    ContDiffMapSupportedIn.seminorm 𝕜 E F n K i = ⊥ := by
  ext f
  rw [ContDiffMapSupportedIn.seminorm_apply,
      coe_iteratedFDeriv'_of_gt hin]
  exact norm_zero

theorem norm_to_bcfₗ (f : 𝓓^{n}_{K}(E, F)) :
    ‖to_bcfₗ 𝕜 f‖ = ContDiffMapSupportedIn.seminorm 𝕜 E F n K 0 f := by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm]
  sorry

@[simps!]
noncomputable def to_bcfL : 𝓓^{n}_{K}(E, F) →L[𝕜] E →ᵇ F :=
  { toLinearMap := to_bcfₗ 𝕜
    cont := show Continuous (to_bcfₗ 𝕜) by
      refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
        (norm_withSeminorms 𝕜 _) _ (fun _ ↦ ⟨{0}, 1, fun f ↦ ?_⟩)
      dsimp only -- TODO: investigate
      rw [Seminorm.comp_apply, coe_normSeminorm, norm_to_bcfₗ, one_smul, Finset.sup_singleton] }

protected theorem continuous_iff {X : Type*} [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ ∀ (i : ℕ) (_ : ↑i ≤ n), Continuous
      (to_bcfₗ 𝕜 ∘ ContDiffMapSupportedIn.iteratedFDeriv' i ∘ φ) := by
  simp_rw [continuous_iInf_rng, continuous_induced_rng]
  constructor <;> intro H i
  · exact fun _ ↦ H i
  · by_cases hin : i ≤ n
    · exact H i hin
    · convert continuous_zero -- TODO: cleanup
      · ext
        rw [Pi.zero_apply]
        simp [iteratedFDeriv_to_bcfₗ, coe_iteratedFDeriv'_of_gt (lt_of_not_ge hin)]
      · infer_instance

end Topology

section fderiv

open Distributions

protected noncomputable def fderiv' (f : 𝓓^{n}_{K}(E, F)) :
    𝓓^{n-1}_{K}(E, E →L[ℝ] F) :=
  if hn : n = 0 then 0 else
    .of_support_subset
    (f.contDiff.fderiv_right <| sorry)
      --(tsub_add_cancel_of_le <| ENat.one_le_iff_ne_zero.mpr hn).le)
    ((support_fderiv_subset ℝ).trans f.tsupport_subset)

@[simp]
lemma fderiv'_apply (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    f.fderiv' x = if n = 0 then 0 else fderiv ℝ f x := by
  rw [ContDiffMapSupportedIn.fderiv']
  split_ifs <;> rfl

@[simp]
lemma coe_fderiv'_of_ne (hn : n ≠ 0) (f : 𝓓^{n}_{K}(E, F)) :
    f.fderiv' = fderiv ℝ f := by
  ext : 1
  rw [fderiv'_apply]
  exact if_neg hn

@[simp]
lemma coe_fderiv'_zero (f : 𝓓^{0}_{K}(E, F)) :
    f.fderiv' = 0 := by
  ext : 1
  rw [fderiv'_apply]
  exact if_pos rfl

@[simps]
noncomputable def fderivₗ' {n : ℕ∞} : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n-1}_{K}(E, E →L[ℝ] F) where
  toFun f := f.fderiv'
  map_add' f₁ f₂ := by
    ext : 1
    simp only [fderiv'_apply, add_apply]
    split_ifs with hn
    · rw [add_zero]
    · rw [← ne_eq, ← ENat.one_le_iff_ne_zero] at hn
      exact fderiv_add
        (f₁.contDiff.differentiable sorry).differentiableAt
        (f₂.contDiff.differentiable sorry).differentiableAt
  map_smul' c f := by
    ext : 1
    simp only [fderiv'_apply, smul_apply]
    split_ifs with hn
    · rw [smul_zero]
    · rw [← ne_eq, ← ENat.one_le_iff_ne_zero] at hn
      exact fderiv_const_smul (f.contDiff.differentiable sorry).differentiableAt c

theorem _root_.ENat.eq_zero_or_add_one (i : ℕ∞) : i = 0 ∨ ∃ k, i = k + 1 := by
  refine or_iff_not_imp_left.mpr fun h ↦ ⟨i - 1, ?_⟩
  sorry
  -- simp only [ENat.one_le_iff_ne_zero, ne_eq, h, tsub_add_cancel_of_le]

theorem seminorm_fderiv' (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.seminorm 𝕜 E (E →L[ℝ] F) (n - 1) K i f.fderiv' =
      ContDiffMapSupportedIn.seminorm 𝕜 E F n K (i+1) f := by
  simp_rw [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.norm_eq_iSup_norm]
  refine iSup_congr fun x ↦ ?_
  rcases eq_or_ne n 0 with rfl|hn
  all_goals sorry
  -- · simp [iteratedFDeriv'_zero]
  -- rcases lt_or_ge (i : ℕ∞) n with (hin|hin)
  -- · have hin' : i + 1 ≤ n := sorry
  --   have hin'' : i ≤ n - 1 := sorry
  --   simp [hin', hin'', hn, ← norm_iteratedFDeriv_fderiv]
  -- · have hin' : i + 1 > n := sorry
  --   simp [hin']
  --   sorry

@[simps! apply]
noncomputable def fderivL' : 𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{n-1}_{K}(E, E →L[ℝ] F) where
  toLinearMap := fderivₗ' 𝕜
  cont := by
    refine Seminorm.continuous_from_bounded  (τ₁₂ := RingHom.id 𝕜)
      (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K)
      (ContDiffMapSupportedIn.withSeminorms 𝕜 E (E →L[ℝ] F) (n-1) K) _
      fun i ↦ ⟨{i+1}, 1, fun f ↦ ?_⟩
    dsimp only -- TODO: cleanup
    rw [Seminorm.comp_apply, one_smul, Finset.sup_singleton, fderivₗ'_apply, seminorm_fderiv']

section infinite

protected noncomputable def iteratedFDeriv (i : ℕ) (f : 𝓓_{K}(E, F)) : 𝓓_{K}(E, E [×i]→L[ℝ] F) :=
  (f.iteratedFDeriv' i).copy (iteratedFDeriv ℝ i f) (coe_iteratedFDeriv'_of_le le_top f)

lemma iteratedFDeriv_eq_iteratedFDeriv' (i : ℕ) (f : 𝓓_{K}(E, F)) :
    f.iteratedFDeriv i = f.iteratedFDeriv' i :=
  (f.iteratedFDeriv' i).copy_eq _ _

@[simp]
lemma iteratedFDeriv_apply (i : ℕ) (f : 𝓓_{K}(E, F)) (x : E) :
    f.iteratedFDeriv i x = iteratedFDeriv ℝ i f x := by
  rfl

@[simps! apply]
noncomputable def iteratedFDerivₗ (i : ℕ) : 𝓓_{K}(E, F) →ₗ[𝕜] 𝓓_{K}(E, E [×i]→L[ℝ] F) :=
  (iteratedFDerivₗ' 𝕜 i).copy (ContDiffMapSupportedIn.iteratedFDeriv i) <| funext <|
    iteratedFDeriv_eq_iteratedFDeriv' i

protected noncomputable def fderiv (f : 𝓓_{K}(E, F)) : 𝓓_{K}(E, E →L[ℝ] F) :=
  f.fderiv'.copy (fderiv ℝ f) (coe_fderiv'_of_ne (by decide) f)

lemma fderiv_eq_fderiv' (f : 𝓓_{K}(E, F)) : f.fderiv = f.fderiv' :=
  f.fderiv'.copy_eq _ _

@[simp]
lemma fderiv_apply (f : 𝓓_{K}(E, F)) (x : E) :
    f.fderiv x = fderiv ℝ f x := by
  rfl

@[simps! apply]
noncomputable def fderivₗ : 𝓓_{K}(E, F) →ₗ[𝕜] 𝓓_{K}(E, E →L[ℝ] F) :=
  (fderivₗ' 𝕜).copy ContDiffMapSupportedIn.fderiv <| funext fderiv_eq_fderiv'

@[simps! apply]
noncomputable def fderivL : 𝓓_{K}(E, F) →L[𝕜] 𝓓_{K}(E, E →L[ℝ] F) :=
  (fderivL' 𝕜).copy ContDiffMapSupportedIn.fderiv <| funext fderiv_eq_fderiv'

end infinite

end fderiv

section finite

variable {n : ℕ}

protected theorem withSeminorms_of_finite : WithSeminorms
    (fun _ : Fin 1 ↦ (ContDiffMapSupportedIn.seminorm' 𝕜 E F n K n)) := by
  refine (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).congr ?_ ?_
  · intro _
    use Finset.Iic n, 1
    rw [one_smul]
    rfl
  · intro i
    use {0}, 1
    rw [one_smul, Finset.sup_singleton, Seminorm.comp_id]
    rcases le_or_gt i n with (hin|hin)
    · rw [← Finset.mem_Iic] at hin
      exact Finset.le_sup (α := Seminorm 𝕜 𝓓^{n}_{K}(E, F)) hin
    · rw [ContDiffMapSupportedIn.seminorm_eq_bot 𝕜 (by norm_cast)]
      exact bot_le

end finite

end ContDiffMapSupportedIn

instance {E F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {K : Compacts E} : LocallyConvexSpace ℝ 𝓓^{n}_{K}(E, F) :=
  locallyConvexSpace_iInf fun _ ↦ locallyConvexSpace_induced _
