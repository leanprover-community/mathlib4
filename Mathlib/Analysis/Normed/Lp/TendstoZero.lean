/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-! # The space `c₀` of sequences tending to zero -/

@[expose] public section

open scoped ENNReal NNReal Topology
open Filter

variable {ι 𝕜 : Type*} {E : ι → Type*}

section NormedRing

variable [NormedRing 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]

namespace lp

variable (E) in
/-- The additive subgroup of `lp E ∞` consisting of those sequences whose norms converge
to zero. This has the notation `c₀ E` in the scope `tendstoZero`. In the special case
where `E := fun _ : ι ↦ 𝕜`, the notation `c₀(ι, 𝕜)` is available. -/
def tendstoZero : AddSubgroup (lp E ∞) where
  carrier := {x | Tendsto (‖x ·‖) cofinite (𝓝 0)}
  add_mem' {x y} hx hy := tendsto_const_nhds.squeeze
    (by simpa using hx.add hy) (by simp [Pi.le_def]) (fun _ ↦ norm_add_le ..)
  zero_mem' := by simpa using tendsto_const_nhds
  neg_mem' := by simp

end lp

@[inherit_doc]
scoped[tendstoZero] notation "c₀" => lp.tendstoZero
@[inherit_doc]
scoped[tendstoZero] notation "c₀(" ι ", " 𝕜 ")" => lp.tendstoZero (fun _ : ι ↦ 𝕜)

open scoped tendstoZero lp

lemma lp.mem_tendstoZero_iff (x : lp E ∞) :
    x ∈ c₀ E ↔ Tendsto (‖x ·‖) cofinite (𝓝 0) :=
  Iff.rfl

namespace lp.tendstoZero

instance instDFunLike : DFunLike (c₀ E) ι E where
  coe x := ⇑(x : lp E ∞)
  coe_injective := DFunLike.coe_injective.comp Subtype.coe_injective

@[simp, norm_cast]
lemma coeFn_coe (x : c₀ E) : ⇑(x : lp E ∞) = ⇑x :=
  rfl

@[simp]
lemma coeFn_subtype_mk (x : lp E ∞) (hx : x ∈ c₀ E) : ⇑(⟨x, hx⟩ : c₀ E) = ⇑x :=
  rfl

@[ext]
lemma ext {x y : c₀ E} (h : ∀ i, x i = y i) : x = y :=
  DFunLike.ext x y h

instance : IsZeroApply (c₀ E) where
instance : IsAddApply (c₀ E) where
instance : IsNegApply (c₀ E) where
instance : IsSubApply (c₀ E) where

/-- Constructor for a term of `c₀ E` which doesn't force the user to pass through `lp E ∞`. -/
def mk (f : (i : ι) → E i) (h : Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0)) : c₀ E :=
  ⟨lp.mk f (memℓp_infty h.bddAbove_range_of_cofinite), h⟩

@[simp]
lemma coeFn_mk (f : (i : ι) → E i) (h : Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0)) :
    ⇑(mk f h) = f :=
  rfl

instance isClosed : IsClosed (c₀ E : Set (lp E ∞)) :=
  LipschitzWith.uniformEquicontinuous (fun i (x : lp E ∞) ↦ ‖x i‖) 1 (fun i ↦ by
    simpa [Function.comp_def] using lipschitzWith_one_norm.comp (lp.lipschitzWith_one_eval ∞ i))
    |>.equicontinuous.isClosed_setOfPred_tendsto continuous_const

instance [∀ i, CompleteSpace (E i)] : CompleteSpace (c₀ E) :=
  completeSpace_coe_iff_isComplete.mpr isClosed.isComplete

noncomputable instance : NormedAddCommGroup (c₀ E) := AddSubgroup.normedAddCommGroup

noncomputable instance : SMul 𝕜 (c₀ E) where
  smul k x := ⟨k • x, squeeze_zero (fun _ ↦ by positivity)
    (fun i ↦ norm_smul_le k (x i)) <| by simpa using Tendsto.const_mul ‖k‖ x.property⟩

@[simp]
lemma coe_smul (k : 𝕜) (x : c₀ E) : ↑(k • x) = k • (x : lp E ∞) := rfl

instance : IsSMulApply 𝕜 (c₀ E) where

noncomputable instance : Module 𝕜 (c₀ E) := fast_instance%
  Subtype.val_injective.module 𝕜 (c₀ E).subtype fun _ _ ↦ rfl

instance : IsBoundedSMul 𝕜 (c₀ E) := .of_norm_smul_le (fun _ _ ↦ norm_smul_le _ (_ : lp E ∞))

noncomputable instance {𝕜 : Type*} [NormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (c₀ E) where
  norm_smul_le := norm_smul_le

section MoreScalars

variable {𝕜' : Type*} [NormedRing 𝕜'] [∀ i, Module 𝕜' (E i)] [∀ i, IsBoundedSMul 𝕜' (E i)]

instance [∀ i, SMulCommClass 𝕜' 𝕜 (E i)] : SMulCommClass 𝕜' 𝕜 (c₀ E) :=
  ⟨fun _ _ _ ↦ Subtype.ext <| smul_comm _ _ _⟩

instance [SMul 𝕜' 𝕜] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] : IsScalarTower 𝕜' 𝕜 (c₀ E) :=
  ⟨fun _ _ _ ↦ Subtype.ext <| smul_assoc _ _ _⟩

instance [∀ i, Module 𝕜ᵐᵒᵖ (E i)] [∀ i, IsCentralScalar 𝕜 (E i)] : IsCentralScalar 𝕜 (c₀ E) :=
  ⟨fun _ _ ↦ Subtype.ext <| op_smul_eq_smul _ _⟩

end MoreScalars

variable (𝕜 E) in
/-- The embedding of `c₀ E` into `lp E ∞` as a linear isometry. -/
def subtypeₗᵢ : c₀ E →ₗᵢ[𝕜] lp E ∞ where
  toFun := (↑)
  map_add' := by simp
  map_smul' := by simp
  norm_map' _ := rfl

variable (𝕜 E) in
/-- `c₀ E` as a `𝕜`-submodule of `lp E ∞`. -/
def toSubmodule : Submodule 𝕜 (lp E ∞) :=
  { c₀ E with
    smul_mem' c x hx := c • (⟨x, hx⟩ : c₀ E) |>.property }

@[simp]
lemma toAddSubgroup_toSubmodule : (toSubmodule 𝕜 E).toAddSubgroup = c₀ E := rfl

variable (𝕜 E) in
/-- The linear isometry equivalence between `c₀ E` and itself, viewed as a
submodule of `lp E ∞` (as opposed to only an `AddSubgroup`). -/
noncomputable def toSubmoduleLinearIsometryEquiv : toSubmodule 𝕜 E ≃ₗᵢ[𝕜] c₀ E :=
  LinearIsometryEquiv.refl ..

end lp.tendstoZero

namespace lp

variable {p : ℝ≥0∞}

@[simp]
lemma coeFn_inclusion {q : ℝ≥0∞} (h : lp E p ≤ lp E q) (f : lp E p) :
    ⇑(AddSubgroup.inclusion h f) = ⇑f :=
  rfl

variable (E) in
lemma range_inclusion_le_tendstoZero (hp : p < ∞) :
    (AddSubgroup.inclusion (lp.monotone hp.le)).range ≤ c₀ E := by
  rintro - ⟨x, rfl⟩
  simp only [mem_tendstoZero_iff, lp.coeFn_inclusion]
  obtain (rfl | hp') := eq_zero_or_pos p
  · exact tendsto_nhds_of_eventually_eq <| by simpa using memℓp_zero_iff.mp <| lp.memℓp x
  have hp'' := ENNReal.toReal_pos_iff.mpr ⟨hp', hp⟩
  have := lp.memℓp x |>.summable hp'' |>.tendsto_cofinite_zero
    |>.rpow_const (p := p.toReal⁻¹) (by aesop)
  rw [Real.zero_rpow (inv_pos.mpr hp'').ne'] at this
  convert this with i
  rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hp''.ne', Real.rpow_one]

variable (𝕜 E) in
lemma range_linearMapOfLE_le_tendstoZero (hp : p < ∞) :
    LinearMap.range (linearMapOfLE 𝕜 E (le_top (a := p))) ≤ tendstoZero.toSubmodule 𝕜 E := by
  simpa [← Submodule.toAddSubgroup_le, LinearMap.range_toAddSubgroup]
    using range_inclusion_le_tendstoZero E hp

end lp

namespace lp.tendstoZero

variable [DecidableEq ι]

lemma single_mem (i : ι) (c : E i) :
    lp.single ∞ i c ∈ c₀ E :=
  lp.range_inclusion_le_tendstoZero E ENNReal.zero_lt_top ⟨lp.single 0 i c, by ext; simp⟩

/-- `lp.single` as an element of `c₀ E`. -/
def single (i : ι) (c : E i) : c₀ E :=
  ⟨lp.single ∞ i c, single_mem i c⟩

@[simp]
lemma coe_single (i : ι) (c : E i) :
    (tendstoZero.single i c : lp E ∞) = lp.single ∞ i c :=
  rfl

@[simp]
lemma coeFn_single (i : ι) (c : E i) : ⇑(single i c) = Pi.single i c :=
  lp.coeFn_single ∞ i c

lemma smul_single (i : ι) (c : 𝕜) (x : E i) :
    c • single i x = single i (c • x) := by
  ext; simp [single]

lemma hasSum_single (x : c₀ E) :
    HasSum (fun i ↦ single i (x i)) x := by
  have hx := mem_tendstoZero_iff _ |>.mp x.property
  rw [HasSum]
  rw [Metric.nhds_basis_closedBall.tendsto_right_iff] at hx ⊢
  gconvert hx with ε hε hx
  rw [Filter.eventually_cofinite] at hx
  simp only [Metric.mem_closedBall, dist_zero_right, norm_norm, not_le] at hx
  filter_upwards [Filter.Ici_mem_atTop hx.toFinset] with s hs
  simp only [Metric.mem_closedBall, dist_eq_norm]
  refine lp.norm_le_of_forall_le hε.le fun i ↦ ?_
  by_cases hi : i ∈ s
  · simpa [hi] using hε.le
  · simpa [hi] using Set.notMem_subset hs hi

end lp.tendstoZero

lemma lp.topologicalClosure_range_inclusion_eq_tendstoZero {p : ℝ≥0∞} (hp : p < ∞) :
    (AddSubgroup.inclusion (lp.monotone hp.le)).range.topologicalClosure = c₀ E := by
  classical
  refine le_antisymm (AddSubgroup.topologicalClosure_minimal _
    (range_inclusion_le_tendstoZero E hp) tendstoZero.isClosed) fun x hx ↦ ?_
  rw [← SetLike.mem_coe, AddSubgroup.topologicalClosure_coe]
  refine mem_closure_of_tendsto ((tendstoZero.hasSum_single ⟨x, hx⟩).map (c₀ E).subtype
    continuous_subtypeVal) <| .of_forall fun s ↦ sum_mem fun i _ ↦ ?_
  exact ⟨lp.single p i (x i), by ext; simp⟩

end NormedRing

section NontriviallyNormedField

open scoped tendstoZero lp

variable {F : ι → Type*}
variable [NontriviallyNormedField 𝕜]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedSpace 𝕜 (F i)]

/-- `c₀ E` is invariant under `lp.mapCLM`. -/
lemma lp.mapCLM_mem_tendstoZero (T : ∀ i, E i →L[𝕜] F i)
    {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) (x : lp E ∞) (hx : x ∈ c₀ E) :
    lp.mapCLM ∞ T hK hTK x ∈ c₀ F :=
  tendsto_const_nhds.squeeze (mul_zero K ▸ hx.const_mul K) (fun _ ↦ by simp)
    fun i ↦ (T i).le_of_opNorm_le (hTK i) _

/-- A uniformly bounded family of continuous linear maps, as a continuous linear map
on the `c₀` space. -/
@[simps!]
noncomputable def lp.tendstoZero.mapCLM (T : ∀ i, E i →L[𝕜] F i)
    {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    c₀ E →L[𝕜] c₀ F :=
  letI e₁ := lp.tendstoZero.subtypeₗᵢ 𝕜 E |>.toContinuousLinearMap
  letI e₂ := lp.mapCLM ∞ T hK hTK
  letI e₃ := lp.tendstoZero.toSubmoduleLinearIsometryEquiv 𝕜 F
    |>.symm.toContinuousLinearEquiv.toContinuousLinearMap
  e₃ ∘L ((e₂ ∘L e₁).codRestrict (lp.tendstoZero.toSubmodule 𝕜 F)
    fun x ↦ lp.mapCLM_mem_tendstoZero T hK hTK x.val x.property)

end NontriviallyNormedField

section Dual

open scoped tendstoZero lp

variable [RCLike 𝕜]

namespace lp.tendstoZero

variable (ι 𝕜) in
/-- The natural continuous linear map from `ℓ¹(ι, 𝕜)` into the (strong) dual of `c₀(ι, 𝕜)`
given by `fun x y ↦ ∑' i, y i * x i`. The order of the factors is reversed because this is
implemented via the `lp.scalarDualPairing` of `ℓ^∞` with `ℓ¹`, precomposed with the inclusion of
`c₀(ι, 𝕜)` into `ℓ^∞(ι, 𝕜)`. -/
noncomputable def lpOneToStrongDual :
    ℓ¹(ι, 𝕜) →L[𝕜] StrongDual 𝕜 c₀(ι, 𝕜) :=
  .flip <| lp.scalarDualPairing ι 𝕜 ∞ 1 ∘L (subtypeₗᵢ 𝕜 _).toContinuousLinearMap

lemma lpOneToStrongDual_apply_apply (x : ℓ¹(ι, 𝕜)) (y : c₀(ι, 𝕜)) :
    lpOneToStrongDual ι 𝕜 x y = ∑' i, (y : ℓ^∞(ι, 𝕜)) i * x i :=
  rfl

lemma norm_lpOneToStrongDual_apply_le (x : ℓ¹(ι, 𝕜)) :
    ‖lpOneToStrongDual ι 𝕜 x‖ ≤ ‖x‖ := by
  refine (lpOneToStrongDual ι 𝕜 x).opNorm_le_bound (by positivity) fun φ ↦ ?_
  rw [mul_comm, ← one_mul ‖φ‖]
  apply lp.scalarDualPairing ι 𝕜 ∞ 1 |>.le_opNorm₂ .. |>.trans
  gcongr
  · exact lp.norm_scalarDualPairing_le
  · exact le_rfl

lemma norm_lpOneToStrongDual_le : ‖lpOneToStrongDual ι 𝕜‖ ≤ 1 :=
  lpOneToStrongDual ι 𝕜 |>.opNorm_le_bound (by positivity) fun x ↦ by
    simpa only [one_mul] using norm_lpOneToStrongDual_apply_le x

open ComplexOrder in
lemma sum_strongDual_eval_single_le_norm [DecidableEq ι]
    (φ : StrongDual 𝕜 c₀(ι, 𝕜)) (s : Finset ι) :
    ∑ i ∈ s, ‖φ (single i 1)‖ ≤ ‖φ‖ := by
  rw [← RCLike.ofReal_le_ofReal (K := 𝕜), RCLike.ofReal_sum]
  have (c : 𝕜) : (‖c‖ : 𝕜) = (‖c‖ * c⁻¹) • c := by
    obtain (rfl | hc) := eq_or_ne c 0
    · simp
    · simp [hc]
  have h₁ : (∑ x ∈ s, ‖φ (single x 1)‖ : 𝕜) =
      φ (∑ x ∈ s, (‖φ (single x 1)‖ * (φ (single x 1))⁻¹) • single x 1) := by
    refine .trans ?_ (map_sum φ _ s).symm
    exact s.sum_congr rfl fun x _ ↦ by rw [map_smul, ← this]
  have := RCLike.norm_of_nonneg' (K := 𝕜) (h₁ ▸ s.sum_nonneg (by simp))
  rw [h₁, ← this, RCLike.ofReal_le_ofReal, ← mul_one ‖φ‖]
  refine φ.le_opNorm_of_le ?_
  simp only [AddSubgroup.coe_norm, AddSubgroup.val_finsetSum, coe_smul, coe_single]
  refine lp.norm_le_of_forall_le (by positivity) fun i ↦ ?_
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_single, Pi.single_apply, smul_eq_mul]
  by_cases! hi : i ∈ s
  · rw [s.sum_eq_single_of_mem i hi fun b _ hb ↦ by simp [hb.symm]]
    obtain (h | h) := eq_or_ne (φ (single i 1)) 0
    all_goals simp [h]
  · rw [s.sum_eq_zero]
    · simp
    · intro j hj
      have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
      simp [hij]

lemma strongDual_eval_single_memℓp_one [DecidableEq ι]
    (φ : StrongDual 𝕜 c₀(ι, 𝕜)) :
    Memℓp (fun i ↦ φ (single i 1)) 1 :=
  memℓp_gen' <| by simpa only [ENNReal.toReal_one, Real.rpow_one]
    using sum_strongDual_eval_single_le_norm φ

/-- The map from the (strong) dual of `c₀(ι, 𝕜)` to `ℓ¹(ι, 𝕜)` given by
`fun φ i ↦ φ (single i 1)`. This is the inverse of `lp.tendstoZero.lpOneToStrongDual`. -/
@[simps]
noncomputable def strongDualTolpOne [DecidableEq ι]
    (φ : StrongDual 𝕜 c₀(ι, 𝕜)) : ℓ¹(ι, 𝕜) :=
  ⟨fun i ↦ φ (single i 1), strongDual_eval_single_memℓp_one φ⟩

lemma norm_strongDualTolpOne_apply_le [DecidableEq ι]
    (φ : StrongDual 𝕜 c₀(ι, 𝕜)) : ‖strongDualTolpOne φ‖ ≤ ‖φ‖ :=
  lp.norm_le_of_forall_sum_le (by simp) (by positivity) <| by
    simpa using sum_strongDual_eval_single_le_norm φ

variable (ι 𝕜) in
/-- The (inverse) maps `lp.tendstoZero.lpOneToStrongDual` and `lp.tendstoZero.strongDualTolpOne`
bundled into a linear equivalence. See `lp.tendstoZero.lpOneToStrongDualₗᵢ` for the linear isometry
equivalence. -/
@[simps!]
noncomputable def lpOneToStrongDualLinearEquiv [DecidableEq ι] :
    ℓ¹(ι, 𝕜) ≃ₗ[𝕜] StrongDual 𝕜 c₀(ι, 𝕜) :=
  { (lpOneToStrongDual ι 𝕜).toLinearMap with
    invFun := strongDualTolpOne
    left_inv x := by
      ext i
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe,
        strongDualTolpOne_coe, lpOneToStrongDual_apply_apply]
      rw [tsum_eq_single i (fun j hj ↦ by simp [hj])]
      simp
    right_inv φ := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
      ext x
      simp only [lpOneToStrongDual_apply_apply, strongDualTolpOne_coe]
      simp_rw [← smul_eq_mul, ← map_smul, smul_single, smul_eq_mul, mul_one]
      exact φ.hasSum (hasSum_single x) |>.tsum_eq }

variable (ι 𝕜) in
/-- The linear isometry equivalence between `ℓ¹(ι, 𝕜)` and the (strong) dual of `c₀(ι, 𝕜)`.
In the forward direction, this is given by `fun x y ↦ ∑' i, y i * x i`, and in the
backward direction by `fun φ i ↦ φ (single i 1)`. -/
@[simps!]
noncomputable def lpOneToStrongDualₗᵢ [DecidableEq ι] :
    ℓ¹(ι, 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 c₀(ι, 𝕜) :=
  .ofBounds (lpOneToStrongDualLinearEquiv ι 𝕜) norm_lpOneToStrongDual_apply_le
    norm_strongDualTolpOne_apply_le

end lp.tendstoZero

end Dual
