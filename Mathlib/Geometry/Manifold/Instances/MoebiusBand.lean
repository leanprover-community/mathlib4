/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.Orientation
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The Möbius band

This file defines the (open) Möbius band as the total space of a non-trivial real line bundle
over the circle and proves that it is a smooth manifold that is not orientable.

## Construction

We cover `Circle` by two open sets `U₀ = {z | z ≠ -1}` and `U₁ = {z | z ≠ 1}` and build a
`VectorBundleCore ℝ Circle ℝ (ZMod 2)` whose coordinate change on the overlap `U₀ ∩ U₁` is
the identity on the upper semicircle and negation on the lower semicircle. The resulting total
space inherits a `C^n` manifold structure from Mathlib's vector bundle infrastructure.

## Main results

* `moebiusBundleCore` : the `VectorBundleCore` defining the Möbius line bundle.
* `MoebiusBand` : the type of the Möbius band as a `Bundle.TotalSpace`.
* `MoebiusBand.isManifold` : the Möbius band is a smooth manifold.
* `MoebiusBand.connectedSpace` : the Möbius band is connected.
* `MoebiusBand.not_orientable` : the Möbius band is not orientable.
-/

@[expose] public section

noncomputable section

open scoped Manifold
open Set Complex

/-! ### Circle helpers -/

instance : ConnectedSpace Circle :=
  Subtype.connectedSpace (isConnected_sphere
    (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1))

namespace Circle

/-- The point `-1` on the circle. -/
def negOne : Circle := ⟨-1, by simp [Submonoid.unitSphere]⟩

@[simp]
theorem coe_negOne : (negOne : ℂ) = -1 := rfl

theorem one_ne_negOne : (1 : Circle) ≠ negOne := by
  intro h; have := congr_arg Subtype.val h; norm_num [negOne, coe_one] at this

/-- On `Circle`, `z ≠ 1` and `z ≠ -1` implies `(z : ℂ).im ≠ 0`. -/
theorem im_ne_zero_of_ne {z : Circle} (h1 : z ≠ 1) (h2 : z ≠ negOne) : (z : ℂ).im ≠ 0 := by
  intro him
  have hnsq : normSq (z : ℂ) = 1 := by rw [normSq_eq_norm_sq]; simp [norm_coe z]
  rw [normSq_apply] at hnsq; simp only [him, mul_zero, add_zero] at hnsq
  rcases mul_self_eq_one_iff.mp hnsq with hre | hre
  · exact h1 (Subtype.ext (Complex.ext hre him))
  · exact h2 (Subtype.ext (Complex.ext (by simpa using hre) (by simpa using him)))

end Circle

/-! ### Möbius bundle core -/

namespace MoebiusBand

/-- The first open set in the cover: `Circle` minus `-1`. -/
def U₀ : Set Circle := {z | z ≠ Circle.negOne}

/-- The second open set in the cover: `Circle` minus `1`. -/
def U₁ : Set Circle := {z | z ≠ 1}

theorem isOpen_U₀ : IsOpen U₀ := isOpen_ne
theorem isOpen_U₁ : IsOpen U₁ := isOpen_ne

theorem U₀_union_U₁ : U₀ ∪ U₁ = univ := by
  ext z; simp only [mem_union, mem_setOf_eq, mem_univ, iff_true, U₀, U₁]
  by_contra h; push_neg at h
  exact Circle.one_ne_negOne (h.2.symm ▸ h.1)

/-- The base sets for the Möbius bundle, indexed by `ZMod 2`. -/
def baseSet : ZMod 2 → Set Circle
  | 0 => U₀
  | 1 => U₁

/-- The coordinate change function for the Möbius bundle.
On the diagonal it is the identity. Off-diagonal, it is the identity on the upper
semicircle (`im z > 0`) and negation on the lower semicircle (`im z < 0`). -/
def coordChange : ZMod 2 → ZMod 2 → Circle → ℝ →L[ℝ] ℝ
  | 0, 0, _ | 1, 1, _ => ContinuousLinearMap.id ℝ ℝ
  | 0, 1, z | 1, 0, z =>
    if 0 < (z : ℂ).im then ContinuousLinearMap.id ℝ ℝ
    else -ContinuousLinearMap.id ℝ ℝ

/-- On the overlap `U₀ ∩ U₁`, the off-diagonal coordinate change is continuous (it is in fact
locally constant, taking the values `id` and `-id` on the upper/lower semicircles). -/
private theorem continuousOn_coordChange_off_diag :
    ContinuousOn (fun z : Circle =>
      if 0 < (z : ℂ).im then ContinuousLinearMap.id ℝ ℝ
      else -ContinuousLinearMap.id ℝ ℝ)
      (U₀ ∩ U₁) := by
  apply continuousOn_of_locally_continuousOn
  intro z hz
  have hne : (z : ℂ).im ≠ 0 := Circle.im_ne_zero_of_ne hz.2 hz.1
  by_cases him : 0 < (z : ℂ).im
  · exact ⟨{w : Circle | 0 < (w : ℂ).im},
      isOpen_lt continuous_const (continuous_im.comp continuous_subtype_val), him,
      continuousOn_const.congr fun w hw => if_pos hw.2⟩
  · exact ⟨{w : Circle | (w : ℂ).im < 0},
      isOpen_lt (continuous_im.comp continuous_subtype_val) continuous_const,
      lt_of_le_of_ne (not_lt.mp him) hne,
      continuousOn_const.congr fun w hw => if_neg (not_lt.mpr (le_of_lt hw.2))⟩

end MoebiusBand

/-- The `VectorBundleCore` defining the Möbius line bundle over the circle.

Two charts cover `Circle`: `U₀ = {z | z ≠ -1}` and `U₁ = {z | z ≠ 1}`. On the overlap
`U₀ ∩ U₁` (which decomposes into the upper and lower open semicircles), the coordinate change
is the identity on the upper semicircle and negation on the lower semicircle. -/
def moebiusBundleCore : VectorBundleCore ℝ Circle ℝ (ZMod 2) where
  baseSet := MoebiusBand.baseSet
  isOpen_baseSet i := by fin_cases i <;> exact isOpen_ne
  indexAt z := by classical exact if z = Circle.negOne then 1 else 0
  mem_baseSet_at z := by
    simp only [MoebiusBand.baseSet]
    split_ifs with h
    · simp [MoebiusBand.U₁, h, Circle.one_ne_negOne.symm]
    · exact h
  coordChange := MoebiusBand.coordChange
  coordChange_self i z _ v := by fin_cases i <;> simp [MoebiusBand.coordChange]
  continuousOn_coordChange i j := by
    fin_cases i <;> fin_cases j <;> simp only [MoebiusBand.baseSet]
    · exact continuousOn_const
    · exact MoebiusBand.continuousOn_coordChange_off_diag
    · rw [show MoebiusBand.U₁ ∩ MoebiusBand.U₀ = MoebiusBand.U₀ ∩ MoebiusBand.U₁
        from inter_comm _ _]
      exact MoebiusBand.continuousOn_coordChange_off_diag
    · exact continuousOn_const
  coordChange_comp i j k z hz v := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [MoebiusBand.coordChange] <;> split <;> simp

/-! ### The Möbius band -/

/-- The Möbius band, defined as the total space of the Möbius line bundle over `Circle`. -/
abbrev MoebiusBand : Type := Bundle.TotalSpace ℝ moebiusBundleCore.Fiber

namespace MoebiusBand

open Manifold

/-! ### Smooth manifold structure -/

/-- The coordinate changes of the Möbius bundle are smooth. -/
instance isContMDiff : moebiusBundleCore.IsContMDiff (𝓡 1) ⊤ where
  contMDiffOn_coordChange i j := by
    fin_cases i <;> fin_cases j <;> simp only [moebiusBundleCore, MoebiusBand.baseSet]
    · exact contMDiffOn_const
    · -- (0,1): locally constant on U₀ ∩ U₁
      apply contMDiffOn_of_locally_contMDiffOn
      intro z hz
      have hne : (z : ℂ).im ≠ 0 := Circle.im_ne_zero_of_ne hz.2 hz.1
      by_cases him : 0 < (z : ℂ).im
      · exact ⟨{w | 0 < (w : ℂ).im},
          isOpen_lt continuous_const (continuous_im.comp continuous_subtype_val), him,
          contMDiffOn_const.congr fun w hw => if_pos hw.2⟩
      · exact ⟨{w | (w : ℂ).im < 0},
          isOpen_lt (continuous_im.comp continuous_subtype_val) continuous_const,
          lt_of_le_of_ne (not_lt.mp him) hne,
          contMDiffOn_const.congr fun w hw => if_neg (not_lt.mpr (le_of_lt hw.2))⟩
    · -- (1,0): same as (0,1) but on U₁ ∩ U₀
      apply contMDiffOn_of_locally_contMDiffOn
      intro z hz
      have hne : (z : ℂ).im ≠ 0 := Circle.im_ne_zero_of_ne hz.1 hz.2
      by_cases him : 0 < (z : ℂ).im
      · exact ⟨{w | 0 < (w : ℂ).im},
          isOpen_lt continuous_const (continuous_im.comp continuous_subtype_val), him,
          contMDiffOn_const.congr fun w hw => if_pos hw.2⟩
      · exact ⟨{w | (w : ℂ).im < 0},
          isOpen_lt (continuous_im.comp continuous_subtype_val) continuous_const,
          lt_of_le_of_ne (not_lt.mp him) hne,
          contMDiffOn_const.congr fun w hw => if_neg (not_lt.mpr (le_of_lt hw.2))⟩
    · exact contMDiffOn_const

/-- The Möbius band is a smooth manifold. -/
instance isManifold : IsManifold ((𝓡 1).prod 𝓘(ℝ, ℝ)) ⊤ MoebiusBand :=
  inferInstance

/-! ### Connectedness -/

/-- The Möbius band is connected. -/
instance connectedSpace : ConnectedSpace MoebiusBand := by
  rw [connectedSpace_iff_univ]
  set Z := moebiusBundleCore with hZ
  have hcover : (univ : Set MoebiusBand) = ⋃ b : Circle,
      (range (Bundle.zeroSection ℝ Z.Fiber) ∪
        range (Bundle.TotalSpace.mk (F := ℝ) (E := Z.Fiber) b)) := by
    ext ⟨b, v⟩
    simp only [mem_univ, mem_iUnion, mem_union, mem_range, true_iff]
    exact ⟨b, Or.inr ⟨v, rfl⟩⟩
  rw [hcover]
  constructor
  · exact ⟨Bundle.zeroSection ℝ Z.Fiber 1, mem_iUnion.mpr ⟨1, Or.inl ⟨1, rfl⟩⟩⟩
  · apply IsPreconnected.iUnion_of_reflTransGen
    · intro b
      apply IsPreconnected.union (Bundle.zeroSection ℝ Z.Fiber b)
      · exact ⟨b, rfl⟩
      · exact ⟨(0 : Z.Fiber b), rfl⟩
      · exact (isConnected_range
          (Bundle.contMDiff_zeroSection (n := ⊤) ℝ Z.Fiber (IB := 𝓡 1)).continuous).isPreconnected
      · exact (isConnected_range
          (FiberBundle.continuous_totalSpaceMk ℝ Z.Fiber b)).isPreconnected
    · intro i j
      apply Relation.ReflTransGen.single
      exact ⟨Bundle.zeroSection ℝ Z.Fiber 1, Or.inl ⟨1, rfl⟩, Or.inl ⟨1, rfl⟩⟩

/-! ### Non-orientability -/

/-- The derivative of a product map `(x, y) ↦ (f x, L y)` factors as `(Df).prodMap L`,
so its determinant equals `det(Df) * det(L)`. -/
private theorem det_fderiv_prodMap {E' F' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
    {f : E' → E'} {L : F' →L[ℝ] F'} {x₀ : E'} {y₀ : F'}
    (hf : DifferentiableAt ℝ f x₀) :
    LinearMap.det (fderiv ℝ (fun p : E' × F' ↦ (f p.1, L p.2)) (x₀, y₀) :
        E' × F' →ₗ[ℝ] E' × F') =
      LinearMap.det (fderiv ℝ f x₀ : E' →ₗ[ℝ] E') *
        LinearMap.det (L : F' →ₗ[ℝ] F') := by
  have h : HasFDerivAt (fun p : E' × F' ↦ (f p.1, L p.2))
      ((fderiv ℝ f x₀).prodMap L) (x₀, y₀) :=
    HasFDerivAt.prodMk
      (hf.hasFDerivAt.comp _ (ContinuousLinearMap.fst ℝ E' F').hasFDerivAt)
      (L.hasFDerivAt.comp _ (ContinuousLinearMap.snd ℝ E' F').hasFDerivAt)
  rw [h.fderiv, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap]

/-- At a zero-section point of MoebiusBand, the determinant of the tangent coordChangeL
equals the product of the base tangent coordChange determinant and the bundle coordChange
determinant. This holds because the Jacobian is block-diagonal at zero-section points. -/
private theorem det_coordChangeL_eq_det_tangentBundleCore_coordChange
    (p q z : MoebiusBand)
    (hmem : z ∈ (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).baseSet ∩
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q).baseSet) :
    LinearMap.det (Trivialization.coordChangeL ℝ
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p)
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q) z).toLinearEquiv.toLinearMap =
    LinearMap.det ((tangentBundleCore ((𝓡 1).prod 𝓘(ℝ, ℝ)) MoebiusBand).coordChange
      ((tangentBundleCore ((𝓡 1).prod 𝓘(ℝ, ℝ)) MoebiusBand).indexAt p)
      ((tangentBundleCore ((𝓡 1).prod 𝓘(ℝ, ℝ)) MoebiusBand).indexAt q) z :
        (EuclideanSpace ℝ (Fin 1) × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) × ℝ) := by
  set I := (𝓡 1).prod 𝓘(ℝ, ℝ) with hI
  set E1 := EuclideanSpace ℝ (Fin 1) with hE1
  set Z := tangentBundleCore I MoebiusBand
  haveI : IsManifold I 1 MoebiusBand := IsManifold.of_le (n := ⊤) le_top
  change LinearMap.det (Trivialization.coordChangeL ℝ
    (trivializationAt (E1 × ℝ) (TangentSpace I) p)
    (trivializationAt (E1 × ℝ) (TangentSpace I) q) z).toLinearEquiv.toLinearMap =
    LinearMap.det (Z.coordChange (Z.indexAt p) (Z.indexAt q) z : (E1 × ℝ) →ₗ[ℝ] E1 × ℝ)
  congr 1
  apply LinearMap.ext
  intro v
  change (Trivialization.coordChangeL ℝ _ _ z) v = Z.coordChange _ _ z v
  exact Z.trivializationAt_coordChange_eq hmem v

private theorem extChartAt_zeroSection_eq
    (p z : MoebiusBand) (hz : z.snd = 0) :
    extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) p z =
      (extChartAt (𝓡 1) p.proj z.proj, (0 : ℝ)) := by
  set mbc := moebiusBundleCore with hmbc
  set ip := mbc.indexAt p.proj with hip
  rw [show ((𝓡 1).prod 𝓘(ℝ, ℝ)) = (𝓡 1).prod 𝓘(ℝ, ℝ) from rfl, FiberBundle.extChartAt]
  simp only [PartialEquiv.trans_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    mbc.trivializationAt, VectorBundleCore.localTrivAt, id]
  change (extChartAt (𝓡 1) p.proj ((mbc.localTriv ip z).1), (mbc.localTriv ip z).2) =
    (extChartAt (𝓡 1) p.proj z.proj, 0)
  rw [mbc.localTriv_apply, hz, map_zero]

private theorem moebius_coordChange_eventually_const
    (p q z : MoebiusBand)
    (hmem_p : z ∈ (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) p).source)
    (hmem_q : z ∈ (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) q).source) :
    ∀ᶠ (c : Circle) in nhds z.proj,
      moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
        (moebiusBundleCore.indexAt q.proj) c =
      moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
        (moebiusBundleCore.indexAt q.proj) z.proj := by
  set mbc := moebiusBundleCore with hmbc
  set ip := mbc.indexAt p.proj with hip
  set iq := mbc.indexAt q.proj with hiq
  set L₀ := mbc.coordChange ip iq z.proj with hL₀
  change ∀ᶠ (c : Circle) in nhds z.proj, mbc.coordChange ip iq c = L₀
  have hzp_ip : z.proj ∈ mbc.baseSet ip := by
    have h := hmem_p
    rw [FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.trans_source] at h
    have h1 := h.1
    rwa [Trivialization.mem_source, mbc.trivializationAt, VectorBundleCore.localTrivAt,
      ← mbc.baseSet_at] at h1
  have hzp_iq : z.proj ∈ mbc.baseSet iq := by
    have h := hmem_q
    rw [FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.trans_source] at h
    have h1 := h.1
    rwa [Trivialization.mem_source, mbc.trivializationAt, VectorBundleCore.localTrivAt,
      ← mbc.baseSet_at] at h1
  have him_cont : Continuous (fun (c : Circle) => (c : ℂ).im) :=
    Complex.continuous_im.comp continuous_subtype_val
  clear_value ip iq mbc L₀
  subst hmbc
  fin_cases ip <;> fin_cases iq <;>
    dsimp only [moebiusBundleCore, MoebiusBand.coordChange] at hL₀ ⊢
  · subst hL₀
    exact .of_forall (fun _ => rfl)
  · have hne : (z.proj : ℂ).im ≠ 0 := Circle.im_ne_zero_of_ne hzp_iq hzp_ip
    by_cases him : 0 < (z.proj : ℂ).im
    · subst hL₀
      exact Filter.eventually_of_mem ((isOpen_Ioi.preimage him_cont).mem_nhds him)
        (fun c (hc : 0 < (c : ℂ).im) => by rw [if_pos hc, if_pos him])
    · subst hL₀
      exact Filter.eventually_of_mem
        ((isOpen_Iio.preimage him_cont).mem_nhds (lt_of_le_of_ne (not_lt.mp him) hne))
        (fun c (hc : (c : ℂ).im < 0) => by
          rw [if_neg (not_lt.mpr (le_of_lt hc)), if_neg him])
  · have hne : (z.proj : ℂ).im ≠ 0 := Circle.im_ne_zero_of_ne hzp_ip hzp_iq
    by_cases him : 0 < (z.proj : ℂ).im
    · subst hL₀
      exact Filter.eventually_of_mem ((isOpen_Ioi.preimage him_cont).mem_nhds him)
        (fun c (hc : 0 < (c : ℂ).im) => by rw [if_pos hc, if_pos him])
    · subst hL₀
      exact Filter.eventually_of_mem
        ((isOpen_Iio.preimage him_cont).mem_nhds (lt_of_le_of_ne (not_lt.mp him) hne))
        (fun c (hc : (c : ℂ).im < 0) => by
          rw [if_neg (not_lt.mpr (le_of_lt hc)), if_neg him])
  · subst hL₀
    exact .of_forall (fun _ => rfl)

private theorem extChart_transition_pullback_const
    (p q z : MoebiusBand)
    (hmem_p_base : z.proj ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) p.proj).source)
    (hcoord_const : ∀ᶠ (c : Circle) in nhds z.proj,
      moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
        (moebiusBundleCore.indexAt q.proj) c =
      moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
        (moebiusBundleCore.indexAt q.proj) z.proj) :
    ∀ᶠ (xw : EuclideanSpace ℝ (Fin 1) × ℝ) in nhds (extChartAt (𝓡 1) p.proj z.proj, (0 : ℝ)),
      moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
          (moebiusBundleCore.indexAt q.proj) ((extChartAt (𝓡 1) p.proj).symm xw.1) =
        moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
          (moebiusBundleCore.indexAt q.proj) z.proj := by
  set E1 := EuclideanSpace ℝ (Fin 1) with hE1
  set x₀ := extChartAt (𝓡 1) p.proj z.proj with hx₀
  set ip := moebiusBundleCore.indexAt p.proj with hip
  set iq := moebiusBundleCore.indexAt q.proj with hiq
  set L₀ := moebiusBundleCore.coordChange ip iq z.proj with hL₀
  change ∀ᶠ (xw : E1 × ℝ) in nhds (x₀, (0 : ℝ)),
      moebiusBundleCore.coordChange ip iq ((extChartAt (𝓡 1) p.proj).symm xw.1) = L₀
  have hcoord_const' : ∀ᶠ (c : Circle) in nhds z.proj,
      moebiusBundleCore.coordChange ip iq c = L₀ := by
    simpa [ip, iq, L₀] using hcoord_const
  have hx₀_target : x₀ ∈ (extChartAt (𝓡 1) p.proj).target :=
    (extChartAt (𝓡 1) p.proj).map_source (extChartAt_source (𝓡 1) p.proj ▸ hmem_p_base)
  have hchart_sym_val : (extChartAt (𝓡 1) p.proj).symm x₀ = z.proj :=
    (extChartAt (𝓡 1) p.proj).left_inv (extChartAt_source (𝓡 1) p.proj ▸ hmem_p_base)
  have hcsa : ContinuousAt ((extChartAt (𝓡 1) p.proj).symm) x₀ :=
    (continuousOn_extChartAt_symm p.proj).continuousAt
      ((isOpen_extChartAt_target p.proj).mem_nhds hx₀_target)
  have hpull : ∀ᶠ (x : E1) in nhds x₀,
      moebiusBundleCore.coordChange ip iq ((extChartAt (𝓡 1) p.proj).symm x) = L₀ :=
    hcsa.eventually (hchart_sym_val ▸ hcoord_const')
  exact (continuous_fst.continuousAt (x := (x₀, (0 : ℝ)))).eventually hpull

private theorem extChart_transition_eventually_formula_on_overlap
    (p q z : MoebiusBand)
    (hmem_p : z ∈ (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) p).source)
    (hmem_q : z ∈ (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) q).source)
    (hext_p_z : extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) p z =
      (extChartAt (𝓡 1) p.proj z.proj, (0 : ℝ))) :
    ∀ᶠ (xw : EuclideanSpace ℝ (Fin 1) × ℝ) in nhds (extChartAt (𝓡 1) p.proj z.proj, (0 : ℝ)),
      (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) q ∘ (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) p).symm) xw =
      (((extChartAt (𝓡 1) q.proj) ∘ (extChartAt (𝓡 1) p.proj).symm) xw.1,
        moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
          (moebiusBundleCore.indexAt q.proj) ((extChartAt (𝓡 1) p.proj).symm xw.1) xw.2) := by
  set I := (𝓡 1).prod 𝓘(ℝ, ℝ) with hI
  set E1 := EuclideanSpace ℝ (Fin 1) with hE1
  set mbc := moebiusBundleCore with hmbc
  set ip := mbc.indexAt p.proj with hip
  set iq := mbc.indexAt q.proj with hiq
  set x₀ := extChartAt (𝓡 1) p.proj z.proj with hx₀
  set baseTransition := (extChartAt (𝓡 1) q.proj) ∘ (extChartAt (𝓡 1) p.proj).symm
    with hbaseTransition
  change ∀ᶠ (xw : E1 × ℝ) in nhds (x₀, (0 : ℝ)),
      (extChartAt I q ∘ (extChartAt I p).symm) xw =
      (baseTransition xw.1, mbc.coordChange ip iq ((extChartAt (𝓡 1) p.proj).symm xw.1) xw.2)
  have hext_p_z' : extChartAt I p z = (x₀, (0 : ℝ)) := by
    simpa [I, x₀] using hext_p_z
  have hz_ext_source_p : z ∈ (extChartAt I p).source := extChartAt_source I p ▸ hmem_p
  have hz_ext_source_q : z ∈ (extChartAt I q).source := extChartAt_source I q ▸ hmem_q
  have hoverlap_mem : (x₀, (0 : ℝ)) ∈ (extChartAt I p).target ∩
      (extChartAt I p).symm ⁻¹' (extChartAt I q).source := by
    refine ⟨hext_p_z' ▸ (extChartAt I p).map_source hz_ext_source_p, ?_⟩
    change (extChartAt I p).symm (x₀, (0 : ℝ)) ∈ (extChartAt I q).source
    rw [← hext_p_z', (extChartAt I p).left_inv hz_ext_source_p]
    exact hz_ext_source_q
  have hoverlap_open : IsOpen ((extChartAt I p).target ∩
      (extChartAt I p).symm ⁻¹' (extChartAt I q).source) :=
    (continuousOn_extChartAt_symm p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) (isOpen_extChartAt_source q)
  apply Filter.eventually_of_mem (hoverlap_open.mem_nhds hoverlap_mem)
  intro ⟨x, w⟩ ⟨hx_target, hx_source⟩
  set b := (extChartAt (𝓡 1) p.proj).symm x with hb_def
  have hproj : ((extChartAt I p).symm (x, w)).proj = b := by
    simp only [show I = (𝓡 1).prod 𝓘(ℝ, ℝ) from rfl, FiberBundle.extChartAt]
    rfl
  have hb_ip : b ∈ mbc.baseSet ip := by
    have h := (extChartAt I p).map_target hx_target
    rw [extChartAt_source, FiberBundle.chartedSpace_chartAt,
      OpenPartialHomeomorph.trans_source] at h
    have h1 := h.1
    rw [Trivialization.mem_source, mbc.trivializationAt, VectorBundleCore.localTrivAt,
      ← mbc.baseSet_at] at h1
    rwa [hproj] at h1
  have hb_iq : b ∈ mbc.baseSet iq := by
    have h := show (extChartAt I p).symm (x, w) ∈ (extChartAt I q).source from hx_source
    rw [extChartAt_source, FiberBundle.chartedSpace_chartAt,
      OpenPartialHomeomorph.trans_source] at h
    have h1 := h.1
    rw [Trivialization.mem_source, mbc.trivializationAt, VectorBundleCore.localTrivAt,
      ← mbc.baseSet_at] at h1
    rwa [hproj] at h1
  simp only [Function.comp_def, show I = (𝓡 1).prod 𝓘(ℝ, ℝ) from rfl, FiberBundle.extChartAt]
  exact Prod.ext rfl
    (mbc.coordChange_comp ip (mbc.indexAt b) iq b ⟨⟨hb_ip, mbc.mem_baseSet_at b⟩, hb_iq⟩ w)

private theorem extChart_transition_eventually_eq_prod_core
    (p q z : MoebiusBand)
    (hformula : ∀ᶠ (xw : EuclideanSpace ℝ (Fin 1) × ℝ) in
      nhds (extChartAt (𝓡 1) p.proj z.proj, (0 : ℝ)),
      (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) q ∘ (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) p).symm) xw =
      (((extChartAt (𝓡 1) q.proj) ∘ (extChartAt (𝓡 1) p.proj).symm) xw.1,
        moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
          (moebiusBundleCore.indexAt q.proj) ((extChartAt (𝓡 1) p.proj).symm xw.1) xw.2))
    (hpullback_prod : ∀ᶠ (xw : EuclideanSpace ℝ (Fin 1) × ℝ) in
      nhds (extChartAt (𝓡 1) p.proj z.proj, (0 : ℝ)),
      moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
          (moebiusBundleCore.indexAt q.proj) ((extChartAt (𝓡 1) p.proj).symm xw.1) =
        moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
          (moebiusBundleCore.indexAt q.proj) z.proj) :
    ∀ᶠ (xw : EuclideanSpace ℝ (Fin 1) × ℝ) in nhds (extChartAt (𝓡 1) p.proj z.proj, (0 : ℝ)),
      (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) q ∘ (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) p).symm) xw =
      (((extChartAt (𝓡 1) q.proj) ∘ (extChartAt (𝓡 1) p.proj).symm) xw.1,
        (moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
          (moebiusBundleCore.indexAt q.proj) z.proj) xw.2) := by
  exact (hformula.and hpullback_prod).mono (fun ⟨x, w⟩ ⟨h1, h2⟩ => by rw [h1, h2])

private theorem extChart_transition_eventually_eq_prod
    (p q z : MoebiusBand) (hz : z.snd = 0)
    (hmem_p : z ∈ (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) p).source)
    (hmem_q : z ∈ (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) q).source) :
    (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) q ∘ (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) p).symm) =ᶠ[nhds
        (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) p z)]
      fun w : EuclideanSpace ℝ (Fin 1) × ℝ =>
        (((extChartAt (𝓡 1) q.proj) ∘ (extChartAt (𝓡 1) p.proj).symm) w.1,
          (moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
            (moebiusBundleCore.indexAt q.proj) z.proj) w.2) := by
  set I := (𝓡 1).prod 𝓘(ℝ, ℝ) with hI
  set E1 := EuclideanSpace ℝ (Fin 1) with hE1
  set mbc := moebiusBundleCore with hmbc
  set ip := mbc.indexAt p.proj with hip
  set iq := mbc.indexAt q.proj with hiq
  set L₀ := mbc.coordChange ip iq z.proj with hL₀
  set x₀ := extChartAt (𝓡 1) p.proj z.proj with hx₀
  set baseTransition := (extChartAt (𝓡 1) q.proj) ∘ (extChartAt (𝓡 1) p.proj).symm
    with hbaseTransition
  change (extChartAt I q ∘ (extChartAt I p).symm) =ᶠ[nhds (extChartAt I p z)]
    fun w : E1 × ℝ => (baseTransition w.1, L₀ w.2)
  have hext_p_z : extChartAt I p z = (x₀, (0 : ℝ)) := by
    simpa [I, x₀] using extChartAt_zeroSection_eq p z hz
  have hmem_p_base : z.proj ∈ (chartAt E1 p.proj).source := by
    simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hmem_p
    exact hmem_p.2
  have hcoord_const : ∀ᶠ (c : Circle) in nhds z.proj, mbc.coordChange ip iq c = L₀ := by
    simpa [mbc, ip, iq, L₀] using moebius_coordChange_eventually_const p q z hmem_p hmem_q
  have hpullback_prod : ∀ᶠ (xw : E1 × ℝ) in nhds (x₀, (0 : ℝ)),
      mbc.coordChange ip iq ((extChartAt (𝓡 1) p.proj).symm xw.1) = L₀ := by
    simpa [E1, x₀, mbc, ip, iq, L₀] using
      extChart_transition_pullback_const p q z hmem_p_base
        (by
          simpa [mbc, ip, iq, L₀] using hcoord_const)
  have hformula : ∀ᶠ (xw : E1 × ℝ) in nhds (x₀, (0 : ℝ)),
      (extChartAt I q ∘ (extChartAt I p).symm) xw =
      (baseTransition xw.1, mbc.coordChange ip iq ((extChartAt (𝓡 1) p.proj).symm xw.1) xw.2) := by
    simpa [I, E1, x₀, mbc, ip, iq, baseTransition] using
      extChart_transition_eventually_formula_on_overlap p q z hmem_p hmem_q
        (by
          simpa [I, x₀] using hext_p_z)
  rw [hext_p_z]
  simpa [E1, x₀, mbc, ip, iq, L₀, baseTransition] using
    extChart_transition_eventually_eq_prod_core p q z
      (by simpa [E1, x₀, mbc, ip, iq, baseTransition] using hformula)
      (by simpa [E1, x₀, mbc, ip, iq, L₀] using hpullback_prod)

private theorem base_chart_transition_differentiableAt
    (p q z : MoebiusBand)
    (hmem_p_base : z.proj ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) p.proj).source)
    (hmem_q_base : z.proj ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) q.proj).source) :
    DifferentiableAt ℝ
      (((extChartAt (𝓡 1) q.proj) ∘ (extChartAt (𝓡 1) p.proj).symm))
      (extChartAt (𝓡 1) p.proj z.proj) := by
  have hmem :
      extChartAt (𝓡 1) p.proj z.proj ∈
        ((extChartAt (𝓡 1) p.proj).symm ≫ extChartAt (𝓡 1) q.proj).source := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
    exact Set.mem_image_of_mem _ ⟨extChartAt_source (𝓡 1) p.proj ▸ hmem_p_base,
      extChartAt_source (𝓡 1) q.proj ▸ hmem_q_base⟩
  exact ((contDiffWithinAt_ext_coord_change q.proj p.proj hmem).differentiableWithinAt
    (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt (by
      rw [ModelWithCorners.range_eq_univ]
      exact isOpen_univ.mem_nhds (Set.mem_univ _))

private theorem fderiv_extChart_transition_eq_prodMap
    (p q z : MoebiusBand) (hz : z.snd = 0)
    (hmem_p : z ∈ (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) p).source)
    (hmem_q : z ∈ (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) q).source) :
    fderiv ℝ (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) q ∘ (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) p).symm)
      (extChartAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) p z) =
    (tangentCoordChange (𝓡 1) p.proj q.proj z.proj).prodMap
      (moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
        (moebiusBundleCore.indexAt q.proj) z.proj) := by
  set I := (𝓡 1).prod 𝓘(ℝ, ℝ) with hI
  set E1 := EuclideanSpace ℝ (Fin 1) with hE1
  set x₀ := extChartAt (𝓡 1) p.proj z.proj with hx₀
  set L₀ := moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
    (moebiusBundleCore.indexAt q.proj) z.proj with hL₀
  set baseTransition := (extChartAt (𝓡 1) q.proj) ∘ (extChartAt (𝓡 1) p.proj).symm
    with hbaseTransition
  have hext_p_z : extChartAt I p z = (x₀, (0 : ℝ)) := by
    simpa [I, x₀] using extChartAt_zeroSection_eq p z hz
  have hmem_p_base : z.proj ∈ (chartAt E1 p.proj).source := by
    simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hmem_p
    exact hmem_p.2
  have hmem_q_base : z.proj ∈ (chartAt E1 q.proj).source := by
    simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hmem_q
    exact hmem_q.2
  have hlocal : (extChartAt I q ∘ (extChartAt I p).symm) =ᶠ[nhds (extChartAt I p z)]
      fun w : E1 × ℝ => (baseTransition w.1, L₀ w.2) := by
    simpa [I, E1, x₀, L₀, baseTransition] using
      extChart_transition_eventually_eq_prod p q z hz hmem_p hmem_q
  have hf_diff : DifferentiableAt ℝ baseTransition x₀ := by
    simpa [x₀, baseTransition] using
      base_chart_transition_differentiableAt p q z hmem_p_base hmem_q_base
  have htc_eq : tangentCoordChange (𝓡 1) p.proj q.proj z.proj = fderiv ℝ baseTransition x₀ := by
    rw [tangentCoordChange_def, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  have hfd_simple : HasFDerivAt (fun w : E1 × ℝ => (baseTransition w.1, L₀ w.2))
      ((fderiv ℝ baseTransition x₀).prodMap L₀) (x₀, (0 : ℝ)) :=
    HasFDerivAt.prodMap (x₀, (0 : ℝ)) hf_diff.hasFDerivAt L₀.hasFDerivAt
  rw [hext_p_z, (hfd_simple.congr_of_eventuallyEq (hext_p_z ▸ hlocal)).fderiv, ← htc_eq]

private theorem det_tangent_coordChangeL_eq_mul
    (p q z : MoebiusBand) (_hp : p.snd = 0) (_hq : q.snd = 0) (hz : z.snd = 0)
    (hmem : z ∈ (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).baseSet ∩
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q).baseSet) :
    LinearMap.det (Trivialization.coordChangeL ℝ
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ) (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p)
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ) (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q)
      z).toLinearEquiv.toLinearMap =
    LinearMap.det (tangentCoordChange (𝓡 1) p.proj q.proj z.proj :
      EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) *
    LinearMap.det (moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
      (moebiusBundleCore.indexAt q.proj) z.proj : ℝ →ₗ[ℝ] ℝ) := by
  set I := (𝓡 1).prod 𝓘(ℝ, ℝ) with hI
  set E1 := EuclideanSpace ℝ (Fin 1) with hE1
  set Z := tangentBundleCore I MoebiusBand with hZ
  have hfderiv_prodMap :
      fderiv ℝ (extChartAt I q ∘ (extChartAt I p).symm) (extChartAt I p z) =
        (tangentCoordChange (𝓡 1) p.proj q.proj z.proj).prodMap
          (moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
            (moebiusBundleCore.indexAt q.proj) z.proj) := by
    simpa [I] using fderiv_extChart_transition_eq_prodMap p q z hz hmem.1 hmem.2
  have hcl_det :
      LinearMap.det (Trivialization.coordChangeL ℝ
        (trivializationAt (E1 × ℝ) (TangentSpace I) p)
        (trivializationAt (E1 × ℝ) (TangentSpace I) q) z).toLinearEquiv.toLinearMap =
      LinearMap.det (Z.coordChange (Z.indexAt p) (Z.indexAt q) z : (E1 × ℝ) →ₗ[ℝ] E1 × ℝ) := by
    simpa [I, Z] using det_coordChangeL_eq_det_tangentBundleCore_coordChange p q z hmem
  rw [hcl_det]
  have hZ_eq : (Z.coordChange (Z.indexAt p) (Z.indexAt q) z : (E1 × ℝ) →L[ℝ] E1 × ℝ) =
      (tangentCoordChange (𝓡 1) p.proj q.proj z.proj).prodMap
        (moebiusBundleCore.coordChange (moebiusBundleCore.indexAt p.proj)
          (moebiusBundleCore.indexAt q.proj) z.proj) := by
    have huc : Z.coordChange (Z.indexAt p) (Z.indexAt q) z =
        fderivWithin ℝ (extChartAt I q ∘ (extChartAt I p).symm) (Set.range I) (extChartAt I p z) :=
      rfl
    rw [huc, ModelWithCorners.range_eq_univ, fderivWithin_univ]
    exact hfderiv_prodMap
  simp only [hZ_eq, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap]

/-- Complex conjugation negates the orthogonal projection onto `(ℝ ∙ v)ᗮ` for real `v`. -/
private theorem orthogonalProjection_conj (v : ℂ) (hv : starRingEnd ℂ v = v) (hne : v ≠ 0)
    (z : ℂ) : Submodule.orthogonalProjection (ℝ ∙ v)ᗮ (starRingEnd ℂ z) =
    -Submodule.orthogonalProjection (ℝ ∙ v)ᗮ z := by
  suffices h : Submodule.orthogonalProjection (ℝ ∙ v)ᗮ (starRingEnd ℂ z + z) = 0 by
    have heq := (map_add (Submodule.orthogonalProjection (ℝ ∙ v)ᗮ)
      (starRingEnd ℂ z) z).symm
    rw [h] at heq; rwa [add_eq_zero_iff_eq_neg] at heq
  apply Submodule.orthogonalProjection_orthogonal_apply_eq_zero
  have hv_im : v.im = 0 := by
    have := congr_arg Complex.im hv; simp at this; linarith
  have hv_re : v.re ≠ 0 := by
    intro h; exact hne (Complex.ext (by simp [h]) hv_im)
  rw [show (starRingEnd ℂ z + z : ℂ) = ((2 * z.re : ℝ) : ℂ) from by
    apply Complex.ext <;> simp [two_mul],
    show ((2 * z.re : ℝ) : ℂ) = (2 * z.re / v.re) • v from by
      apply Complex.ext
      · simp [hv_im, div_mul_cancel₀ _ hv_re]
      · simp [hv_im]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))

/-- Stereographic projection negates under complex conjugation for real poles:
`stereo_v(conj z) = -stereo_v(z)`. -/
private theorem stereographic_conj_neg {v : ℂ} (hv : ‖v‖ = 1)
    (hv_real : starRingEnd ℂ v = v)
    (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) 1)
    (hcz : starRingEnd ℂ z ∈ Metric.sphere (0 : ℂ) 1) :
    stereographic hv ⟨starRingEnd ℂ z, hcz⟩ =
    -(stereographic hv ⟨z, hz⟩ : ↥(ℝ ∙ (v : ℂ))ᗮ) := by
  simp only [stereographic_apply]
  have hv_im : v.im = 0 := by
    have := congr_arg Complex.im hv_real; simp at this; linarith
  have hinner : inner ℝ v (starRingEnd ℂ z) = inner ℝ v z := by
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    rw [hv_im]; ring
  have hne : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; linarith
  rw [hinner, orthogonalProjection_conj v hv_real hne z, smul_neg]

/-- `stereographic'(conj z) = -stereographic'(z)` for real poles, lifting `stereographic_conj_neg`
through the ONB isometry. -/
private theorem stereographic'_conj_neg [Fact (Module.finrank ℝ ℂ = 1 + 1)]
    (v : ↥(Metric.sphere (0 : ℂ) 1))
    (hv_real : starRingEnd ℂ (v : ℂ) = (v : ℂ))
    (z : ↥(Metric.sphere (0 : ℂ) 1))
    (hcz : starRingEnd ℂ (z : ℂ) ∈ Metric.sphere (0 : ℂ) 1) :
    (stereographic' 1 v) ⟨starRingEnd ℂ z, hcz⟩ =
    -((stereographic' 1 v) z) := by
  unfold stereographic'
  simp only [OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
    LinearIsometryEquiv.coe_toHomeomorph]
  rw [stereographic_conj_neg (by simp : ‖(↑v : ℂ)‖ = 1) hv_real z.val z.prop hcz, map_neg]

/-- The inverse stereographic chart satisfies `symm(-t) = conj(symm(t))` for real poles. This is
proved from `stereographic'_conj_neg` via bijectivity rather than by formula manipulation. -/
private theorem stereographic'_symm_neg_eq_conj [hfr : Fact (Module.finrank ℝ ℂ = 1 + 1)]
    (v : ↥(Metric.sphere (0 : ℂ) 1))
    (hv_real : starRingEnd ℂ (v : ℂ) = (v : ℂ))
    (t : EuclideanSpace ℝ (Fin 1)) :
    (stereographic' 1 v).symm (-t) = ⟨starRingEnd ℂ ((stereographic' 1 v).symm t : ℂ),
      by simp⟩ := by
  have htarget : ∀ s : EuclideanSpace ℝ (Fin 1), s ∈ (stereographic' 1 v).target :=
    fun s => (stereographic'_target (n := 1) v).symm ▸ Set.mem_univ s
  have hsymm_source : ∀ s, (stereographic' 1 v).symm s ∈ (stereographic' 1 v).source :=
    fun s => (stereographic' 1 v).map_target (htarget s)
  have hsource_eq : (stereographic' 1 v).source = {v}ᶜ := stereographic'_source (n := 1) v
  -- conj(symm(t)) ≠ v: if conj(symm(t)) = v then symm(t) = conj(v) = v,
  -- contradicting symm(t) ∈ {v}ᶜ.
  have hconj_ne_v : (⟨starRingEnd ℂ ((stereographic' 1 v).symm t : ℂ), by simp⟩ :
      ↥(Metric.sphere (0 : ℂ) 1)) ≠ v := by
    intro h
    have hsrc := hsymm_source t
    rw [hsource_eq, Set.mem_compl_iff, Set.mem_singleton_iff] at hsrc
    apply hsrc; ext
    have h1 : starRingEnd ℂ ((stereographic' 1 v).symm t : ℂ) = (v : ℂ) :=
      congr_arg (fun z : ↥(Metric.sphere (0 : ℂ) 1) => (z : ℂ)) h
    have h2 := congr_arg (starRingEnd ℂ) h1
    simpa [hv_real] using h2
  -- Both sides are in source; they map to the same value under stereographic', so are equal
  apply (stereographic' 1 v).injOn (hsymm_source (-t))
  · rw [hsource_eq]; exact hconj_ne_v
  rw [(stereographic' 1 v).right_inv (htarget (-t)),
    stereographic'_conj_neg v hv_real _ _,
    (stereographic' 1 v).right_inv (htarget t)]

/-- Chart transitions on `Circle` are differentiable at any interior point.
Extracted as a standalone lemma to avoid kernel timeouts in larger proof contexts. -/
private theorem circle_chart_transition_differentiableAt
    (x x' : Circle) (z : Circle)
    (hmem : (extChartAt (𝓡 1) x) z ∈
      ((extChartAt (𝓡 1) x).symm ≫ extChartAt (𝓡 1) x').source) :
    DifferentiableAt ℝ
      ((extChartAt (𝓡 1) x') ∘ (extChartAt (𝓡 1) x).symm)
      ((extChartAt (𝓡 1) x) z) :=
  ((contDiffWithinAt_ext_coord_change x' x hmem).differentiableWithinAt
    (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt (by
      rw [ModelWithCorners.range_eq_univ]; exact isOpen_univ.mem_nhds (Set.mem_univ _))

private theorem circle_I_mem_extChartAt_one_source
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) ∈
      (extChartAt (𝓡 1) (1 : Circle)).source := by
  rw [extChartAt_source,
    show chartAt (EuclideanSpace ℝ (Fin 1)) (1 : Circle) =
      stereographic' 1 (-(1 : ↥(Metric.sphere (0 : ℂ) 1))) from rfl,
    stereographic'_source (n := 1) (-(1 : ↥(Metric.sphere (0 : ℂ) 1)))]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have := congr_arg (fun z : Circle => (z : ℂ).im) h
  simp at this

private theorem circle_negI_mem_extChartAt_one_source
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    (⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) ∈
      (extChartAt (𝓡 1) (1 : Circle)).source := by
  rw [extChartAt_source,
    show chartAt (EuclideanSpace ℝ (Fin 1)) (1 : Circle) =
      stereographic' 1 (-(1 : ↥(Metric.sphere (0 : ℂ) 1))) from rfl,
    stereographic'_source (n := 1) (-(1 : ↥(Metric.sphere (0 : ℂ) 1)))]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have := congr_arg (fun z : Circle => (z : ℂ).im) h
  simp at this

private theorem extChartAt_one_negI_eq_neg_extChartAt_one_I
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    (extChartAt (𝓡 1) (1 : Circle)) (⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) =
      -((extChartAt (𝓡 1) (1 : Circle))
        (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)) := by
  have hext : ∀ z : Circle,
      (extChartAt (𝓡 1) (1 : Circle)) z = (chartAt (EuclideanSpace ℝ (Fin 1)) (1 : Circle)) z :=
    fun _ => rfl
  rw [hext, hext]
  have hchart : chartAt (EuclideanSpace ℝ (Fin 1)) (1 : ↥(Metric.sphere (0 : ℂ) 1)) =
      stereographic' 1 (-(1 : ↥(Metric.sphere (0 : ℂ) 1))) := rfl
  rw [hchart]
  unfold stereographic'
  simp only [OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
    LinearIsometryEquiv.coe_toHomeomorph]
  have key : ∀ (hv : ‖(↑(-(1 : ↥(Metric.sphere (0 : ℂ) 1))) : ℂ)‖ = 1),
      stereographic hv ⟨-Complex.I, by simp⟩ =
      -(stereographic hv ⟨Complex.I, by simp⟩ :
        ↥(ℝ ∙ (↑(-(1 : ↥(Metric.sphere (0 : ℂ) 1))) : ℂ))ᗮ) := by
    intro hv
    simp only [stereographic_apply]
    have hconj : (-Complex.I : ℂ) = starRingEnd ℂ Complex.I := by
      simp [Complex.conj_I]
    have hinner : inner ℝ (↑(-(1 : ↥(Metric.sphere (0 : ℂ) 1))) : ℂ) (-Complex.I : ℂ) =
        inner ℝ (↑(-(1 : ↥(Metric.sphere (0 : ℂ) 1))) : ℂ) (Complex.I : ℂ) := by
      simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      have : (↑(-(1 : ↥(Metric.sphere (0 : ℂ) 1))) : ℂ).im = 0 := by
        simp
      rw [this]
      norm_num
    rw [hinner, hconj,
      orthogonalProjection_conj _ (by simp) (by simp [ne_eq]) Complex.I, smul_neg]
  simp only [key, map_neg]

private theorem circle_transition_one_to_negOne_odd
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    ((↑(extChartAt (𝓡 1) Circle.negOne)) ∘ (↑(extChartAt (𝓡 1) (1 : Circle)).symm)) ∘ Neg.neg =
      Neg.neg ∘ ((↑(extChartAt (𝓡 1) Circle.negOne)) ∘
        (↑(extChartAt (𝓡 1) (1 : Circle)).symm)) := by
  set g := (↑(extChartAt (𝓡 1) Circle.negOne)) ∘ (↑(extChartAt (𝓡 1) (1 : Circle)).symm) with hg
  change g ∘ Neg.neg = Neg.neg ∘ g
  set v₁ : ↥(Metric.sphere (0 : ℂ) 1) := -(1 : ↥(Metric.sphere (0 : ℂ) 1))
  set v₂ : ↥(Metric.sphere (0 : ℂ) 1) := -v₁
  have hpole1_real : starRingEnd ℂ (v₁ : ℂ) = (v₁ : ℂ) := by
    change starRingEnd ℂ (-1 : ℂ) = -1
    simp
  have hpole2_real : starRingEnd ℂ (v₂ : ℂ) = (v₂ : ℂ) := by
    simp [v₂, v₁]
  funext t
  simp only [Function.comp, hg]
  change (stereographic' 1 v₂) ((stereographic' 1 v₁).symm (-t)) =
    -((stereographic' 1 v₂) ((stereographic' 1 v₁).symm t))
  rw [stereographic'_symm_neg_eq_conj v₁ hpole1_real t]
  exact stereographic'_conj_neg v₂ hpole2_real ((stereographic' 1 v₁).symm t) (by simp)

private theorem trans_source_mem_at
    [Fact (Module.finrank ℝ ℂ = 1 + 1)]
    (z : Circle)
    (hz_src : z ∈ (extChartAt (𝓡 1) (1 : Circle)).source)
    (hz_ne_one : z ≠ (1 : Circle)) :
    (extChartAt (𝓡 1) (1 : Circle)) z ∈
      ((extChartAt (𝓡 1) (1 : Circle)).symm.trans (extChartAt (𝓡 1) Circle.negOne)).source := by
  simp only [PartialEquiv.trans_source]
  constructor
  · exact (extChartAt (𝓡 1) (1 : Circle)).map_source hz_src
  · change (extChartAt (𝓡 1) (1 : Circle)).symm ((extChartAt (𝓡 1) (1 : Circle)) z) ∈
      (extChartAt (𝓡 1) Circle.negOne).source
    rw [(extChartAt (𝓡 1) (1 : Circle)).left_inv hz_src]
    rw [extChartAt_source,
      show chartAt (EuclideanSpace ℝ (Fin 1)) Circle.negOne =
        stereographic' 1 (-(-(1 : ↥(Metric.sphere (0 : ℂ) 1)))) from rfl,
      stereographic'_source (n := 1) (-(-(1 : ↥(Metric.sphere (0 : ℂ) 1))))]
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz_ne_one

private theorem trans_source_mem_at_t0
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    (extChartAt (𝓡 1) (1 : Circle)) (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) ∈
      ((extChartAt (𝓡 1) (1 : Circle)).symm.trans (extChartAt (𝓡 1) Circle.negOne)).source := by
  refine trans_source_mem_at (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)
    circle_I_mem_extChartAt_one_source ?_
  intro h
  have := congr_arg (fun z : Circle => (z : ℂ).im) h
  simp at this

private theorem trans_source_mem_at_neg_t0
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    (extChartAt (𝓡 1) (1 : Circle)) (⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) ∈
      ((extChartAt (𝓡 1) (1 : Circle)).symm.trans (extChartAt (𝓡 1) Circle.negOne)).source := by
  refine trans_source_mem_at (⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)
    circle_negI_mem_extChartAt_one_source ?_
  intro h
  have := congr_arg (fun z : Circle => (z : ℂ).im) h
  simp at this

private theorem fderiv_eq_at_neg_of_odd
    {g : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)} {t₀ : EuclideanSpace ℝ (Fin 1)}
    (h_odd : g ∘ Neg.neg = Neg.neg ∘ g)
    (_hdiff_t : DifferentiableAt ℝ g t₀)
    (hdiff_nt : DifferentiableAt ℝ g (-t₀)) :
    fderiv ℝ g (-t₀) = fderiv ℝ g t₀ := by
  have h1 := congr_arg (fun f => fderiv ℝ f t₀) h_odd
  dsimp only at h1
  have hdn : DifferentiableAt ℝ (Neg.neg : EuclideanSpace ℝ (Fin 1) → _) t₀ :=
    differentiableAt_id.neg
  rw [fderiv_comp t₀ hdiff_nt hdn] at h1
  conv_rhs at h1 => rw [show (Neg.neg : EuclideanSpace ℝ (Fin 1) → _) ∘ g = (-g) from rfl]
  rw [fderiv_neg] at h1
  have hfn : fderiv ℝ (Neg.neg : EuclideanSpace ℝ (Fin 1) → _) t₀ =
      -(ContinuousLinearMap.id ℝ _) := by
    change fderiv ℝ (-fun y => y) t₀ = _
    rw [fderiv_neg, fderiv_id']
  rw [hfn] at h1
  simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] at h1
  exact neg_inj.mp h1

/-- The tangent coordinate change on Circle between the two standard stereographic charts
gives the same linear map at I and -I. This follows from the chart transition being an odd
function: complex conjugation on the circle (which swaps I ↔ -I) corresponds to negation in
the model space, so g(-t) = -g(t), hence g'(-t) = g'(t). -/
private theorem circle_tangentCoordChange_eq_at_neg_I :
    tangentCoordChange (𝓡 1) (1 : Circle) Circle.negOne
      (⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) =
    tangentCoordChange (𝓡 1) (1 : Circle) Circle.negOne
      (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) := by
  haveI := finrank_real_complex_fact'
  simp only [tangentCoordChange, tangentBundleCore_coordChange_achart]
  set g := (↑(extChartAt (𝓡 1) Circle.negOne)) ∘ (↑(extChartAt (𝓡 1) (1 : Circle)).symm) with hg
  set t₀ := (extChartAt (𝓡 1) (1 : Circle))
    (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)
  have ht_neg : (extChartAt (𝓡 1) (1 : Circle))
      (⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) = -t₀ := by
    simpa [t₀] using extChartAt_one_negI_eq_neg_extChartAt_one_I
  rw [ht_neg]
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  have h_odd : g ∘ Neg.neg = Neg.neg ∘ g := by
    simpa [g] using circle_transition_one_to_negOne_odd
  have hmem_t : t₀ ∈ ((extChartAt (𝓡 1) (1 : Circle)).symm.trans
      (extChartAt (𝓡 1) Circle.negOne)).source := by
    simpa [t₀] using trans_source_mem_at_t0
  have hdiff_t : DifferentiableAt ℝ g t₀ :=
    circle_chart_transition_differentiableAt (1 : Circle) Circle.negOne
      ⟨Complex.I, by simp [Submonoid.unitSphere]⟩ hmem_t
  have hmem_nt : -t₀ ∈ ((extChartAt (𝓡 1) (1 : Circle)).symm.trans
      (extChartAt (𝓡 1) Circle.negOne)).source := by
    rw [← ht_neg]
    simpa using trans_source_mem_at_neg_t0
  have hdiff_nt : DifferentiableAt ℝ g (-t₀) := by
    rw [← ht_neg] at hmem_nt ⊢
    exact circle_chart_transition_differentiableAt (1 : Circle) Circle.negOne
      ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ hmem_nt
  exact fderiv_eq_at_neg_of_odd h_odd hdiff_t hdiff_nt

private theorem moebius_triv_baseSet_eq_index_baseSet (x : Circle) :
    (trivializationAt ℝ moebiusBundleCore.Fiber x).baseSet =
      moebiusBundleCore.baseSet (moebiusBundleCore.indexAt x) := by
  simp [trivializationAt, FiberBundle.trivializationAt]
  rfl

private theorem chartAt_one_eq_stereographic_negOne
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    chartAt (EuclideanSpace ℝ (Fin 1)) (1 : Circle) =
      stereographic' 1 (-(1 : ↥(Metric.sphere (0 : ℂ) 1))) := rfl

private theorem chartAt_negOne_eq_stereographic_posOne
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    chartAt (EuclideanSpace ℝ (Fin 1)) Circle.negOne =
      stereographic' 1 (1 : ↥(Metric.sphere (0 : ℂ) 1)) := by
  change stereographic' 1 (-⟨(-1 : ℂ), by simp⟩) = stereographic' 1 (1 : ↥(Metric.sphere (0 : ℂ) 1))
  congr 1
  ext
  simp

private theorem mem_tangent_triv_overlap_of_proj_ne_endpoints
    [Fact (Module.finrank ℝ ℂ = 1 + 1)]
    (z : MoebiusBand) (hne_neg : z.proj ≠ Circle.negOne) (hne_one : z.proj ≠ (1 : Circle)) :
    z ∈ (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) (⟨(1 : Circle), (0 : ℝ)⟩ : MoebiusBand)).baseSet ∩
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) (⟨Circle.negOne, (0 : ℝ)⟩ : MoebiusBand)).baseSet := by
  let p : MoebiusBand := ⟨(1 : Circle), (0 : ℝ)⟩
  let q : MoebiusBand := ⟨Circle.negOne, (0 : ℝ)⟩
  change z ∈ (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).baseSet ∩
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q).baseSet
  have chartAt_p : chartAt (EuclideanSpace ℝ (Fin 1)) p.proj =
      stereographic' 1 (-(1 : ↥(Metric.sphere (0 : ℂ) 1))) := by
    simpa [p] using chartAt_one_eq_stereographic_negOne
  have chartAt_q : chartAt (EuclideanSpace ℝ (Fin 1)) q.proj =
      stereographic' 1 (1 : ↥(Metric.sphere (0 : ℂ) 1)) := by
    simpa [q] using chartAt_negOne_eq_stereographic_posOne
  simp only [mem_inter_iff, TangentBundle.trivializationAt_baseSet]
  constructor
  · simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
    have hmem : z.proj ∈ (trivializationAt ℝ moebiusBundleCore.Fiber p.proj).baseSet := by
      rw [moebius_triv_baseSet_eq_index_baseSet]
      have hidx : moebiusBundleCore.indexAt p.proj = 0 := by
        simp [moebiusBundleCore, p, Circle.one_ne_negOne]
      rw [hidx]
      simpa [MoebiusBand.baseSet, MoebiusBand.U₀] using hne_neg
    exact ⟨(Trivialization.mem_source _).mpr hmem, by
      rw [Trivialization.coe_fst' _ hmem, chartAt_p, stereographic'_source,
        Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      apply hne_neg
      exact Subtype.ext (congr_arg Subtype.val heq)⟩
  · simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
    have hmem : z.proj ∈ (trivializationAt ℝ moebiusBundleCore.Fiber q.proj).baseSet := by
      rw [moebius_triv_baseSet_eq_index_baseSet]
      simp only [moebiusBundleCore, Circle.negOne, q]
      exact hne_one
    exact ⟨(Trivialization.mem_source _).mpr hmem, by
      rw [Trivialization.coe_fst' _ hmem, chartAt_q, stereographic'_source,
        Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      apply hne_one
      exact Subtype.ext (congr_arg Subtype.val heq)⟩

private theorem bundle_det_01_at_negI :
    LinearMap.det (↑(moebiusBundleCore.coordChange 0 1
      (⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)) : ℝ →ₗ[ℝ] ℝ) = -1 := by
  have : (moebiusBundleCore.coordChange 0 1
      (⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) : ℝ →L[ℝ] ℝ) =
      -ContinuousLinearMap.id ℝ ℝ := by
    simp [moebiusBundleCore, MoebiusBand.coordChange]
  rw [this]
  simp

private theorem bundle_det_01_at_posI :
    LinearMap.det (↑(moebiusBundleCore.coordChange 0 1
      (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)) : ℝ →ₗ[ℝ] ℝ) = 1 := by
  have : (moebiusBundleCore.coordChange 0 1
      (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) : ℝ →L[ℝ] ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by
    simp [moebiusBundleCore, MoebiusBand.coordChange]
  simp only [this, ContinuousLinearMap.coe_id, LinearMap.det_id]

private theorem tangentCoordChange_det_ne_zero_at_posI
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    LinearMap.det (tangentCoordChange (𝓡 1) (1 : Circle) Circle.negOne
      (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) :
      EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) ≠ 0 := by
  haveI := finrank_real_complex_fact'
  intro hzero
  have hcomp : ∀ v, tangentCoordChange (𝓡 1) Circle.negOne (1 : Circle)
      (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)
      (tangentCoordChange (𝓡 1) (1 : Circle) Circle.negOne
        (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) v) = v := by
    intro v
    have hmem_src : (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle) ∈
        (extChartAt (𝓡 1) (1 : Circle)).source ∩
        (extChartAt (𝓡 1) Circle.negOne).source ∩
        (extChartAt (𝓡 1) (1 : Circle)).source := by
      simp only [extChartAt_source, mem_inter_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [chartAt_one_eq_stereographic_negOne, stereographic'_source, mem_compl_iff,
          mem_singleton_iff]
        intro h
        have := congr_arg (fun z : Circle => (z : ℂ).im) h
        simp at this
      · rw [chartAt_negOne_eq_stereographic_posOne, stereographic'_source, mem_compl_iff,
          mem_singleton_iff]
        intro h
        have := congr_arg (fun z : Circle => (z : ℂ).im) h
        simp at this
      · rw [chartAt_one_eq_stereographic_negOne, stereographic'_source, mem_compl_iff,
          mem_singleton_iff]
        intro h
        have := congr_arg (fun z : Circle => (z : ℂ).im) h
        simp at this
    rw [tangentCoordChange_comp (I := (𝓡 1)) (w := (1 : Circle)) (x := Circle.negOne)
      (y := (1 : Circle)) (z := (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)) hmem_src]
    exact tangentCoordChange_self (by
      rw [extChartAt_source, chartAt_one_eq_stereographic_negOne, stereographic'_source,
        mem_compl_iff, mem_singleton_iff]
      intro h
      have := congr_arg (fun z : Circle => (z : ℂ).im) h
      simp at this)
  have hcomp_eq : (↑(tangentCoordChange (𝓡 1) Circle.negOne (1 : Circle)
      (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)) :
      EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)).comp
      (↑(tangentCoordChange (𝓡 1) (1 : Circle) Circle.negOne
      (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)) :
      EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) = LinearMap.id :=
    LinearMap.ext (fun v => hcomp v)
  have h1 := LinearMap.det_comp
    (↑(tangentCoordChange (𝓡 1) Circle.negOne (1 : Circle)
      (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)) :
      EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1))
    (↑(tangentCoordChange (𝓡 1) (1 : Circle) Circle.negOne
      (⟨Complex.I, by simp [Submonoid.unitSphere]⟩ : Circle)) :
      EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1))
  rw [hcomp_eq, LinearMap.det_id] at h1
  rw [hzero, mul_zero] at h1
  exact one_ne_zero h1

private theorem preconnected_univ_tangent_triv_baseSet_of
    (x : Circle)
    (hbs : (trivializationAt ℝ moebiusBundleCore.Fiber x).baseSet =
      (chartAt (EuclideanSpace ℝ (Fin 1)) x).source)
    (he₂t : ((chartAt (EuclideanSpace ℝ (Fin 1)) x).prod
      (OpenPartialHomeomorph.refl ℝ)).target = univ) :
    IsPreconnected (Set.univ : Set ↥(trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) (⟨x, (0 : ℝ)⟩ : MoebiusBand)).baseSet) := by
  let p : MoebiusBand := ⟨x, (0 : ℝ)⟩
  change IsPreconnected (Set.univ : Set ↥(trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
    (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).baseSet)
  rw [← preconnectedSpace_iff_univ, TangentBundle.trivializationAt_baseSet,
      FiberBundle.chartedSpace_chartAt]
  set e := (trivializationAt ℝ moebiusBundleCore.Fiber p.proj).trans
      ((chartAt (EuclideanSpace ℝ (Fin 1)) p.proj).prod (OpenPartialHomeomorph.refl ℝ))
  suffices ht : e.target = univ by
    have h := e.toHomeomorphSourceTarget
    rw [preconnectedSpace_iff_univ,
      show (univ : Set ↥e.source) = h ⁻¹' univ from by simp]
    exact h.isPreconnected_preimage.mpr (preconnectedSpace_iff_univ.mp
      (by rw [ht]; exact Subtype.preconnectedSpace isPreconnected_univ))
  rw [show e = (trivializationAt ℝ moebiusBundleCore.Fiber p.proj).trans
      ((chartAt (EuclideanSpace ℝ (Fin 1)) p.proj).prod (OpenPartialHomeomorph.refl ℝ))
    from rfl, OpenPartialHomeomorph.trans_target]
  rw [he₂t, univ_inter]
  ext z
  simp only [mem_preimage, mem_univ, iff_true]
  have hz : z ∈ ((chartAt (EuclideanSpace ℝ (Fin 1)) p.proj).prod
      (OpenPartialHomeomorph.refl ℝ)).target := he₂t ▸ mem_univ z
  have hsymm := ((chartAt (EuclideanSpace ℝ (Fin 1)) p.proj).prod
      (OpenPartialHomeomorph.refl ℝ)).map_target hz
  rw [OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source] at hsymm
  convert hsymm using 1
  rw [(trivializationAt ℝ moebiusBundleCore.Fiber p.proj).target_eq, hbs]

private theorem preconnected_univ_tangent_triv_baseSet_at_one
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    IsPreconnected (Set.univ : Set ↥(trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) (⟨(1 : Circle), (0 : ℝ)⟩ : MoebiusBand)).baseSet) := by
  have hbs : (trivializationAt ℝ moebiusBundleCore.Fiber (1 : Circle)).baseSet =
      (chartAt (EuclideanSpace ℝ (Fin 1)) (1 : Circle)).source := by
    have neg_one_eq : Circle.negOne = -(1 : ↥(Metric.sphere (0 : ℂ) 1)) :=
      Subtype.ext (by simp [Circle.negOne])
    rw [moebius_triv_baseSet_eq_index_baseSet, chartAt_one_eq_stereographic_negOne,
      stereographic'_source]
    have hidx : moebiusBundleCore.indexAt (1 : Circle) = 0 := by
      simp [moebiusBundleCore, Circle.one_ne_negOne]
    rw [hidx]
    ext z
    simp only [mem_compl_iff, mem_singleton_iff]
    change z ∈ MoebiusBand.U₀ ↔ _
    simp [MoebiusBand.U₀, neg_one_eq]
  have he₂t : ((chartAt (EuclideanSpace ℝ (Fin 1)) (1 : Circle)).prod
      (OpenPartialHomeomorph.refl ℝ)).target = univ := by
    rw [chartAt_one_eq_stereographic_negOne]
    simp [stereographic'_target]
  simpa using preconnected_univ_tangent_triv_baseSet_of (1 : Circle) hbs he₂t

private theorem preconnected_univ_tangent_triv_baseSet_at_negOne
    [Fact (Module.finrank ℝ ℂ = 1 + 1)] :
    IsPreconnected (Set.univ : Set ↥(trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) (⟨Circle.negOne, (0 : ℝ)⟩ : MoebiusBand)).baseSet) := by
  have hbs : (trivializationAt ℝ moebiusBundleCore.Fiber Circle.negOne).baseSet =
      (chartAt (EuclideanSpace ℝ (Fin 1)) Circle.negOne).source := by
    rw [moebius_triv_baseSet_eq_index_baseSet, chartAt_negOne_eq_stereographic_posOne,
      stereographic'_source]
    simp only [moebiusBundleCore, Circle.negOne]
    ext z
    simp only [mem_compl_iff, mem_singleton_iff]
    change z ∈ MoebiusBand.U₁ ↔ _
    simp [MoebiusBand.U₁]
  have he₂t : ((chartAt (EuclideanSpace ℝ (Fin 1)) Circle.negOne).prod
      (OpenPartialHomeomorph.refl ℝ)).target = univ := by
    rw [chartAt_negOne_eq_stereographic_posOne]
    simp [stereographic'_target]
  simpa using preconnected_univ_tangent_triv_baseSet_of Circle.negOne hbs he₂t

/-- Key computational fact: there exist two points in the base set overlap of two tangent
trivializations where the tangent coordinate change has opposite determinant signs. -/
private theorem exists_tangentCoordChangeL_neg_det :
    ∃ (p q zU zL : MoebiusBand)
      (_hzU : zU ∈ (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).baseSet ∩
        (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q).baseSet)
      (_hzL : zL ∈ (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).baseSet ∩
        (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q).baseSet),
  0 < LinearMap.det ((trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).coordChangeL ℝ
        (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q) zU).toLinearEquiv.toLinearMap ∧
    LinearMap.det ((trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).coordChangeL ℝ
        (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q) zL).toLinearEquiv.toLinearMap < 0 ∧
    IsPreconnected (Set.univ : Set ↥(trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).baseSet) ∧
    IsPreconnected (Set.univ : Set ↥(trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
        (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q).baseSet) := by
  let p : MoebiusBand := ⟨(1 : Circle), (0 : ℝ)⟩
  let q : MoebiusBand := ⟨Circle.negOne, (0 : ℝ)⟩
  let z_neg_I : MoebiusBand := ⟨⟨-Complex.I, by simp [Submonoid.unitSphere]⟩, (0 : ℝ)⟩
  let z_pos_I : MoebiusBand := ⟨⟨Complex.I, by simp [Submonoid.unitSphere]⟩, (0 : ℝ)⟩
  haveI := finrank_real_complex_fact'
  have hmem_neg : z_neg_I ∈ (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).baseSet ∩
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q).baseSet := by
    simpa [p, q] using mem_tangent_triv_overlap_of_proj_ne_endpoints z_neg_I
      (by
        intro h
        have := congr_arg (fun z : Circle => (z : ℂ).im) h
        simp [Circle.negOne, z_neg_I] at this)
      (by
        intro h
        have := congr_arg (fun z : Circle => (z : ℂ).im) h
        simp [z_neg_I] at this)
  have hmem_pos : z_pos_I ∈ (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).baseSet ∩
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q).baseSet := by
    simpa [p, q] using mem_tangent_triv_overlap_of_proj_ne_endpoints z_pos_I
      (by
        intro h
        have := congr_arg (fun z : Circle => (z : ℂ).im) h
        simp [Circle.negOne, z_pos_I] at this)
      (by
        intro h
        have := congr_arg (fun z : Circle => (z : ℂ).im) h
        simp [z_pos_I] at this)
  have hidxp : moebiusBundleCore.indexAt p.proj = 0 := by
    simp [moebiusBundleCore, p, Circle.one_ne_negOne]
  have hidxq : moebiusBundleCore.indexAt q.proj = 1 := by
    simp [moebiusBundleCore, q]
  have hfactor_neg := det_tangent_coordChangeL_eq_mul p q z_neg_I rfl rfl rfl hmem_neg
  have hfactor_pos := det_tangent_coordChangeL_eq_mul p q z_pos_I rfl rfl rfl hmem_pos
  rw [hidxp, hidxq] at hfactor_neg hfactor_pos
  have hbundle_det_neg :
      LinearMap.det (↑(moebiusBundleCore.coordChange 0 1 z_neg_I.proj) : ℝ →ₗ[ℝ] ℝ) = -1 := by
    simpa [z_neg_I] using bundle_det_01_at_negI
  have hbundle_det_pos :
      LinearMap.det (↑(moebiusBundleCore.coordChange 0 1 z_pos_I.proj) : ℝ →ₗ[ℝ] ℝ) = 1 := by
    simpa [z_pos_I] using bundle_det_01_at_posI
  rw [hbundle_det_neg, mul_neg_one] at hfactor_neg
  rw [hbundle_det_pos, mul_one] at hfactor_pos
  have hbase_eq : LinearMap.det
      (tangentCoordChange (𝓡 1) p.proj q.proj z_neg_I.proj :
        EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) =
      LinearMap.det (tangentCoordChange (𝓡 1) p.proj q.proj z_pos_I.proj :
        EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) := by
    have h := circle_tangentCoordChange_eq_at_neg_I
    change LinearMap.det (↑(tangentCoordChange (𝓡 1) (1 : Circle) Circle.negOne
      ⟨-Complex.I, _⟩) : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) =
      LinearMap.det (↑(tangentCoordChange (𝓡 1) (1 : Circle) Circle.negOne
      ⟨Complex.I, _⟩) : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1))
    rw [h]
  rw [hbase_eq] at hfactor_neg
  have hdet_ne : LinearMap.det (tangentCoordChange (𝓡 1) p.proj q.proj z_pos_I.proj :
      EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) ≠ 0 := by
    simpa [p, q, z_pos_I] using tangentCoordChange_det_ne_zero_at_posI
  have hpc_p : IsPreconnected (Set.univ : Set ↥(trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) p).baseSet) := by
    simpa [p] using preconnected_univ_tangent_triv_baseSet_at_one
  have hpc_q : IsPreconnected (Set.univ : Set ↥(trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ)
      (TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ))) q).baseSet) := by
    simpa [q] using preconnected_univ_tangent_triv_baseSet_at_negOne
  rcases ne_iff_lt_or_gt.mp hdet_ne with hlt | hgt
  · exact ⟨p, q, z_neg_I, z_pos_I, hmem_neg, hmem_pos,
      by linarith [hfactor_neg, hlt], by linarith [hfactor_pos, hlt], hpc_p, hpc_q⟩
  · exact ⟨p, q, z_pos_I, z_neg_I, hmem_pos, hmem_neg,
      by linarith [hfactor_pos, hgt], by linarith [hfactor_neg, hgt], hpc_p, hpc_q⟩

/-- The Möbius band is not orientable.

The tangent coordinate change between charts using the two different bundle trivializations has
Jacobian determinant of opposite sign on the upper and lower semicircles. A chart-sign cocycle
for `ManifoldOrientation` cannot satisfy the same compatibility equation at both points when these
determinants have opposite signs. -/
theorem not_orientable :
    ¬ Manifold.Orientable ((𝓡 1).prod 𝓘(ℝ, ℝ)) MoebiusBand := by
  intro ⟨orient⟩
  -- Get points where the tangent coordChange has opposite determinant signs.
  obtain ⟨p, q, zU, zL, hzU, hzL, hdet_pos, hdet_neg, hpc_p, hpc_q⟩ :=
    exists_tangentCoordChangeL_neg_det
  -- The compatibility condition at zU and zL:
  have hcompU := orient.compatible p q zU hzU
  have hcompL := orient.compatible p q zL hzL
  -- The determinants have opposite signs, so Orientation.map gives different results.
  have hcard : Fintype.card (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × ℝ))) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × ℝ) := by simp
  set I := (𝓡 1).prod 𝓘(ℝ, ℝ)
  set eU := (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ) (TangentSpace I) p).coordChangeL ℝ
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ) (TangentSpace I) q) zU
  set eL := (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ) (TangentSpace I) p).coordChangeL ℝ
      (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ) (TangentSpace I) q) zL
  set σU := Manifold.signedOrientation (orient.chartSign p ⟨zU, hzU.1⟩)
    (Manifold.baseOrientation (E := EuclideanSpace ℝ (Fin 1) × ℝ))
  set σL := Manifold.signedOrientation (orient.chartSign p ⟨zL, hzL.1⟩)
    (Manifold.baseOrientation (E := EuclideanSpace ℝ (Fin 1) × ℝ))
  set τU := Manifold.signedOrientation (orient.chartSign q ⟨zU, hzU.2⟩)
    (Manifold.baseOrientation (E := EuclideanSpace ℝ (Fin 1) × ℝ))
  set τL := Manifold.signedOrientation (orient.chartSign q ⟨zL, hzL.2⟩)
    (Manifold.baseOrientation (E := EuclideanSpace ℝ (Fin 1) × ℝ))
  -- Positive det: CL zU preserves orientation
  have hU : Orientation.map _ eU.toLinearEquiv σU = σU :=
      (Orientation.map_eq_iff_det_pos σU _ hcard).mpr hdet_pos
  -- Negative det: CL zL reverses orientation
  have hL : Orientation.map _ eL.toLinearEquiv σL = -σL :=
      (Orientation.map_eq_neg_iff_det_neg σL _ hcard).mpr hdet_neg
  -- From hcompU and hU: σU = τU
  rw [hU] at hcompU
  -- From hcompL and hL: -σL = τL
  rw [hL] at hcompL
  have hsignP : σU = σL := by
    simp only [σU, σL]
    congr 1
    exact (orient.chartSign p).apply_eq_of_isPreconnected hpc_p (mem_univ _) (mem_univ _)
  have hsignQ : τU = τL := by
    simp only [τU, τL]
    congr 1
    exact (orient.chartSign q).apply_eq_of_isPreconnected hpc_q (mem_univ _) (mem_univ _)
  have hcontra : σU = -σU := by
    calc
      σU = τU := hcompU
      _ = τL := hsignQ
      _ = -σL := hcompL.symm
      _ = -σU := by simp [hsignP]
  exact Module.Ray.ne_neg_self σU hcontra

end MoebiusBand
