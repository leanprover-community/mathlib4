/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.Algebra.Module.Equiv

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option linter.unusedSectionVars false

/-! ## Existence of a Riemannian bundle metric

Using a partition of unity, we prove the existence of a smooth Riemannian metric.
Specialized attempt.

-/

open Bundle ContDiff Manifold

-- Let E be a smooth vector bundle over a manifold E

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [InnerProductSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB ω B] [ContMDiffVectorBundle ω F E IB]

noncomputable instance : TopologicalSpace (TotalSpace EB (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) :=
  inferInstanceAs (TopologicalSpace (TangentBundle IB B))

section

variable (E) in
/-- This is the bundle `Hom_ℝ(E, T)`, where `T` is the rank one trivial bundle over `B`. -/
private def V : (b : B) → Type _ := (fun b ↦ E b →L[ℝ] Trivial B ℝ b)

noncomputable instance : (x : B) → TopologicalSpace (V E x) := by
  unfold V
  infer_instance

noncomputable instance : (x : B) → AddCommGroup (V E x) := by
  unfold V
  infer_instance

noncomputable instance (x : B) : Module ℝ (V E x) := by
  unfold V
  infer_instance

noncomputable instance : TopologicalSpace (TotalSpace (F →L[ℝ] ℝ) (V E)) := by
  unfold V
  infer_instance

noncomputable instance : FiberBundle (F →L[ℝ] ℝ) (V E) := by
  unfold V
  infer_instance

noncomputable instance : VectorBundle ℝ (F →L[ℝ] ℝ) (V E) := by
  unfold V
  infer_instance

noncomputable instance :
VectorBundle ℝ (EB →L[ℝ] ℝ) (V (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) := by
  unfold V
  infer_instance

noncomputable instance : ContMDiffVectorBundle n (F →L[ℝ] ℝ) (V E) IB := by
  unfold V
  infer_instance

instance (x : B) : ContinuousAdd (V E x) := by
  unfold V
  infer_instance

instance (x : B) : ContinuousSMul ℝ (V E x) := by
  unfold V
  infer_instance

instance (x : B) : IsTopologicalAddGroup (V E x) := by
  unfold V
  infer_instance

example : ContMDiffVectorBundle n (F →L[ℝ] F →L[ℝ] ℝ) (fun b ↦ E b →L[ℝ] V E b) IB :=
  ContMDiffVectorBundle.continuousLinearMap (IB := IB) (n := n)
    (F₁ := F) (E₁ := E) (F₂ := F →L[ℝ] ℝ) (E₂ := V E)

example : ContMDiffVectorBundle n (EB →L[ℝ] EB →L[ℝ] ℝ)
(fun b ↦ (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ] V (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b)
IB :=
  ContMDiffVectorBundle.continuousLinearMap (IB := IB) (n := n)
  (F₁ := EB) (E₁ := (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) (F₂ := EB →L[ℝ] ℝ)
  (E₂ := V (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _))

variable (E) in
/-- The real vector bundle `Hom(E, Hom(E, T)) = Hom(E, V)`, whose fiber at `x` is
(equivalent to) the space of continuous real bilinear maps `E x → E x → ℝ`. -/
private def W : (b : B) → Type _ := fun b ↦ E b →L[ℝ] V E b

noncomputable instance (x : B) : TopologicalSpace (W E x) := by
  unfold W
  infer_instance

noncomputable instance (x : B) : AddCommGroup (W E x) := by
  unfold W
  infer_instance

noncomputable instance (x : B) : Module ℝ (W E x) := by
  unfold W
  infer_instance

noncomputable instance : TopologicalSpace (TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) (W E)) := by
  unfold W
  infer_instance

noncomputable instance : FiberBundle (F →L[ℝ] F →L[ℝ] ℝ) (W E) := by
  unfold W
  infer_instance

noncomputable instance : VectorBundle ℝ (F →L[ℝ] F →L[ℝ] ℝ) (W E) := by
  unfold W
  infer_instance

noncomputable instance : ContMDiffVectorBundle n (F →L[ℝ] F →L[ℝ] ℝ) (W E) IB := by
  unfold W
  infer_instance

instance (x : B) : ContinuousAdd (W E x) := by
  unfold W
  infer_instance

instance (x : B) : ContinuousSMul ℝ (W E x) := by
  unfold W
  infer_instance

instance (x : B) : IsTopologicalAddGroup (W E x) := by
  unfold W
  infer_instance

end

noncomputable def g (i : B) (p : B) (v w : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) : ℝ :=
  letI dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  @Inner.inner ℝ EB _ (dψ v) (dψ w)

noncomputable def g_comp (i : B) :
  B × TangentBundle IB B × TangentBundle IB B → ℝ :=
  fun x =>
    let f := Bundle.TotalSpace.snd ∘ tangentMap IB 𝓘(ℝ, EB) (extChartAt IB i)
    ((fun x ↦ @Inner.inner ℝ EB _ x.1 x.2) ∘ Prod.map f f) (x.2)

noncomputable def G (i : B) (x : B) (v : TangentSpace IB x) :
  TangentBundle IB B → ℝ
| (⟨y, w⟩) =>
    @Inner.inner ℝ EB _
      (Bundle.TotalSpace.snd (tangentMap IB 𝓘(ℝ, EB) (extChartAt IB i) ⟨x, v⟩))
      (Bundle.TotalSpace.snd (tangentMap IB 𝓘(ℝ, EB) (extChartAt IB i) ⟨y, w⟩))

theorem contMDiff_G (i x : B) (v : TangentSpace IB x) :
  ContMDiff (IB.tangent) (𝓘(ℝ, ℝ)) ω (G i x v) := by

  have : ContMDiffOn IB 𝓘(ℝ, EB) ω (extChartAt IB i) (chartAt HB i).source :=
      contMDiffOn_extChartAt

  have h_tangent :
   ContMDiffOn IB.tangent (𝓘(ℝ, EB).tangent) (ω-1)
    (tangentMapWithin IB 𝓘(ℝ, EB) (extChartAt IB i) (chartAt HB i).source)
    (TotalSpace.proj ⁻¹' (chartAt HB i).source) :=
    ContMDiffOn.contMDiffOn_tangentMapWithin this
      (OrderTop.le_top (ω - 1 + 1)) (IsOpen.uniqueMDiffOn (chartAt HB i).open_source)

  have h_snd : ContMDiff ((𝓘(ℝ, EB)).tangent) (𝓘(ℝ, EB)) ⊤
    (fun p : TangentBundle (𝓘(ℝ, EB)) EB => Bundle.TotalSpace.snd p) := by
      exact contMDiff_snd_tangentBundle_modelSpace EB 𝓘(ℝ, EB)

  have h_sndOn : ContMDiffOn ((𝓘(ℝ, EB)).tangent) (𝓘(ℝ, EB)) ⊤
    (fun p : TangentBundle (𝓘(ℝ, EB)) EB => Bundle.TotalSpace.snd p) ⊤ := fun x a ↦ h_snd x

  -- So far we have (p, v) ↦ d(ψᵢ)ₚ(v) is smooth
  have h_fiber : ContMDiffOn IB.tangent 𝓘(ℝ, EB) ω
    ((fun p ↦ p.snd) ∘ tangentMapWithin IB 𝓘(ℝ, EB) (↑(extChartAt IB i)) (chartAt HB i).source)
    (TotalSpace.proj ⁻¹' (chartAt HB i).source) :=
      ContMDiffOn.comp h_sndOn h_tangent (fun ⦃a⦄ a ↦ trivial)

  have h_inneq : ContDiff ℝ ω fun (w : EB) ↦ @Inner.inner ℝ EB _ v w := by
    exact contDiff_inner.comp (ContDiff.prodMk contDiff_const contDiff_id)
  have h_inner : ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ⊤ fun (w : EB) ↦ @Inner.inner ℝ EB _ v w := by
    apply ContDiff.contMDiff
    exact h_inneq
  have h_innerOn : ContMDiffOn 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ⊤ (fun (w : EB) ↦ @Inner.inner ℝ EB _ v w) ⊤ :=
    fun x a ↦ h_inner x

  have : ContMDiffOn IB.tangent 𝓘(ℝ, ℝ) ω
   ((fun w ↦ @Inner.inner ℝ EB _ v w) ∘
    (fun p ↦ p.snd) ∘
    tangentMapWithin IB 𝓘(ℝ, EB) (↑(extChartAt IB i)) (chartAt HB i).source)
    (TotalSpace.proj ⁻¹' (chartAt HB i).source) :=
      ContMDiffOn.comp h_innerOn h_fiber (fun ⦃a⦄ a ↦ trivial)
  unfold G
  exact sorry

example : ContDiff ℝ ω fun (p : EB × EB) ↦ @Inner.inner ℝ EB _ p.1 p.2 := contDiff_inner

example (i : B) :
  ContMDiffOn (IB.tangent) (𝓘(ℝ, EB).tangent) (ω - 1)
    (tangentMapWithin IB 𝓘(ℝ, EB) (extChartAt IB i) (chartAt HB i).source)
    (Bundle.TotalSpace.proj ⁻¹' (chartAt HB i).source) := by
  apply ContMDiffOn.contMDiffOn_tangentMapWithin
  · have : ContMDiffOn IB 𝓘(ℝ, EB) ω (extChartAt IB i) (chartAt HB i).source :=
      contMDiffOn_extChartAt
    exact this
  · exact OrderTop.le_top (ω - 1 + 1)
  · exact IsOpen.uniqueMDiffOn (chartAt HB i).open_source

lemma g_add' (i p : B) (x y v : TangentSpace IB p) :
  g i p v (x + y) = g i p v x + g i p v y := by
  unfold g
  let dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  have h_map : dψ (x + y) = dψ x + dψ y := ContinuousLinearMap.map_add dψ x y
  rw [h_map]
  exact @inner_add_right ℝ EB _ _ _ _ _ _

lemma g_add'' (i p : B) (x y v : TangentSpace IB p) :
  g i p (x + y) v = g i p x v + g i p y v := by
  unfold g
  let dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  have h_map : dψ (x + y) = dψ x + dψ y := ContinuousLinearMap.map_add dψ x y
  rw [h_map]
  exact @inner_add_left ℝ EB _ _ _ _ _ _

lemma g_smul' (i p : B) (x v : TangentSpace IB p) (m : ℝ) :
  g i p v (m • x) = (RingHom.id ℝ) m • g i p v x := by
  unfold g
  let dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  have : dψ (m • x) = m • dψ x := ContinuousLinearMap.map_smul_of_tower dψ m x
  rw [this]
  have : @Inner.inner ℝ EB _ (dψ v) (m • (dψ x)) = m • @Inner.inner ℝ EB _ (dψ v) (dψ x) :=
    @inner_smul_right_eq_smul ℝ EB _ _ _ _ _ _ _ _ _ _ (dψ v) (dψ x) m
  exact this

lemma g_smul'' (i p : B) (x v : TangentSpace IB p) (m : ℝ) :
  g i p (m • v) x = (RingHom.id ℝ) m • g i p v x := by
  unfold g
  let dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  have : dψ (m • v) = m • dψ v := ContinuousLinearMap.map_smul_of_tower dψ m v
  rw [this]
  have : @Inner.inner ℝ EB _ (m • (dψ v)) (dψ x) = m • @Inner.inner ℝ EB _ (dψ v) (dψ x) :=
    @inner_smul_left_eq_smul ℝ EB _ _ _ _ _ _ _ _ _ _ _ (dψ v) (dψ x) m
  exact this

lemma g_symm (i p : B) (v w : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) :
  g i p v w = g i p w v := by
  unfold g
  rw [real_inner_comm]

lemma g_nonneg (i p : B) (v : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) :
  0 ≤ g i p v v := by
  unfold g
  exact @inner_self_nonneg ℝ _ _ _ _ _

lemma g_pos (i p : B) (hp : p ∈ (extChartAt IB i).source)
            (v : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) (hv : v ≠ 0) :
    0 < g i p v v := by
  let ψ := extChartAt IB i
  let dψ := mfderiv IB 𝓘(ℝ, EB) ψ p
  have h_invert : dψ.IsInvertible := isInvertible_mfderiv_extChartAt hp
  obtain ⟨inv, left_inv⟩ := h_invert
  have inj : Function.Injective inv := inv.injective
  have h1 : inv v = dψ v := by
    rw[← left_inv]
    exact inj (inj (inj (inj rfl)))
  have hx : dψ v ≠ 0 := by
    intro h
    have h2 : inv v = inv 0 := by simp [h, h1]
    exact hv (inj h2)
  exact real_inner_self_pos.mpr hx

lemma g_cont (i p : B) (v : TangentSpace IB p) :
  Continuous (fun w ↦ g i p v w) := by
  unfold g

  have continuous_inner_left {v : EB} : Continuous (fun w ↦ @Inner.inner ℝ EB _ v w) :=
    continuous_inner.comp (continuous_const.prodMk continuous_id)

  have h_desired : Continuous fun w ↦
  @Inner.inner ℝ EB _ ((mfderiv IB 𝓘(ℝ, EB) (↑(extChartAt IB i)) p) v)
    ((mfderiv IB 𝓘(ℝ, EB) (↑(extChartAt IB i)) p) w) := by
    exact continuous_inner_left |>.comp (mfderiv IB 𝓘(ℝ, EB) (↑(extChartAt IB i)) p).continuous

  exact h_desired

noncomputable
def g_bilinear (i p : B) :
    W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p :=
  ContinuousLinearMap.mk
    { toFun := fun v ↦
        ContinuousLinearMap.mk
          { toFun := fun w ↦ g i p v w
            map_add' := fun x y ↦ g_add' i p x y v
            map_smul' := fun m x ↦ g_smul' i p x v m }
          (g_cont i p v)
      map_add' := fun x y ↦ by
                    apply ContinuousLinearMap.ext
                    intro w
                    change g i p (x + y) w = g i p x w + g i p y w
                    exact g_add'' i p x y w
      map_smul' := fun m x ↦ by
                    apply ContinuousLinearMap.ext
                    intro w
                    change g i p (m • x) w = m • g i p x w
                    exact g_smul'' i p w x m }
    (by sorry : Continuous _)

open SmoothPartitionOfUnity

noncomputable instance (x : B) : NormedAddCommGroup (W (TangentSpace IB) x) :=
  show NormedAddCommGroup (TangentSpace IB x →L[ℝ] (TangentSpace IB x →L[ℝ] ℝ)) from
    inferInstance

noncomputable instance :
  TopologicalSpace (TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
                   (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _))) := by
    unfold W
    infer_instance

noncomputable instance : TopologicalSpace (TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
  (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _))) := by
  unfold W
  infer_instance

#check SmoothBumpCovering.IsSubordinate.toSmoothPartitionOfUnity

#print SmoothPartitionOfUnity
#check tsupport

variable [FiniteDimensional ℝ EB] [IsManifold IB ω B] [SigmaCompactSpace B] [T2Space B]

noncomputable
def g_global (f : SmoothPartitionOfUnity B IB B) :
    ∀ (p : B), TangentSpace IB p → TangentSpace IB p → ℝ :=
  fun p v w ↦ ∑ᶠ i : B, (f i p) * g i p v w

lemma g_global_add' (f : SmoothPartitionOfUnity B IB B) (p : B) (x y v : TangentSpace IB p) :
  g_global f p v (x + y) = g_global f p v x + g_global f p v y := by
  unfold g_global
  simp_rw [g_add', mul_add]
  have h1 : (Function.support fun i ↦ (f i) p * g i p v x).Finite := by
    apply (f.locallyFinite'.point_finite p).subset
    intro i hi
    simp [Function.mem_support] at hi ⊢
    have :  (f i) p ≠ 0 ∧ g i p v x ≠ 0 := hi
    have : (f i) p * g i p v x ≠ 0 := mul_ne_zero_iff.mpr this
    exact mul_ne_zero_iff.mp this |>.1
  have h2 : (Function.support fun i ↦ (f i) p * g i p v y).Finite := by
    apply (f.locallyFinite'.point_finite p).subset
    intro i hi
    simp [Function.mem_support] at hi ⊢
    have :  (f i) p ≠ 0 ∧ g i p v y ≠ 0 := hi
    have : (f i) p * g i p v y ≠ 0 := mul_ne_zero_iff.mpr this
    exact mul_ne_zero_iff.mp this |>.1
  exact @finsum_add_distrib _ ℝ _ _ _ h1 h2

lemma g_global_smul' (f : SmoothPartitionOfUnity B IB B) (p : B) (x v : TangentSpace IB p)
                     (m : ℝ) :
  g_global f p v (m • x) = (RingHom.id ℝ) m • g_global f p v x := by
  unfold g_global
  simp_rw [g_smul']
  simp_rw [mul_smul_comm]
  have : ∑ᶠ (i : B), (RingHom.id ℝ) m • ((f i) p * g i p v x) =
         (RingHom.id ℝ) m • ∑ᶠ (i : B), (f i) p * g i p v x :=
    Eq.symm (smul_finsum ((RingHom.id ℝ) m) fun i ↦ (f i) p * g i p v x)
  exact this

lemma g_global_symm (f : SmoothPartitionOfUnity B IB B)
        (p : B) (v w : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) :
  g_global f p v w = g_global f p w v := by
    unfold g_global
    have : ∑ᶠ (i : B), (f i) p * g i p v w = ∑ᶠ (i : B), (f i) p * g i p w v := by
      simp_rw [g_symm]
    exact this

lemma g_global_pos (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
  (p : B) (v : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) :
  v ≠ 0 → 0 < g_global f p v v := by
  intro hv
  unfold g_global
  have h_nonneg : ∀ i, 0 ≤ f.toFun i p := fun i => f.nonneg' i p
  have ⟨i, hi_pos⟩ : ∃ i, 0 < f i p := by
    by_contra hneg
    push_neg at hneg
    have : ∀ (x : B), f x p = 0 := fun x => le_antisymm (hneg x) (h_nonneg x)
    have h1 : ∑ᶠ i, f i p = 0 := finsum_eq_zero_of_forall_eq_zero this
    have h2 : ∑ᶠ i, f i p = 1 := f.sum_eq_one' p trivial
    exact absurd (h1.symm.trans h2) one_ne_zero.symm
  have hi_chart : p ∈ (extChartAt IB i).source := by
    apply h_sub
    apply subset_closure
    exact Function.mem_support.mpr hi_pos.ne'
  let h x := f x p * g x p v v
  have h1 : ∀ j, 0 ≤ h j := fun j => mul_nonneg (h_nonneg j) (g_nonneg j p v)
  have h2 : ∃ j, 0 < h j := ⟨i, mul_pos hi_pos (g_pos i p hi_chart v hv)⟩
  have h3 : (Function.support h).Finite := by
    apply (f.locallyFinite'.point_finite p).subset
    intro x hx
    simp [Function.mem_support, h] at hx
    have : f x p ≠ 0 ∧ g x p v v ≠ 0 := hx
    have : (f x) p * g x p v v ≠ 0 := mul_ne_zero_iff.mpr this
    exact mul_ne_zero_iff.mp this |>.1
  have h4 : 0 < ∑ᶠ i, h i := finsum_pos' h1 h2 h3
  exact h4

lemma g_global_cont (f : SmoothPartitionOfUnity B IB B) (p : B) (v : TangentSpace IB p) :
  Continuous (fun w ↦ g_global f p v w) := sorry

noncomputable
def g_global_bilinear (f : SmoothPartitionOfUnity B IB B) (p : B) :
    W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p :=
  ContinuousLinearMap.mk
    { toFun := fun v ↦
        ContinuousLinearMap.mk
          { toFun := fun w ↦ g_global f p v w
            map_add' := fun x y ↦ g_global_add' f p x y v
            map_smul' := fun m x ↦ g_global_smul' f p x v m }
          (g_global_cont f p v)
      map_add' := sorry
      map_smul' := sorry }
    sorry

lemma g_global_bilinear_eq_sum (f : SmoothPartitionOfUnity B IB B) (p : B) :
  g_global_bilinear f p = ∑ᶠ (j : B), (f j) p • g_bilinear j p := by
  unfold W at *
  simp only [g_global_bilinear, g_global]
  ext v
  simp only [ContinuousLinearMap.coe_mk']
  exact sorry

lemma bar (f : SmoothPartitionOfUnity B IB B)
        (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
  ContMDiff IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞ fun x ↦
    TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x
                   ((∑ᶠ (j : B), (f j) x • g_bilinear j x :  W (TangentSpace IB) x)) := by
      have h := contMDiff_totalSpace_weighted_sum_of_local_sections
        (E := EB) (I := IB) (M := B)
        (V := fun b => TangentSpace IB b →L[ℝ] (TangentSpace IB b →L[ℝ] Trivial B ℝ b))
        (F_fiber := EB →L[ℝ] (EB →L[ℝ] ℝ))
        (n := (⊤ : ℕ∞)) (ι := B)
        (ρ := f)
        (s_loc := g_bilinear)
        (U := fun x ↦ (extChartAt IB x).source)
        (by intro i; exact isOpen_extChartAt_source i)
        h_sub
        (by intro i; sorry)
      exact h

lemma g_global_bilinear_smooth (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
  ContMDiff IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_global_bilinear f x)) := by
  simp_rw [g_global_bilinear_eq_sum]
  exact (bar f h_sub)

example : (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) =
  fun b ↦ (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ]
          ((@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ] Trivial B ℝ b)
   := rfl

noncomputable
def g_global_smooth_section
    (f : SmoothPartitionOfUnity B IB B)
    (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
    ContMDiffSection (I := IB) (F := (EB →L[ℝ] EB →L[ℝ] ℝ)) (n := ∞)
      (V := (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _))) :=
  { toFun := g_global_bilinear f
    contMDiff_toFun := g_global_bilinear_smooth f h_sub}

noncomputable
def riemannian_metric_exists
    (f : SmoothPartitionOfUnity B IB B)
    (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
    (hf : f.IsSubordinate fun x ↦ (chartAt HB x).source) :
    ContMDiffRiemannianMetric (IB := IB) (n := ∞) (F := EB)
     (E := @TangentSpace ℝ _ _ _ _ _ _ IB B _ _) :=
  { inner := g_global_bilinear f
    symm := g_global_symm f
    pos := g_global_pos f (by simpa only [extChartAt_source] using hf)
    isVonNBounded := sorry
    contMDiff := (g_global_smooth_section f h_sub).contMDiff_toFun
     }


noncomputable def G (i : B) (x : B) (v : TangentSpace IB x) :
  TangentBundle IB B → ℝ
| (⟨y, w⟩) =>
    @Inner.inner ℝ EB _
      (Bundle.TotalSpace.snd (tangentMap IB 𝓘(ℝ, EB) (extChartAt IB i) ⟨x, v⟩))
      (Bundle.TotalSpace.snd (tangentMap IB 𝓘(ℝ, EB) (extChartAt IB i) ⟨y, w⟩))

theorem contMDiff_G (i x : B) (v : TangentSpace IB x) :
  ContMDiff (IB.tangent) (𝓘(ℝ, ℝ)) ω (G i x v) := by

  have : ContMDiffOn IB 𝓘(ℝ, EB) ω (extChartAt IB i) (chartAt HB i).source :=
      contMDiffOn_extChartAt

  have h_tangent :
   ContMDiffOn IB.tangent (𝓘(ℝ, EB).tangent) (ω-1)
    (tangentMapWithin IB 𝓘(ℝ, EB) (extChartAt IB i) (chartAt HB i).source)
    (TotalSpace.proj ⁻¹' (chartAt HB i).source) :=
    ContMDiffOn.contMDiffOn_tangentMapWithin this
      (OrderTop.le_top (ω - 1 + 1)) (IsOpen.uniqueMDiffOn (chartAt HB i).open_source)

  have h_snd : ContMDiff ((𝓘(ℝ, EB)).tangent) (𝓘(ℝ, EB)) ⊤
    (fun p : TangentBundle (𝓘(ℝ, EB)) EB => Bundle.TotalSpace.snd p) := by
      exact contMDiff_snd_tangentBundle_modelSpace EB 𝓘(ℝ, EB)

  have h_sndOn : ContMDiffOn ((𝓘(ℝ, EB)).tangent) (𝓘(ℝ, EB)) ⊤
    (fun p : TangentBundle (𝓘(ℝ, EB)) EB => Bundle.TotalSpace.snd p) ⊤ := fun x a ↦ h_snd x

  -- So far we have (p, v) ↦ d(ψᵢ)ₚ(v) is smooth
  have h_fiber : ContMDiffOn IB.tangent 𝓘(ℝ, EB) ω
    ((fun p ↦ p.snd) ∘ tangentMapWithin IB 𝓘(ℝ, EB) (↑(extChartAt IB i)) (chartAt HB i).source)
    (TotalSpace.proj ⁻¹' (chartAt HB i).source) :=
      ContMDiffOn.comp h_sndOn h_tangent (fun ⦃a⦄ a ↦ trivial)

  have h_inneq : ContDiff ℝ ω fun (w : EB) ↦ @Inner.inner ℝ EB _ v w := by
    exact contDiff_inner.comp (ContDiff.prodMk contDiff_const contDiff_id)
  have h_inner : ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ⊤ fun (w : EB) ↦ @Inner.inner ℝ EB _ v w := by
    apply ContDiff.contMDiff
    exact h_inneq
  have h_innerOn : ContMDiffOn 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ⊤ (fun (w : EB) ↦ @Inner.inner ℝ EB _ v w) ⊤ :=
    fun x a ↦ h_inner x

  have : ContMDiffOn IB.tangent 𝓘(ℝ, ℝ) ω
   ((fun w ↦ @Inner.inner ℝ EB _ v w) ∘
    (fun p ↦ p.snd) ∘
    tangentMapWithin IB 𝓘(ℝ, EB) (↑(extChartAt IB i)) (chartAt HB i).source)
    (TotalSpace.proj ⁻¹' (chartAt HB i).source) :=
      ContMDiffOn.comp h_innerOn h_fiber (fun ⦃a⦄ a ↦ trivial)
  unfold G
  exact sorry

example : ContDiff ℝ ω fun (p : EB × EB) ↦ @Inner.inner ℝ EB _ p.1 p.2 := contDiff_inner

example (i : B) :
  ContMDiffOn (IB.tangent) (𝓘(ℝ, EB).tangent) (ω - 1)
    (tangentMapWithin IB 𝓘(ℝ, EB) (extChartAt IB i) (chartAt HB i).source)
    (Bundle.TotalSpace.proj ⁻¹' (chartAt HB i).source) := by
  apply ContMDiffOn.contMDiffOn_tangentMapWithin
  · have : ContMDiffOn IB 𝓘(ℝ, EB) ω (extChartAt IB i) (chartAt HB i).source :=
      contMDiffOn_extChartAt
    exact this
  · exact OrderTop.le_top (ω - 1 + 1)
  · exact IsOpen.uniqueMDiffOn (chartAt HB i).open_source
