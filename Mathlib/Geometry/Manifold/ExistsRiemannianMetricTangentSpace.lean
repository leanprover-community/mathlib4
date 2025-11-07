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
  {EB : Type*} [NormedAddCommGroup EB] [InnerProductSpace ℝ EB]
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

variable (IB) in
noncomputable def g' (i p : B) : TangentSpace IB p → TangentSpace IB p → ℝ := fun v w ↦
  letI dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  @Inner.inner ℝ EB _ (dψ v) (dψ w)

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

noncomputable instance (p : B) : NormedAddCommGroup (TangentSpace IB p) := by
  change NormedAddCommGroup EB
  infer_instance

noncomputable instance (p : B) : NormedSpace ℝ (TangentSpace IB p) := by
  change NormedSpace ℝ EB
  infer_instance

noncomputable
def g_bilin (i p : B) :
  (TangentSpace IB) p →L[ℝ]  ((TangentSpace IB) p →L[ℝ] Trivial B ℝ p) := by
  let dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  let inner := innerSL ℝ (E := EB)
  exact inner.comp dψ |>.flip.comp dψ

@[simp]
theorem linear_flip_apply
  {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
  (f : E →L[𝕜] F →L[𝕜] G) (x : F) (y : E) :
  f.flip x y = f y x := rfl

theorem g_bilin_symm (i p : B) (v w : TangentSpace IB p) :
    ((g_bilin i p).toFun v).toFun w =
    ((g_bilin i p).toFun w).toFun v := by
  unfold g_bilin
  simp
  rw [real_inner_comm]

example (x y : EB) : (innerSL ℝ (E := EB)) x y = Inner.inner ℝ x y := rfl

example (x y : EB) : (innerSL ℝ (E := EB)).flip y x = (innerSL ℝ (E := EB)) x y := rfl

open SmoothPartitionOfUnity

noncomputable instance (x : B) : NormedAddCommGroup (W (TangentSpace IB) x) :=
  show NormedAddCommGroup (TangentSpace IB x →L[ℝ] (TangentSpace IB x →L[ℝ] ℝ)) from
    inferInstance

noncomputable instance :
  TopologicalSpace (TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
                   (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _))) := by
    unfold W
    infer_instance

variable [FiniteDimensional ℝ EB] [IsManifold IB ω B] [SigmaCompactSpace B] [T2Space B]

noncomputable
def g_global (f : SmoothPartitionOfUnity B IB B) :
    ∀ (p : B), TangentSpace IB p → TangentSpace IB p → ℝ :=
  fun p v w ↦ ∑ᶠ i : B, (f i p) * g i p v w

noncomputable
def g_global_bilin (f : SmoothPartitionOfUnity B IB B) (p : B) :
    W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p := ∑ᶠ (j : B), (f j) p • g_bilin j p

lemma finsum_image_eq_sum {B E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
 (φ : E →+ F) (f : B → E) (h_fin : Finset B)
 (h1 : Function.support f ⊆ h_fin) :
    ∑ᶠ j, φ (f j) = ∑ j ∈ h_fin, φ (f j) := by
  apply finsum_eq_sum_of_support_subset
  have : Function.support f ⊆ ↑h_fin := h1
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj ⊢
  have hf : f j ≠ 0 := by
    contrapose! hj
    simpa using (map_zero φ).symm ▸ congrArg φ hj
  exact h1 hf

def evalAt (b : B) (v w : TangentSpace IB b) : W (TangentSpace IB) b →+ ℝ :=
  {
    toFun := fun f => (f.toFun v).toFun w
    map_zero' := by
      simp
    map_add' := by
      intro f g
      exact rfl
  }

lemma h_need (f : SmoothPartitionOfUnity B IB B) (b : B) (v w : TangentSpace IB b)
  (h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin j b) : W (TangentSpace IB) b)).Finite) :
  ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun w =
  ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun w).toFun v := by

    have ha : ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun w =
              ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun w := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
      rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]

    have ha' : ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun w).toFun v =
              ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun w).toFun v := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
      rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]

    let h : (j : B) → W ((@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) b :=
      fun j ↦ (f j) b • g_bilin j b

    have h_inc : (Function.support h) ⊆ h_fin.toFinset :=
      Set.Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a

    have hb : ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun v).toFun w =
           ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun w :=
      finsum_image_eq_sum (evalAt b v w) h h_fin.toFinset h_inc

    have hb' : ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun w).toFun v =
           ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun w).toFun v :=
      finsum_image_eq_sum (evalAt b w v) h h_fin.toFinset h_inc

    have h_gbilin_symm : ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun v).toFun w =
                         ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun w).toFun v := by
      have h5 : ∀ (j : B), (((g_bilin j b)).toFun v).toFun w =
                           (((g_bilin j b)).toFun w).toFun v := fun j => g_bilin_symm j b v w
      have h6 : ∀ (j : B), (f j b) * ((g_bilin j b).toFun v).toFun w =
                           (f j b) * ((g_bilin j b).toFun w).toFun v :=
        fun j ↦ congrArg (HMul.hMul ((f j) b)) (h5 j)
      exact finsum_congr h6

    calc
        ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun w
          = ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun w := ha.symm
        _ = ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun v).toFun w := hb.symm
        _ = ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun w).toFun v := h_gbilin_symm
        _ = ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun w).toFun v := hb'
        _ = ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun w).toFun v := ha'

lemma foo' (f : SmoothPartitionOfUnity B IB B) (b : B) (v w : TangentSpace IB b) :
  ((g_global_bilin f b).toFun v).toFun w = ((g_global_bilin f b).toFun w).toFun v := by
  unfold g_global_bilin
  simp
  have h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin j b) :
                  W (TangentSpace IB) b)).Finite := by
      apply (f.locallyFinite'.point_finite b).subset
      intro i hi
      simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi
      simp only [Set.mem_setOf_eq, Function.mem_support, ne_eq]
      exact hi.1
  have h6a : (∑ᶠ (j : B), (f j) b • g_bilin j b) =
            ∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b := finsum_eq_sum _ h_fin
  rw [h6a]
  have : ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun w =
         ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun w).toFun v :=
    h_need f b v w h_fin
  exact this

lemma g_global_bilin_eq_sum (f : SmoothPartitionOfUnity B IB B) (p : B) :
  g_global_bilin f p = ∑ᶠ (j : B), (f j) p • g_bilin j p := rfl

lemma urk' (i : B)
 (hbase : (FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
            (fun b ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ) i).baseSet =
          (extChartAt IB i).source) : ContMDiffOn IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (fun x ↦ (TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_bilin i x) :
      TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
       (fun b ↦ (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ]
          ((@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ] ℝ))))
    (extChartAt IB i).source := by
  intros x hx
  let e := FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
              (fun b ↦ TangentSpace IB b →L[ℝ] (TangentSpace IB b →L[ℝ] ℝ)) i
  let F := fun (x : B) ↦ e.invFun (x, (e.toPartialEquiv.toFun ⟨x, g_bilin i x⟩).2)
  have h_eq : ∀ x ∈ (extChartAt IB i).source,
    TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_bilin i x) = F x := by
    intros x hx
    let p : TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
        fun x ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ := ⟨x, g_bilin i x⟩
    let pe := e.toPartialEquiv.toFun p
    let m := pe.2
    have hp : p ∈ e.toPartialEquiv.source := by
      have : e.baseSet = (extChartAt IB i).source := hbase
      simp [e.source_eq, this]
      exact Set.mem_of_mem_inter_left hx
    have : e.invFun (x, m) = p := by calc
      e.toPartialEquiv.invFun (x, m)
        = e.toPartialEquiv.invFun (e.toPartialEquiv.toFun p) := rfl
      _ = p := e.toPartialEquiv.left_inv' hp
    have h_er : TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_bilin i x)
              = e.toPartialEquiv.invFun (x, m) := by
      exact id (Eq.symm this)
    exact h_er

  have h_easier : ContMDiffOn IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞ F
                  (extChartAt IB i).source := sorry

  apply ContMDiffOn.congr h_easier h_eq
  exact hx

lemma baseSet_eq_extChartAt_source (i : B) :
    (FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
      (fun b ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ) i).baseSet =
    (extChartAt IB i).source := by
  simp only [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet,
      Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, Set.inter_univ,
      Set.inter_self, extChartAt, PartialHomeomorph.extend, PartialEquiv.trans_source,
      PartialHomeomorph.toFun_eq_coe, ModelWithCorners.source_eq, Set.preimage_univ]

lemma bar' (f : SmoothPartitionOfUnity B IB B)
        (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
  ContMDiff IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞ fun x ↦
    TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x
                   (∑ᶠ (j : B), (f j) x • g_bilin j x :  W (TangentSpace IB) x) := by
      have h := contMDiff_totalSpace_weighted_sum_of_local_sections
        (E := EB) (I := IB) (M := B)
        (V := fun b => TangentSpace IB b →L[ℝ] (TangentSpace IB b →L[ℝ] Trivial B ℝ b))
        (F_fiber := EB →L[ℝ] (EB →L[ℝ] ℝ))
        (n := (⊤ : ℕ∞)) (ι := B)
        (ρ := f)
        (s_loc := g_bilin)
        (U := fun x ↦ (extChartAt IB x).source)
        (by intro i; exact isOpen_extChartAt_source i)
        h_sub
        (by intro i; exact (urk' i (baseSet_eq_extChartAt_source i)))
      exact h

lemma g_global_bilin_smooth (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
  ContMDiff IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_global_bilin f x)) := by
  simp_rw [g_global_bilin_eq_sum]
  exact (bar' f h_sub)

noncomputable
def g_global_smooth_section'
    (f : SmoothPartitionOfUnity B IB B)
    (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
    ContMDiffSection (I := IB) (F := (EB →L[ℝ] EB →L[ℝ] ℝ)) (n := ∞)
      (V := (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _))) :=
  { toFun := g_global_bilin f
    contMDiff_toFun := g_global_bilin_smooth f h_sub}

lemma h_need' (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
  (b : B) (v : TangentSpace IB b)
  (h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin j b) : W (TangentSpace IB) b)).Finite) :
  v ≠ 0 → 0 < ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun v := by

  have ha : ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun v =
            ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun v := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]

  let h : (j : B) → W ((@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) b :=
    fun j ↦ (f j) b • g_bilin j b

  let h' x := f x b * ((g_bilin x b).toFun v).toFun v

  have h_inc : (Function.support h) ⊆ h_fin.toFinset :=
      Set.Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a

  have hb : ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun v).toFun v =
           ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun v :=
      finsum_image_eq_sum (evalAt b v v) h h_fin.toFinset h_inc

  have : ∀ j, (((f j) b • g_bilin j b).toFun v).toFun v = h' j := by
    simp
    exact fun j ↦ rfl

  intro hv
  have h_nonneg : ∀ i, 0 ≤ f.toFun i b := fun i => f.nonneg' i b
  have ⟨i, hi_pos⟩ : ∃ i, 0 < f i b := by
    by_contra hneg
    push_neg at hneg
    have : ∀ (x : B), f x b = 0 := fun x => le_antisymm (hneg x) (h_nonneg x)
    have h1 : ∑ᶠ i, f i b = 0 := finsum_eq_zero_of_forall_eq_zero this
    have h2 : ∑ᶠ i, f i b = 1 := f.sum_eq_one' b trivial
    exact absurd (h1.symm.trans h2) one_ne_zero.symm
  have hi_chart : b ∈ (extChartAt IB i).source := by
    apply h_sub
    apply subset_closure
    exact Function.mem_support.mpr hi_pos.ne'

  have h1 : ∀ j, 0 ≤ h' j := fun j => mul_nonneg (h_nonneg j) (g_nonneg j b v)
  have h2 : ∃ j, 0 < h' j := ⟨i, mul_pos hi_pos (g_pos i b hi_chart v hv)⟩
  have h3 : (Function.support h').Finite := by
    apply (f.locallyFinite'.point_finite b).subset
    intro x hx
    simp [Function.mem_support, h'] at hx
    have : f x b ≠ 0 ∧ (((g_bilin x b)).toFun v).toFun v ≠ 0 := hx
    have : (f x) b * ((g_bilin x b).toFun v).toFun v ≠ 0 := mul_ne_zero_iff.mpr this
    exact mul_ne_zero_iff.mp this |>.1
  have h4 : 0 < ∑ᶠ i, h' i := finsum_pos' h1 h2 h3

  have h5 : ∑ᶠ i, h' i  = ∑ᶠ i, (((f i) b • g_bilin i b).toFun v).toFun v := rfl
  have h6 : ∑ᶠ i, h' i  = ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun v := by
    rw [hb] at h5
    exact h5
  have h7 : ∑ᶠ i, h' i = ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun v := by
    rw [ha] at h6
    exact h6

  exact lt_of_lt_of_eq h4 h7

lemma baz (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
  (b : B) (v : TangentSpace IB b) :
  v ≠ 0 → 0 < ((g_global_bilin f b).toFun v).toFun v := by
  intro hv
  unfold g_global_bilin
  have h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin j b) :
                W (TangentSpace IB) b)).Finite := by
    apply (f.locallyFinite'.point_finite b).subset
    intro i hi
    simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi
    simp only [Set.mem_setOf_eq, Function.mem_support, ne_eq]
    exact hi.1
  have h6a : (∑ᶠ (j : B), (f j) b • g_bilin j b) =
            ∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b := finsum_eq_sum _ h_fin
  rw [h6a]
  exact h_need' f h_sub b v h_fin hv

#check Bornology.isVonNBounded_iff
#check Bornology.IsVonNBounded
#check Metric.isBounded_ball
#check Bornology.IsVonNBounded.subset

lemma eek (f : SmoothPartitionOfUnity B IB B) :
  ∀ (b : B), Bornology.IsVonNBounded ℝ
    {v  : TangentSpace IB b | ((g_global_bilin f b).toFun v).toFun v < 1} := by
  intro b
  exact sorry

noncomputable
def riemannian_metric_exists'
    (f : SmoothPartitionOfUnity B IB B)
    (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
    ContMDiffRiemannianMetric (IB := IB) (n := ∞) (F := EB)
     (E := @TangentSpace ℝ _ _ _ _ _ _ IB B _ _) :=
  { inner := g_global_bilin f
    symm := foo' f
    pos := baz f h_sub
    isVonNBounded := eek f
    contMDiff := (g_global_smooth_section' f h_sub).contMDiff_toFun
     }
