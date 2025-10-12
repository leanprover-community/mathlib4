/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

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
  [IsManifold IB ⊤ B] [ContMDiffVectorBundle ⊤ F E IB]

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

noncomputable
def g (i : B) (p : B) (v w : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) : ℝ :=
  let ψ := extChartAt IB i
  let dψ := mfderiv IB (modelWithCornersSelf ℝ EB) ψ p
  let x : EB := dψ v
  let y : EB := dψ w
  @Inner.inner ℝ EB _ x y

variable [FiniteDimensional ℝ EB] [IsManifold IB ∞ B] [SigmaCompactSpace B] [T2Space B]

noncomputable
def g_global (f : SmoothPartitionOfUnity B IB B) :
    ∀ (p : B), TangentSpace IB p → TangentSpace IB p → ℝ :=
  fun p v w ↦ ∑ᶠ i : B, (f i p) * g i p v w

example : true := by
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source IB B
  let g_global : ∀ (p : B), TangentSpace IB p → TangentSpace IB p → ℝ :=
    fun p v w ↦ ∑ᶠ i : B, (f i p) * g i p v w
  trivial

noncomputable
def g_global_bilinear (f : SmoothPartitionOfUnity B IB B) (p : B) :
    W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p :=
  ContinuousLinearMap.mk
    { toFun := fun v ↦
        ContinuousLinearMap.mk
          { toFun := fun w ↦ g_global f p v w
            map_add' := sorry
            map_smul' := sorry }
          sorry
      map_add' := sorry
      map_smul' := sorry }
    sorry

noncomputable
def g_global_smooth_section
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate fun x ↦ (chartAt HB x).source) :
    ContMDiffSection IB (EB →L[ℝ] EB →L[ℝ] ℝ) ⊤
      (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) :=
  { toFun := g_global_bilinear f
    contMDiff_toFun := sorry }

noncomputable
def riemannian_metric_exists
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate fun x ↦ (chartAt HB x).source) :
    ContMDiffRiemannianMetric (IB := IB) (n := ⊤) (F := EB)
     (E := @TangentSpace ℝ _ _ _ _ _ _ IB B _ _) :=
  { inner := g_global_bilinear f
    symm := sorry
    pos := sorry
    isVonNBounded := sorry
    contMDiff := (g_global_smooth_section f hf).contMDiff_toFun
     }
