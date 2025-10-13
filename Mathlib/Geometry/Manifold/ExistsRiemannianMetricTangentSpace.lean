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

omit [IsManifold IB ω B] in
lemma g_symm (i p : B) (v w : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) :
  g i p v w = g i p w v := by
  unfold g
  rw [real_inner_comm]

def linearEquivToSemiLinearEquiv
  {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]
  [TopologicalSpace E] [TopologicalSpace F]
  (e : E ≃L[ℝ] F) :
  E ≃SL[RingHom.id ℝ] F :=
{ toFun := e.toFun,
  invFun := e.invFun,
  map_add' := e.map_add,
  map_smul' := by intro r x; exact e.map_smul r x,
  left_inv := e.left_inv,
  right_inv := e.right_inv }

lemma g_pos (i p : B) (hp : p ∈ (extChartAt IB i).source)
            (v : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) :
  v ≠ 0 → 0 < g i p v v := by
  intro hv
  unfold g
  simp only
  let ψ := extChartAt IB i
  let dψ := mfderiv IB (modelWithCornersSelf ℝ EB) ψ p
  let x : EB := dψ v
  have h_invert : dψ.IsInvertible := isInvertible_mfderiv_extChartAt hp
  rcases h_invert with ⟨inv, left_inv⟩
  let e : TangentSpace IB p ≃SL[RingHom.id ℝ] TangentSpace 𝓘(ℝ, EB) (ψ p) :=
    linearEquivToSemiLinearEquiv inv
  have h5 : Function.Injective e :=  ContinuousLinearEquiv.injective e
  have inj : Function.Injective e := ContinuousLinearEquiv.injective e
  have h1 : e v = dψ v := by
    unfold e
    rw[<-left_inv]
    exact h5 (h5 (h5 (h5 rfl)))
  have hx : x ≠ 0 := by
    intro h
    have h2 : e v = e 0 := by
      rw [h1]
      simp [x, h]
    have h3 := inj h2
    exact hv h3
  exact real_inner_self_pos.mpr hx

variable [FiniteDimensional ℝ EB] [IsManifold IB ∞ B] [SigmaCompactSpace B] [T2Space B]

noncomputable
def g_global (f : SmoothPartitionOfUnity B IB B) :
    ∀ (p : B), TangentSpace IB p → TangentSpace IB p → ℝ :=
  fun p v w ↦ ∑ᶠ i : B, (f i p) * g i p v w

omit [IsManifold IB ω B] [FiniteDimensional ℝ EB] [IsManifold IB ∞ B] [SigmaCompactSpace B]
     [T2Space B]
lemma g_global_symm (f : SmoothPartitionOfUnity B IB B)
        (p : B) (v w : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) :
  g_global f p v w = g_global f p w v := by
    unfold g_global
    have : ∑ᶠ (i : B), (f i) p * g i p v w = ∑ᶠ (i : B), (f i) p * g i p w v := by
      simp_rw [g_symm]
    exact this

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
    symm := g_global_symm f
    pos := sorry
    isVonNBounded := sorry
    contMDiff := (g_global_smooth_section f hf).contMDiff_toFun
     }
