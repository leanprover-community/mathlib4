/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! ## Existence of a Riemannian bundle metric

Using a partition of unity, we prove that every finite-dimensional smooth vector bundle
admits a smooth Riemannian metric.
Second attempt.

## TODO
- this should work for C^n; prove the same for topological bundles and add it there
- also deduce that every manifold can be made Riemannian...

-/

open Bundle ContDiff Manifold

-- Let E be a smooth vector bundle over a manifold E

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]

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

variable (E) in

def W : (b : B) → Type _ := fun b ↦ V E b →L[ℝ] Trivial B ℝ b
-- old definiton was: `E b →L[ℝ] (V E) b`, probably wrong!

noncomputable instance (x : B) : AddCommGroup (W E x) := by
  unfold W
  infer_instance

noncomputable instance (x : B) : Module ℝ (W E x) := by
  unfold W
  infer_instance

noncomputable instance : TopologicalSpace (TotalSpace ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (W E)) := by
  unfold W
  infer_instance


example : ContMDiffVectorBundle n ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (fun b ↦ V E b →L[ℝ] Trivial B ℝ b) IB :=
  ContMDiffVectorBundle.continuousLinearMap (IB := IB) (n := n) (F₁ := F →L[ℝ] ℝ) (E₁ := V E)
    (E₂ := Bundle.Trivial B ℝ) (F₂ := ℝ)

noncomputable instance (x : B) : TopologicalSpace (W E x) := by
  unfold W
  infer_instance

noncomputable instance : FiberBundle ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (W E) := by
  unfold W
  infer_instance

noncomputable instance : VectorBundle ℝ ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (W E) := by
  unfold W
  infer_instance

noncomputable instance : ContMDiffVectorBundle n ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (W E) IB := by
  unfold W
  infer_instance

end

#exit

/-

variable (E) in
def mapsMatchingInner3 (x : B) : Set (W E x) :=
  {φ : E x →L[ℝ] E x →L[ℝ] ℝ | ∀ v w : E x, φ v w = ⟪v, w⟫}

variable (E) in
omit [TopologicalSpace B] [VectorBundle ℝ F E] in
lemma convex_mapsMatchingInner3 (x : B) : Convex ℝ (mapsMatchingInner3 E x) := by
  intro φ hφ ψ hψ r s hr hs hrs
  simp_all only [W]
  simp only [mapsMatchingInner3] at hφ hψ ⊢
  erw [Set.mem_setOf] at hφ hψ ⊢
  intro v w
  specialize hφ v w
  specialize hψ v w
  sorry -- some issue is blocking the rewrites!
  -- simp [hφ v w, hψ v w]
  -- grind

lemma hloc3 (x₀ : B) :
    ∃ U_x₀ ∈ nhds x₀, ∃ s_loc : (x : B) → W E x,
      ContMDiffOn IB (IB.prod 𝓘(ℝ, ℝ →L[ℝ] ℝ)) ∞ (fun x ↦ TotalSpace.mk' (ℝ →L[ℝ] ℝ) x (s_loc x)) U_x₀ ∧
      ∀ y ∈ U_x₀, s_loc y ∈ (fun x ↦ mapsMatchingInner3 E x) y :=
  sorry
  -- construct a local section using a local frame?

variable (E F IB) in
-- XXX: do I want this return type instead? C^∞⟮IB, B; 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ), F →L[ℝ] F →L[ℝ] ℝ⟯
noncomputable def RMetric_aux : Cₛ^∞⟮IB; ℝ →L[ℝ] ℝ, W E⟯ :=
  Classical.choose <|
    exists_contMDiffOn_section_forall_mem_convex_of_local IB (V := W E) (n := (⊤ : ℕ∞))
      (t := fun x ↦ mapsMatchingInner3 E x) (convex_mapsMatchingInner3 E) hloc3


-/


def foo : ContMDiffRiemannianMetric IB n F E :=
  sorry

#exit
section -- Building continuous bilinear maps

structure IsBilinearMap (R : Type*) {E F G : Type*} [Semiring R]
  [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid G]
  [Module R E] [Module R F] [Module R G] (f : E → F → G) : Prop where
  add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂) y = f x₁ y + f x₂ y
  smul_left : ∀ (c : R) (x : E) (y : F), f (c • x) y = c • f x y
  add_right : ∀ (x : E) (y₁ y₂ : F), f x (y₁ + y₂) = f x y₁ + f x y₂
  smul_right : ∀ (c : R) (x : E) (y : F), f x (c • y) = c • f x y

def IsBilinearMap.toLinearMap {R : Type*} {E F G : Type*} [CommSemiring R]
    [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid G]
    [Module R E] [Module R F] [Module R G] {f : E → F → G} (hf : IsBilinearMap R f) :
    E →ₗ[R] F →ₗ[R] G :=
  LinearMap.mk₂ _ f hf.add_left hf.smul_left hf.add_right hf.smul_right

lemma isBilinearMap_eval (R : Type*) (E F : Type*) [CommSemiring R]
    [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F] :
    IsBilinearMap R (fun (e : E) (φ : E →ₗ[R] F) ↦ φ e) := by
  constructor <;> simp

def IsBilinearMap.toContinuousLinearMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
    [T2Space E]
    {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]
    [T2Space F]
    {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]
    {f : E → F → G} (h : IsBilinearMap 𝕜 f) : E →L[𝕜] F →L[𝕜] G :=
  IsLinearMap.mk' (fun x : E ↦ h.toLinearMap x |>.toContinuousLinearMap)
      (by constructor <;> (intros;simp)) |>.toContinuousLinearMap

@[simp]
lemma IsBilinearMap.toContinuousLinearMap_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
    [T2Space E]
    {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]
    [T2Space F]
    {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]
    {f : E → F → G} (h : IsBilinearMap 𝕜 f) (e : E) (f' : F) :
    h.toContinuousLinearMap e f' = f e f' := rfl

lemma LinearMap.BilinMap.isBilinearMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
    [T2Space E]
    {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]
    (f : LinearMap.BilinMap 𝕜 E G) : IsBilinearMap 𝕜 (f.toFun · : E → E → G) where
  add_left := by intros; simp
  add_right := by intros; simp
  smul_left := by intros; simp
  smul_right := by intros; simp

def LinearMap.BilinMap.toContinuousLinearMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
    [T2Space E]
    {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]
    (f : LinearMap.BilinMap 𝕜 E G) : E →L[𝕜] E →L[𝕜] G :=
  f.isBilinearMap.toContinuousLinearMap

@[simp]
def LinearMap.BilinMap.toContinuousLinearMap_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
    [T2Space E]
    {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]
    (f : LinearMap.BilinMap 𝕜 E G) (e e' : E) : f.toContinuousLinearMap e e' = f e e' := rfl

def isBilinearMap_evalL
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (E : Type*) [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
    [T2Space E]
    (F : Type*) [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]
    [T2Space F] :
    IsBilinearMap 𝕜 (fun (e : E) (φ : E →L[𝕜] F) ↦ φ e) := by
  constructor <;> simp

def evalL
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (E : Type*) [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
    [T2Space E]
    (F : Type*) [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]
    [T2Space F] : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F :=
  (isBilinearMap_evalL 𝕜 E F).toContinuousLinearMap

end

variable (F E) in
/-- The set of bounded bi-continuous ℝ-bilinear maps from `F` to `ℝ` which agree with the given
inner product structure on `E`, when read through the trivialisations of `E`. -/
def mapsMatchingInner (x : B) : Set (F →L[ℝ] F →L[ℝ] ℝ) :=
  letI t := trivializationAt F E x
  {φ | ∀ v w : E x, φ (t v).2 (t w).2 = ⟪v, w⟫ }

omit [VectorBundle ℝ F E] in
lemma convex_mapsMatchingInner (x : B) : Convex ℝ (mapsMatchingInner F E x) := by
  intro φ hφ ψ hψ r s hr hs hrs
  simp only [mapsMatchingInner, Set.mem_setOf] at hφ hψ ⊢
  intro v w
  simp [hφ v w, hψ v w]
  grind

open Module



variable [FiniteDimensional ℝ F] [T2Space F]


variable (F E) in
noncomputable def RMetric_local (x : B) : F →L[ℝ] F →L[ℝ] ℝ := sorry

variable [SigmaCompactSpace B] [T2Space B] [hI : IsManifold IB ∞ B] [FiniteDimensional ℝ EB]

-- Consider the bundle V := Hom(E, Hom(E, ℝ)),
-- morally, the bundle of ℝ-bilinear forms on E over B.

variable (E) in
def V : (b : B) → Type _ := (fun b ↦ E b →L[ℝ] Trivial B ℝ b)

noncomputable instance : (x : B) → NormedAddCommGroup (V E x) := by
  unfold V
  infer_instance

noncomputable instance (x : B) : NormedSpace ℝ (V E x) := by
  unfold V
  infer_instance

noncomputable instance : (x : B) → Module ℝ (V E x) := by
  unfold V
  infer_instance

noncomputable instance : TopologicalSpace (TotalSpace (ℝ →L[ℝ] ℝ) (V E)) := by
  unfold V
  sorry -- infer_instance

noncomputable instance : (x : B) → TopologicalSpace (V E x) := by
  unfold V
  infer_instance

noncomputable instance : FiberBundle (ℝ →L[ℝ] ℝ) (V E) := by
  unfold V
  sorry -- infer_instance

noncomputable instance : VectorBundle ℝ (ℝ →L[ℝ] ℝ) (V E) := by
  unfold V
  sorry -- infer_instance

noncomputable instance : ContMDiffVectorBundle n (ℝ →L[ℝ] ℝ) (V E) IB := by
  unfold V
  sorry -- infer_instance

instance (x : B) : ContinuousAdd (V E x) := by
  unfold V
  infer_instance

instance (x : B) : ContinuousSMul ℝ (V E x) := by
  unfold V
  infer_instance

variable (E) in
def W : (b : B) → Type _ := fun b ↦ E b →L[ℝ] (V E) b

noncomputable instance (x : B) : NormedAddCommGroup (W E x) := by
  unfold W
  infer_instance

noncomputable instance (x : B) : Module ℝ (W E x) := by
  unfold W
  infer_instance

noncomputable instance : TopologicalSpace (TotalSpace (ℝ →L[ℝ] ℝ) (W E)) := by
  unfold W
  sorry -- infer_instance

noncomputable instance (x : B) : TopologicalSpace (W E x) := by
  unfold W
  infer_instance

noncomputable instance : FiberBundle (ℝ →L[ℝ] ℝ) (W E) := by
  unfold W
  sorry -- infer_instance

noncomputable instance : VectorBundle ℝ (ℝ →L[ℝ] ℝ) (W E) := by
  unfold W
  sorry -- infer_instance

noncomputable instance : ContMDiffVectorBundle n (ℝ →L[ℝ] ℝ) (W E) IB := by
  unfold W
  sorry -- infer_instance

variable (E) in
def mapsMatchingInner3 (x : B) : Set (W E x) :=
  {φ : E x →L[ℝ] E x →L[ℝ] ℝ | ∀ v w : E x, φ v w = ⟪v, w⟫}

variable (E) in
omit [TopologicalSpace B] [VectorBundle ℝ F E] in
lemma convex_mapsMatchingInner3 (x : B) : Convex ℝ (mapsMatchingInner3 E x) := by
  intro φ hφ ψ hψ r s hr hs hrs
  simp_all only [W]
  simp only [mapsMatchingInner3] at hφ hψ ⊢
  erw [Set.mem_setOf] at hφ hψ ⊢
  intro v w
  specialize hφ v w
  specialize hψ v w
  sorry -- some issue is blocking the rewrites!
  -- simp [hφ v w, hψ v w]
  -- grind

lemma hloc3 (x₀ : B) :
    ∃ U_x₀ ∈ nhds x₀, ∃ s_loc : (x : B) → W E x,
      ContMDiffOn IB (IB.prod 𝓘(ℝ, ℝ →L[ℝ] ℝ)) ∞ (fun x ↦ TotalSpace.mk' (ℝ →L[ℝ] ℝ) x (s_loc x)) U_x₀ ∧
      ∀ y ∈ U_x₀, s_loc y ∈ (fun x ↦ mapsMatchingInner3 E x) y :=
  sorry
  -- construct a local section using a local frame?

variable (E F IB) in
-- XXX: do I want this return type instead? C^∞⟮IB, B; 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ), F →L[ℝ] F →L[ℝ] ℝ⟯
noncomputable def RMetric_aux : Cₛ^∞⟮IB; ℝ →L[ℝ] ℝ, W E⟯ :=
  Classical.choose <|
    exists_contMDiffOn_section_forall_mem_convex_of_local IB (V := W E) (n := (⊤ : ℕ∞))
      (t := fun x ↦ mapsMatchingInner3 E x) (convex_mapsMatchingInner3 E) hloc3

variable (E F IB) in
/-- An arbitrary choice of bundle metric on `E`, which is smooth in the fibre. -/
def RMetric [SigmaCompactSpace B] [T2Space B] [IsManifold IB ∞ B] [FiniteDimensional ℝ EB] :
    Π (x : B), E x →L[ℝ] E x →L[ℝ] ℝ := by
  let aux := RMetric_aux IB E
  intro x
  let aux' := aux x
  -- TODO: translate everything back (and prove this preserves smoothness...)
  sorry

lemma rMetric_contMDiff [FiniteDimensional ℝ EB] :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (RMetric IB E b)) :=
  sorry

lemma rMetric_eq (x : B) (v w : E x) : ⟪v, w⟫ = (RMetric IB E) x v w := sorry

/-- Every `C^n` vector bundle whose fibre admits a `C^n` partition of unity
is a `C^n` Riemannian vector bundle. (The Lean statement assumes an inner product on each fibre
already, which is why there are no other assumptions yet??) -/
lemma ContDiffVectorBundle.isContMDiffRiemannianBundle : IsContMDiffRiemannianBundle IB n F E :=
  ⟨RMetric IB E, rMetric_contMDiff, fun x v w ↦ rMetric_eq x v w⟩
