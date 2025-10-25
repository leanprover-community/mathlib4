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
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

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

-- probably not that useful
noncomputable def pullback_bifunction {X Y Z : Type*} (f : X → Y) (φ : Y → Y → Z) : X → X → Z :=
  fun v w ↦ φ (f v) (f w)

open Module

section

variable {ι : Type*} [Fintype ι] {x : B}

-- is the wrong associativity; just prove things differently myself
-- TODO: remove the `Fintype ι` requirement from `Basis.linearMap` and then this definition
noncomputable def pullback_aux (φ : (E x) →ₗ[ℝ] (E x) →ₗ[ℝ] ℝ)
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (b : Basis ι ℝ F) :
    (F →ₗ[ℝ] F) →ₗ[ℝ] ℝ := by
  classical
  letI g : ι × ι → ℝ := fun (i, j) ↦ φ (e.symm x (b i)) (e.symm x (b j))
  exact (b.linearMap b).constr ℝ g

-- XXX: this can be generalised a lot, right?
-- ??? where do we use that e.symm x is somewhat nice?
noncomputable def IsBilinearMap.pullback {φ : (E x) → (E x) → ℝ} (_hφ : IsBilinearMap ℝ φ)
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (b : Basis ι ℝ F) :
    F →ₗ[ℝ] F →ₗ[ℝ] ℝ :=
  b.constr ℝ <| fun i ↦ b.constr ℝ (fun j ↦ φ (e.symm x (b i)) (e.symm x (b j)))

noncomputable def LinearMap.BilinMap.pullback (φ : LinearMap.BilinMap ℝ (E x) ℝ)
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (b : Basis ι ℝ F) :
    LinearMap.BilinMap ℝ F ℝ :=
  b.constr ℝ <| fun i ↦ b.constr ℝ (fun j ↦ φ (e.symm x (b i)) (e.symm x (b j)))

lemma LinearMap.BilinMap.pullback_apply_basis (φ : LinearMap.BilinMap ℝ (E x) ℝ)
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (b : Basis ι ℝ F) (i j : ι) :
    (φ.pullback e b) (b i) (b j) = φ (e.symm x (b i)) (e.symm x (b j)) := by
  simp [LinearMap.BilinMap.pullback]
  -- should be a standard fact, apply Finsupp.sum_single twice...
  sorry

end

variable [FiniteDimensional ℝ F] [T2Space F]

variable (F) in
noncomputable def pullback_clm {x : B}
    (φ : LinearMap.BilinMap ℝ (E x) ℝ) : F →L[ℝ] F →L[ℝ] ℝ :=
  letI t := trivializationAt F E x
  letI b := Basis.ofVectorSpace ℝ F
  (φ.pullback t b).toContinuousLinearMap

omit [VectorBundle ℝ F E] in
@[simp]
lemma pullback_clm_apply {x : B} (φ : LinearMap.BilinMap ℝ (E x) ℝ) (v w : F) :
    pullback_clm F φ v w = φ.pullback (trivializationAt F E x) (Basis.ofVectorSpace ℝ F) v w :=
  rfl

lemma pullback_clm_apply_basis {x : B} (φ : LinearMap.BilinMap ℝ (E x) ℝ) :
    letI ι := Basis.ofVectorSpaceIndex ℝ F;-- (v w : F)
    letI t := (trivializationAt F E x)
    letI b := Basis.ofVectorSpace ℝ F
    ∀ i j : ι, pullback_clm F φ i j = φ (t.symm x (b i)) (t.symm x (b j)) := by
  set ι := Basis.ofVectorSpaceIndex ℝ F
  intro i j
  simp only [pullback_clm_apply]

  set t := (trivializationAt F E x)
  set b := Basis.ofVectorSpace ℝ F
  have := φ.pullback_apply_basis t b i j
  convert this <;> sorry -- almost true!

variable (F) in
noncomputable def IsBilinearMap.pullback_clm {x : B}
    {φ : (E x) → (E x) → ℝ} (hφ : IsBilinearMap ℝ φ) : F →L[ℝ] F →L[ℝ] ℝ :=
  letI t := trivializationAt F E x
  letI b := Basis.ofVectorSpace ℝ F
  LinearMap.BilinMap.toContinuousLinearMap (hφ.pullback t b)

@[simp]
lemma IsBilinearMap.pullback_clm_apply {x : B}
    {φ : (E x) → (E x) → ℝ} (hφ : IsBilinearMap ℝ φ) (f f' : F) :
    --letI t := trivializationAt F E x
    --letI b := Basis.ofVectorSpace ℝ F
    hφ.pullback_clm F f f' =
      (hφ.pullback (trivializationAt F E x) (Basis.ofVectorSpace ℝ F)) f f' := by -- (φ.pullback t b) f f', at least on basis vectors
  simp only [IsBilinearMap.pullback_clm]
  simp only [LinearMap.BilinMap.toContinuousLinearMap_apply]
  -- XXX: is there further simplification?

omit [TopologicalSpace B] in
lemma foo (x : B) : IsBilinearMap ℝ (@Inner.inner ℝ (E x) _) where
  add_left := InnerProductSpace.add_left
  add_right := inner_add_right
  smul_left c x' y := inner_smul_left_eq_smul x' y c
  smul_right c x' y := inner_smul_right_eq_smul x' y c

-- unused
noncomputable def RMetric_local_pre (x : B) : F →ₗ[ℝ] F →ₗ[ℝ] ℝ :=
  (foo x).pullback (trivializationAt F E x) (Basis.ofVectorSpace ℝ F)

variable (F E) in
noncomputable def RMetric_local (x : B) : F →L[ℝ] F →L[ℝ] ℝ := (foo x).pullback_clm (E := E) F

-- TODO: apply simp lemma! is just .pullback

lemma hloc (x : B) :
    ∃ U ∈ nhds x, ∃ g,
      ContMDiffOn IB 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞ g U ∧ ∀ y ∈ U, g y ∈ mapsMatchingInner F E y := by
  letI t := trivializationAt F E x
  have := t.open_baseSet.mem_nhds <| FiberBundle.mem_baseSet_trivializationAt' x
  use t.baseSet, this, (fun x ↦ RMetric_local F E x)
  refine ⟨?_, ?_⟩
  · sorry
  · intro y hy
    simp only [mapsMatchingInner, Set.mem_setOf]
    intro v w
    simp only [RMetric_local, IsBilinearMap.pullback_clm_apply]
    -- IF the preimage of the basis of F is a basis of E y, prove equality on that basis
    -- What if that's not the case? Need to think harder!
    sorry

variable (E) in
/-- The set of bounded bi-continuous ℝ-bilinear maps from `E x` to `ℝ` which agree with the given
inner product structure on `E`: such a map is unique, but a priori the set of these maps
might be empty as the inner product structure a priori may not be continuous w.r.t. the given
topology on `E x`. (In finite dimensional spaces, it will be.) -/
def mapsMatchingInner2 (x : B) : Set (E x →L[ℝ] E x →L[ℝ] ℝ) :=
  {φ | ∀ v w : E x, φ v w = ⟪v, w⟫}

omit [TopologicalSpace B] [VectorBundle ℝ F E] in
lemma convex_mapsMatchingInner2 (x : B) : Convex ℝ (mapsMatchingInner2 E x) := by
  intro φ hφ ψ hψ r s hr hs hrs
  simp only [mapsMatchingInner2, Set.mem_setOf] at hφ hψ ⊢
  intro v w
  simp [hφ v w, hψ v w]
  grind

-- lemma hloc2 (x : B) :
--     ∃ U ∈ nhds x, ∃ g,
--       ContMDiffOn IB 𝓘(ℝ, E x →L[ℝ] E x →L[ℝ] ℝ) ∞ g U ∧ ∀ y ∈ U, g y ∈ mapsMatchingInner2 E y := by
--   letI t := trivializationAt F E x
--   have := t.open_baseSet.mem_nhds <| FiberBundle.mem_baseSet_trivializationAt' x
--   use t.baseSet, this, (fun x ↦ RMetric_local F E x)
--   refine ⟨?_, ?_⟩
--   · sorry
--   · intro y hy
--     simp only [mapsMatchingInner, Set.mem_setOf]
--     intro v w
--     simp only [RMetric_local, IsBilinearMap.pullback_clm_apply]
--     -- IF the preimage of the basis of F is a basis of E y, prove equality on that basis
--     -- What if that's not the case? Need to think harder!
--     sorry

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
