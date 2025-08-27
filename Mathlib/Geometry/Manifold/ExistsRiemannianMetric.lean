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

def LinearMap.BilinMap.toContinuousLinearMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
    [T2Space E]
    {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]
    (f : LinearMap.BilinMap 𝕜 E G) : E →L[𝕜] E →L[𝕜] G :=
  sorry--IsLinearMap.mk' (fun x : E ↦ h.toLinearMap x |>.toContinuousLinearMap)
    --  (by constructor <;> (intros;simp)) |>.toContinuousLinearMap

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


-- is the wrong associativity; just prove things differently myself
-- TODO: remove the `Fintype ι` requirement from `Basis.linearMap` and then this definition
noncomputable def pullback_aux {ι : Type*} [Fintype ι]
    {x : B} (φ : (E x) →ₗ[ℝ] (E x) →ₗ[ℝ] ℝ)
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (b : Basis ι ℝ F) :
    (F →ₗ[ℝ] F) →ₗ[ℝ] ℝ := by
  classical
  letI g : ι × ι → ℝ := fun (i, j) ↦ φ (e.symm x (b i)) (e.symm x (b j))
  exact (b.linearMap b).constr ℝ g

-- XXX: this can be generalised a lot, right?
-- ??? where do we use that e.symm x is somewhat nice?
noncomputable def IsBilinearMap.pullback {ι : Type*} [Fintype ι]
    {x : B} {φ : (E x) → (E x) → ℝ} (_hφ : IsBilinearMap ℝ φ)
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (b : Basis ι ℝ F) :
    F →ₗ[ℝ] F →ₗ[ℝ] ℝ :=
  b.constr ℝ <| fun i ↦ b.constr ℝ (fun j ↦ φ (e.symm x (b i)) (e.symm x (b j)))

noncomputable def LinearMap.BilinMap.pullback {ι : Type*} [Fintype ι]
    {x : B} (φ : LinearMap.BilinMap ℝ (E x) ℝ)
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (b : Basis ι ℝ F) :
    LinearMap.BilinMap ℝ F ℝ :=
  b.constr ℝ <| fun i ↦ b.constr ℝ (fun j ↦ φ (e.symm x (b i)) (e.symm x (b j)))

variable [FiniteDimensional ℝ F] [T2Space F]

variable (E) in
noncomputable def pullback_clm {x : B}
    (φ : LinearMap.BilinMap ℝ (E x) ℝ) : F →L[ℝ] F →L[ℝ] ℝ :=
  letI t := trivializationAt F E x
  letI b := Basis.ofVectorSpace ℝ F
  (φ.pullback t b).toContinuousLinearMap

variable (E) in
noncomputable def IsBilinearMap.pullback_clm {x : B}
    {φ : (E x) → (E x) → ℝ} (hφ : IsBilinearMap ℝ φ) : F →L[ℝ] F →L[ℝ] ℝ :=
  letI t := trivializationAt F E x
  letI b := Basis.ofVectorSpace ℝ F
  LinearMap.BilinMap.toContinuousLinearMap (hφ.pullback t b)


omit [TopologicalSpace B] in
lemma foo (x : B) : IsBilinearMap ℝ (@Inner.inner ℝ (E x) _) where
  add_left := InnerProductSpace.add_left
  add_right := inner_add_right
  smul_left c x' y := inner_smul_left_eq_smul x' y c
  smul_right c x' y := inner_smul_right_eq_smul x' y c

noncomputable def RMetric_local_pre (x : B) : F →ₗ[ℝ] F →ₗ[ℝ] ℝ :=
  (foo x).pullback (trivializationAt F E x) (Basis.ofVectorSpace ℝ F)

variable (F E) in
noncomputable def RMetric_local (x : B) : F →L[ℝ] F →L[ℝ] ℝ := (foo x).pullback_clm E

lemma hloc (x : B) :
    ∃ U ∈ nhds x, ∃ g,
      ContMDiffOn IB 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞ g U ∧ ∀ y ∈ U, g y ∈ mapsMatchingInner F E y := by
  letI t := trivializationAt F E x
  have : t.baseSet ∈ nhds x := sorry
  use t.baseSet, this, (fun x ↦ RMetric_local F E x)
  refine ⟨?_, ?_⟩
  · sorry
  · sorry

variable [SigmaCompactSpace B] [T2Space B] [IsManifold IB ∞ B] [FiniteDimensional ℝ EB]

variable (E F IB) in
noncomputable def RMetric_aux : C^∞⟮IB, B; 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ), F →L[ℝ] F →L[ℝ] ℝ⟯ :=
  Classical.choose <|
    exists_contMDiffOn_forall_mem_convex_of_local (n := (⊤ : ℕ∞)) (I := IB)
    (t := fun x ↦ mapsMatchingInner F E x) convex_mapsMatchingInner hloc

variable (E F IB) in
/-- An arbitrary choice of bundle metric on `E`, which is smooth in the fibre. -/
def RMetric [SigmaCompactSpace B] [T2Space B] [IsManifold IB ∞ B] [FiniteDimensional ℝ EB] :
    Π (x : B), E x →L[ℝ] E x →L[ℝ] ℝ := by
  let aux := RMetric_aux IB F E
  intro x
  let aux' := aux x
  -- TODO: translate everything back (and prove this preserves smoothness...)
  sorry

lemma rMetric_contMDiff [FiniteDimensional ℝ EB] :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (RMetric IB F E b)) :=
  sorry

lemma rMetric_eq (x : B) (v w : E x) : ⟪v, w⟫ = (RMetric IB F E) x v w := sorry

/-- Every `C^n` vector bundle whose fibre admits a `C^n` partition of unity
is a `C^n` Riemannian vector bundle. (The Lean statement assumes an inner product on each fibre
already, which is why there are no other assumptions yet??) -/
lemma ContDiffVectorBundle.isContMDiffRiemannianBundle : IsContMDiffRiemannianBundle IB n F E :=
  ⟨RMetric IB F E, rMetric_contMDiff, fun x v w ↦ rMetric_eq x v w⟩
