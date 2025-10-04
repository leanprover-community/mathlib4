/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Elaborators
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Miscellaneous pre-requisites for covariant derivatives

TODO: this file should not exist; move everything in here to a proper place
(and PR it accordingly)

-/

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

section prerequisites

open Bundle Filter Function Topology Set

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 0 M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  -- `V` vector bundle

def bar (a : 𝕜) : TangentSpace 𝓘(𝕜) a ≃L[𝕜] 𝕜 where
  toFun v := v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

@[simp]
theorem Bundle.Trivial.mdifferentiableAt_iff (σ : (x : E) → Trivial E E' x) (e : E) :
    MDiffAt (T% σ) e ↔ DifferentiableAt 𝕜 σ e := by
  simp [mdifferentiableAt_totalSpace, mdifferentiableAt_iff_differentiableAt]

attribute [simp] mdifferentiableAt_iff_differentiableAt

lemma FiberBundle.trivializationAt.baseSet_mem_nhds {B : Type*} (F : Type*)
    [TopologicalSpace B] [TopologicalSpace F]
    (E : B → Type*) [TopologicalSpace (TotalSpace F E)] [(b : B) → TopologicalSpace (E b)]
    [FiberBundle F E] (b : B) : (trivializationAt F E b |>.baseSet) ∈ 𝓝 b :=
  (trivializationAt F E b).open_baseSet.eventually_mem (FiberBundle.mem_baseSet_trivializationAt' b)

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [(x : M) → Module 𝕜 (V x)]
     [(x : M) → AddCommGroup (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V] in
variable {I F V x} in
/-- If two sections `σ` and `σ'` are equal on a neighbourhood `s` of `x`,
if one is differentiable at `x` then so is the other.
Issue: EventuallyEq does not work for dependent functions. -/
lemma mdifferentiableAt_dependent_congr {σ σ' : Π x : M, V x} {s : Set M} (hs : s ∈ nhds x)
    (hσ₁ : MDiffAt (T% σ) x) (hσ₂ : ∀ x ∈ s, σ x = σ' x) :
    MDiffAt (T% σ') x := by
  apply MDifferentiableAt.congr_of_eventuallyEq hσ₁
  -- TODO: split off a lemma?
  apply Set.EqOn.eventuallyEq_of_mem _ hs
  intro x hx
  simp [hσ₂, hx]

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [(x : M) → Module 𝕜 (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V] [(x : M) → AddCommGroup (V x)] in
variable {I F V x} in
/-- If two sections `σ` and `σ'` are equal on a neighbourhood `s` of `x`,
one is differentiable at `x` iff the other is. -/
lemma mdifferentiable_dependent_congr_iff {σ σ' : Π x : M, V x} {s : Set M} (hs : s ∈ nhds x)
    (hσ : ∀ x ∈ s, σ x = σ' x) :
    MDiffAt (T% σ) x  ↔ MDiffAt (T% σ') x :=
  ⟨fun h ↦ mdifferentiableAt_dependent_congr hs h hσ,
   fun h ↦ mdifferentiableAt_dependent_congr hs h (fun x hx ↦ (hσ x hx).symm)⟩

end prerequisites
