/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Covariant derivatives

TODO: add a more complete doc-string

-/

open Bundle Filter Function Topology

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 0 M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  -- `V` vector bundle

section prerequisites

def bar (a : 𝕜) : TangentSpace 𝓘(𝕜) a ≃L[𝕜] 𝕜 where
  toFun v := v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

-- TODO: cleanup
@[simp]
theorem Bundle.Trivial.mdifferentiableAt_iff (σ : (x : E) → Trivial E E' x) (e : E) :
    MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (fun x ↦ TotalSpace.mk' E' x (σ x)) e ↔
    DifferentiableAt 𝕜 σ e := by
  rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_totalSpace,
      mdifferentiableWithinAt_univ,  mdifferentiableWithinAt_univ]
  change MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E) id e ∧ MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') σ e ↔
    DifferentiableAt 𝕜 σ e
  simp [mdifferentiableAt_id, mdifferentiableAt_iff_differentiableAt]

attribute [simp] mdifferentiableAt_iff_differentiableAt

-- XXX: make a better version of fderiv_const_smul'', with field coefficients instead!
theorem _root_.fderiv_section_smul {𝕜 E E' : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (σ : (x : E) → Trivial E E' x) (a : 𝕜) (x : E) :
    fderiv 𝕜 (a • σ) x = a • fderiv 𝕜 σ x := by
  obtain (rfl | ha) := eq_or_ne a 0
  · simp
  · have : Invertible a := invertibleOfNonzero ha
    exact fderiv_const_smul'' ..

end prerequisites

variable (x : M)

structure CovariantDerivative where
  toFun : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)
  addX : ∀ (X X' : Π x : M, TangentSpace I x) (σ : Π x : M, V x),
    toFun (X + X') σ = toFun X σ + toFun X' σ
  smulX : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → 𝕜),
    toFun (f • X) σ = f • toFun X σ
  addσ : ∀ (X : Π x : M, TangentSpace I x) (σ σ' : Π x : M, V x) (x : M),
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x
    → MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x
    → toFun X (σ + σ') x = toFun X σ x + toFun X σ' x
  leibniz : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → 𝕜) (x : M),
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x
    → MDifferentiableAt I 𝓘(𝕜) f x
    → toFun X (f • σ) x = (f • toFun X σ) x + (bar _ <| mfderiv I 𝓘(𝕜) f x (X x)) • σ x
  smul_const_σ : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (a : 𝕜),
    toFun X (a • σ) = a • toFun X σ

namespace CovariantDerivative

attribute [coe] toFun

/-- Coercion of a `CovariantDerivative` to function -/
instance : CoeFun (CovariantDerivative I F V)
    fun _ ↦ (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  ⟨fun e ↦ e.toFun⟩

-- TODO: prove this via a DFunLike instance
lemma myext  (cov cov' : CovariantDerivative I F V)
    (h : ∀ X : (Π x : M, TangentSpace I x), ∀ (σ : Π x : M, V x), ∀ (x : M), cov X σ x = cov' X σ x) :
    cov = cov' := sorry

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
@[simp]
lemma zeroX (cov : CovariantDerivative I F V) (σ : Π x : M, V x) : cov 0 σ = 0 := by
  have := cov.addX (0 : (x : M) → TangentSpace I x) (0 : (x : M) → TangentSpace I x) σ
  simpa using this

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
@[simp]
lemma zeroσ (cov : CovariantDerivative I F V) (X : Π x : M, TangentSpace I x) : cov X 0 = 0 := by
  ext x
  have : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (0 : V x)) x := by
    exact (contMDiff_zeroSection 𝕜 V).mdifferentiableAt le_rfl
  have := cov.addσ X (0 : (x : M) → V x) (0 : (x : M) → V x) x this this
  simpa using this

lemma _root_.FiberBundle.trivializationAt.baseSet_mem_nhds {B : Type*} (F : Type*)
    [TopologicalSpace B] [TopologicalSpace F]
    (E : B → Type*) [TopologicalSpace (TotalSpace F E)] [(b : B) → TopologicalSpace (E b)]
    [FiberBundle F E] (b : B) : (trivializationAt F E b |>.baseSet) ∈ 𝓝 b :=
  (trivializationAt F E b).open_baseSet.eventually_mem (FiberBundle.mem_baseSet_trivializationAt' b)

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)]
  [∀ (x : M), ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V] in
variable {I F V} in
/-- If `σ` and `σ'` are equal sections of `E`, they have equal covariant derivatives. -/
lemma congr_σ (cov : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x} (hσ : ∀ x, σ x = σ' x) :
    cov X σ x = cov X σ' x := by
  simp [funext hσ]

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [(x : M) → Module 𝕜 (V x)]
     [(x : M) → AddCommGroup (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V] in
variable {I F V x} in
/-- If two sections `σ` and `σ'` are equal on a neighbourhood `s` of `x`,
if one is differentiable at `x` then so is the other.
Issue: EventuallyEq does not work for dependent functions. -/
lemma _root_.mdifferentiableAt_dependent_congr {σ σ' : Π x : M, V x} {s : Set M} (hs : s ∈ nhds x)
    (hσ₁ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x)
    (hσ₂ : ∀ x ∈ s, σ x = σ' x) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x := by
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
lemma _root_.mfderiv_dependent_congr_iff {σ σ' : Π x : M, V x} {s : Set M} (hs : s ∈ nhds x)
    (hσ : ∀ x ∈ s, σ x = σ' x) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x  ↔
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x :=
  ⟨fun h ↦ _root_.mdifferentiableAt_dependent_congr hs h hσ,
   fun h ↦ _root_.mdifferentiableAt_dependent_congr hs h (fun x hx ↦ (hσ x hx).symm)⟩

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma sum_X (cov : CovariantDerivative I F V)
    {ι : Type*} {s : Finset ι} {X : ι → Π x : M, TangentSpace I x} {σ : Π x : M, V x} :
    cov (∑ i ∈ s, X i) σ = ∑ i ∈ s, cov (X i) σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, Finset.sum_insert ha, ← h, cov.addX]

/-- A convex combination of covariant derivatives is a covariant derivative. -/
@[simps]
def convexCombination (cov cov' : CovariantDerivative I F V) (t : 𝕜) :
    CovariantDerivative I F V where
  toFun X s := (t • (cov X s)) + (1 - t) • (cov' X s)
  addX X X' σ := by simp only [cov.addX, cov'.addX]; module
  smulX X σ f := by simp only [cov.smulX, cov'.smulX]; module
  addσ X σ σ' x hσ hσ' := by
    simp [cov.addσ X σ σ' x hσ hσ', cov'.addσ X σ σ' x hσ hσ']
    module
  smul_const_σ X {σ x} /-hσ-/ := by
    simp [cov.smul_const_σ, cov'.smul_const_σ]
    module
  leibniz X σ f x hσ hf := by
    simp [cov.leibniz X σ f x hσ hf, cov'.leibniz X σ f x hσ hf]
    module

section real

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  -- `V` vector bundle

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- If `X` and `X'` agree in a neighbourhood of `p`, then `∇_X σ` and `∇_X' σ` agree at `p`. -/
lemma congr_X_of_eventuallyEq (cov : CovariantDerivative I F V) [T2Space M]
    {X X' : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M} {s : Set M} (hs : s ∈ nhds x)
    (hσσ' : ∀ x ∈ s, X x = X' x) :
    cov X σ x = cov X' σ x := by
  -- Choose a smooth bump function ψ with support around `x` contained in `s`
  obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.1 hs
  -- Observe that `ψ • X = ψ • X'` as dependent functions.
  have (x : M) : ((ψ : M → ℝ) • X) x = ((ψ : M → ℝ) • X') x := by
    by_cases h : x ∈ s
    · simp [hσσ' x h]
    · simp [notMem_support.mp fun a ↦ h (hψ a)]
  -- Then, it's a chain of (dependent) equalities.
  calc cov X σ x
    _ = cov ((ψ : M → ℝ) • X) σ x := by simp [cov.smulX]
    _ = cov ((ψ : M → ℝ) • X') σ x := by rw [funext this]
    _ = cov X' σ x := by simp [cov.smulX]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_X_at_aux (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M}
    (hX : X x = 0) : cov X σ x = 0 := by
  -- Consider the local frame {Xⁱ} on TangentSpace I x induced by chartAt H x.
  -- To do so, choose a basis of TangentSpace I x = E.
  let n : ℕ := Module.finrank ℝ E
  let b : Basis (Fin n) ℝ E := Module.finBasis ℝ E
  let e := trivializationAt E (TangentSpace I) x
  let Xi (i : Fin n) := b.localFrame e i
  -- Write X in coordinates: X = ∑ i, a i • Xi i near `x`.
  let a := fun i ↦ b.localFrame_repr e i X
  have : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have aux : ∀ᶠ (x' : M) in 𝓝 x, X x' = ∑ i, a i x' • Xi i x' := b.localFrame_repr_spec this X
  have (i : Fin n) : a i x = 0 := b.localFrame_repr_apply_zero_at hX i
  calc cov X σ x
    _ = cov (∑ i, a i • Xi i) σ x := cov.congr_X_of_eventuallyEq aux (by simp)
    _ = ∑ i, cov (a i • Xi i) σ x := by rw [cov.sum_X]; simp
    _ = ∑ i, a i x • cov (Xi i) σ x := by
      congr; ext i; simp [cov.smulX (Xi i) σ (a i)]
    _ = 0 := by simp [this]

-- XXX: better name?
-- golfing welcome!
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- `cov X σ x` only depends on `X` via `X x` -/
lemma congr_X_at (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X X' : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M} (hXX' : X x = X' x) :
    cov X σ x = cov X' σ x := by
  have : cov X' σ x = cov X σ x + cov (X' - X) σ x := by
    have : X' = X + (X' - X) := by simp
    nth_rw 1 [this]
    rw [cov.addX X (X' - X) σ]
    simp
  have h : (X' - X) x = 0 := by simp [hXX']
  simp [this, cov.congr_X_at_aux (X' - X) h]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_σ_smoothBumpFunction (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x)
    (f : SmoothBumpFunction I x) :
    cov X ((f : M → ℝ) • σ) x = cov X σ x := by
  rw [cov.leibniz _ _ _ _ hσ]
  swap; · apply f.contMDiff.mdifferentiable (by norm_num)
  calc _
    _ = cov X σ x + 0 := ?_
    _ = cov X σ x := by rw [add_zero]
  simp [f.eq_one, f.eventuallyEq_one.mfderiv_eq]
  rw [show mfderiv I 𝓘(ℝ, ℝ) 1 x = 0 by apply mfderiv_const]
  left
  rfl

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_σ_of_eventuallyEq
    (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x} {x : M} {s : Set M} (hs : s ∈ nhds x)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x)
    (hσσ' : ∀ x ∈ s, σ x = σ' x) :
    cov X σ x = cov X σ' x := by
  -- Choose a smooth bump function ψ with support around `x` contained in `s`
  obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.1 hs
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have (x : M) : ((ψ : M → ℝ) • σ) x = ((ψ : M → ℝ) • σ') x := by
    by_cases h : x ∈ s
    · simp [hσσ' x h]
    · simp [notMem_support.mp fun a ↦ h (hψ a)]
  -- Then, it's a chain of (dependent) equalities.
  calc cov X σ x
    _ = cov X ((ψ : M → ℝ) • σ) x := by rw [cov.congr_σ_smoothBumpFunction _ hσ]
    _ = cov X ((ψ : M → ℝ) • σ') x := cov.congr_σ _ _ (by simp [this])
    _ = cov X σ' x := by
      simp [cov.congr_σ_smoothBumpFunction, _root_.mdifferentiableAt_dependent_congr hs hσ hσσ']

-- TODO: prove that `cov X σ x` depends on σ only via σ(X) and the 1-jet of σ at x

/-- The difference of two covariant derivatives, as a function `Γ(TM) × Γ(E) → Γ(E)`.
Future lemmas will upgrade this to a map `TM ⊕ E → E`. -/
def differenceAux (cov cov' : CovariantDerivative I F V) :
    (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  fun X σ ↦ cov X σ - cov' X σ

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] [FiniteDimensional ℝ E] in
lemma differenceAux_smul_eq (cov cov' : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → ℝ)
    (hσ : MDifferentiable I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)))
    (hf : MDifferentiable I 𝓘(ℝ) f) :
    differenceAux cov cov' X ((f : M → ℝ) • σ) = (f : M → ℝ) • (differenceAux cov cov' X σ) :=
  calc _
    _ = cov X ((f : M → ℝ) • σ) - cov' X ((f : M → ℝ) • σ) := rfl
    _ = (f • cov X σ +  (fun x ↦ bar _ <| mfderiv I 𝓘(ℝ) f x (X x)) • σ)
        - (f • cov' X σ +  (fun x ↦ bar _ <| mfderiv I 𝓘(ℝ) f x (X x)) • σ) := by
      ext x
      simp [cov.leibniz X _ _ _ (hσ x) (hf x), cov'.leibniz X _ _ _ (hσ x) (hf x)]
    _ = f • cov X σ - f • cov' X σ := by simp
    _ = f • (cov X σ - cov' X σ) := by simp [smul_sub]
    _ = _ := rfl

omit [FiniteDimensional ℝ E] [∀ (x : M), IsTopologicalAddGroup (V x)]
    [∀ (x : M), ContinuousSMul ℝ (V x)] [VectorBundle ℝ F V] in
lemma differenceAux_smul_eq' (cov cov' : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → ℝ) :
    differenceAux cov cov' (f • X) σ = (f : M → ℝ) • differenceAux cov cov' X σ := by
  simp [differenceAux, cov.smulX, cov'.smulX, smul_sub]

/-- The value of `differenceAux cov cov' X σ` at `x₀` depends only on `X x₀` and `σ x₀`. -/
lemma foo (cov cov' : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X X' : Π x : M, TangentSpace I x) (σ σ' : Π x : M, V x) (x₀ : M)
    (hσ : MDifferentiable I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)))
    (hσ' : MDifferentiable I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ' x))) :
    differenceAux cov cov' X σ x₀ = differenceAux cov cov' X' σ' x₀ := by
  -- use the previous two lemmas: they prove that differenceAux is tensorial
  sorry

-- TODO: either change `localFrame` to make sure it is everywhere smooth
-- or introduce a cut-off here. First option is probaly better.
variable (F) in
noncomputable def extend [FiniteDimensional ℝ F] {x : M} (v : V x) : (x' : M) → V x' :=
  letI b := Basis.ofVectorSpace ℝ F
  letI t := trivializationAt F V x
  letI bV := b.localFrame_toBasis_at t (FiberBundle.mem_baseSet_trivializationAt F V x)
  fun x' ↦ ∑ i, bV.repr v i • b.localFrame t i x'

-- FIXME: these two lemmas only hold for *very particular* choices of extensions of v
-- (but there exist such choices, and our definition makes these ?! TODO check!!)
-- so, one may argue this is mathematically wrong, but it encodes the "choice some extension
-- with this and that property" nicely
-- a different proof would be to argue only the value at a point matters for cov
@[simp]
lemma extend_add_apply [FiniteDimensional ℝ F] {x : M} (v v' : V x) :
  extend F (v + v') = extend F v + extend F v' := sorry

@[simp]
lemma extend_smul_apply [FiniteDimensional ℝ F] {a : ℝ} (v  : V x) :
  extend F (a • v) = a • extend F v := sorry

-- TODO: cleanup this proof by adding simp lemmas to the localFrame stuff
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
@[simp] lemma extend_apply_self [FiniteDimensional ℝ F] {x : M} (v : V x) :
    extend F v x = v := by
  letI b := Basis.ofVectorSpace ℝ F
  letI t := trivializationAt F V x
  have x_mem : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  letI bV := b.localFrame_toBasis_at t x_mem
  change ∑ i, bV.repr v i • b.localFrame t i x = v
  conv_rhs => rw [←bV.sum_repr v]
  simp [bV, Basis.localFrame_toBasis_at, Basis.localFrame, x_mem]

lemma contMDiff_extend [FiniteDimensional ℝ F] {x : M} (σ₀ : V x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) 1 (fun x ↦ TotalSpace.mk' F x (extend F σ₀ x)) := by
  sorry

/-- The difference of two covariant derivatives, as a tensorial map -/
noncomputable def difference [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (cov cov' : CovariantDerivative I F V) :
    Π x : M, TangentSpace I x → V x → V x :=
  fun x X₀ σ₀ ↦ differenceAux cov cov' (extend E X₀) (extend F σ₀) x

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
@[simp]
lemma difference_apply [FiniteDimensional ℝ F] [IsManifold I 1 M]
    (cov cov' : CovariantDerivative I F V) (x : M) (X₀ : TangentSpace I x) (σ₀ : V x) :
    difference cov cov' x X₀ σ₀ =
      cov (extend E X₀) (extend F σ₀) x - cov' (extend E X₀) (extend F σ₀) x := rfl

end real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable (E E') in
@[simps]
noncomputable def trivial : CovariantDerivative 𝓘(𝕜, E) E'
  (Bundle.Trivial E E') where
  toFun X s := fun x ↦ fderiv 𝕜 s x (X x)
  addX X X' σ := by ext; simp
  smulX X σ c' := by ext; simp
  addσ X σ σ' e hσ hσ' := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
    rw [fderiv_add hσ hσ']
    rfl
  smul_const_σ X σ a := by ext; simp [fderiv_section_smul σ a]
  leibniz X σ f x hσ hf := by
    have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
      fderiv_smul (by simp_all) (by simp_all)
    simp [this, bar]
    rfl

open scoped Classical in
@[simps]
noncomputable def of_endomorphism (A : E → E →L[𝕜] E' →L[𝕜] E') :
    CovariantDerivative 𝓘(𝕜, E) E' (Bundle.Trivial E E') where
  toFun X σ := fun x ↦ fderiv 𝕜 σ x (X x) + A x (X x) (σ x)
  addX X X' σ := by
    ext x
    by_cases h : DifferentiableAt 𝕜 σ x
    · simp [h, map_add]; abel
    · simp [fderiv_zero_of_not_differentiableAt h]
  smulX X σ c' := by ext; simp
  addσ X σ σ' e hσ hσ' := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
    rw [fderiv_add hσ hσ']
    simp [hσ, hσ']
    abel
  smul_const_σ X σ a := by ext; simp [fderiv_section_smul σ a]
  leibniz X σ f x hσ hf := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ
    rw [mdifferentiableAt_iff_differentiableAt] at hf
    have h : DifferentiableAt 𝕜 (f • σ) x := hf.smul hσ
    have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
      fderiv_smul (by simp_all) (by simp_all)
    simp [this, bar, hσ, h]
    module

section real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

@[simps]
noncomputable def endomorph_of_trivial_aux [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (cov : CovariantDerivative 𝓘(ℝ, E) E' (Bundle.Trivial E E')) (x X : E) : E' →ₗ[ℝ] E' where
  toFun := difference cov (CovariantDerivative.trivial E E') x X
  map_add' y y' := by
    -- follows from the (not yet proven) smoothness
    have A : fderiv ℝ ((extend E' y  (x := x)) + extend E' y' (x := x)) x =
      fderiv ℝ (extend E' y (x := x)) x + fderiv ℝ (extend E' y' (x := x)) x := sorry
    have B : cov (extend E X (x := x)) (extend E' y  (x := x) + extend E' y' (x := x)) x =
      cov (extend E X (x := x)) (extend E' y (x := x)) x +
        cov (extend E X (x := x)) (extend E' y' (x := x)) x := sorry
    simp [A, B]
    module
  map_smul' a v := by
    simp [fderiv_section_smul, cov.smul_const_σ]
    module

@[simps!]
noncomputable def endomorph_of_trivial_aux' [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (cov : CovariantDerivative 𝓘(ℝ, E) E' (Bundle.Trivial E E')) (x X : E) : E' →L[ℝ] E' where
  toLinearMap := cov.endomorph_of_trivial_aux x X
  cont := LinearMap.continuous_of_finiteDimensional _

@[simps]
noncomputable def endomorph_of_trivial_aux'' [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (cov : CovariantDerivative 𝓘(ℝ, E) E' (Bundle.Trivial E E')) (x : E) : E →ₗ[ℝ] E' →L[ℝ] E' where
  toFun X := cov.endomorph_of_trivial_aux' x X
  map_add' X Y := by
    ext Z
    simp [cov.addX (extend E X (x := x)) (extend E Y (x := x)) (extend E' Z (x := x))]
    module
  map_smul' t X := by
    ext Z
    simp
    --expose_names
    --have A : cov (t • extend E X (x := x)) (extend E' Z) x = t • cov (extend E X (x := x)) (extend E' Z) x := sorry
    --simp [A]
    --have aux := cov.smulX (extend E X (x := x)) (extend E' Z (x := x)) (f := fun _ ↦ t) --t
    --simp [aux]
    --module
    sorry

@[simps!]
noncomputable def endomorph_of_trivial_aux''' [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (cov : CovariantDerivative 𝓘(ℝ, E) E' (Bundle.Trivial E E')) (x : E) : E →L[ℝ] E' →L[ℝ] E' where
  toLinearMap := cov.endomorph_of_trivial_aux'' x
  cont := LinearMap.continuous_of_finiteDimensional _

/-- Classification of covariant derivatives over a trivial vector bundle: every connection
is of the form `D + A`, where `D` is the trivial covariant derivative, and `A` a zeroth-order term
-/
lemma exists_endomorph [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (cov : CovariantDerivative 𝓘(ℝ, E) E' (Bundle.Trivial E E')) :
    ∃ (A : E → E →L[ℝ] E' →L[ℝ] E'), cov = .of_endomorphism A := by
  use cov.endomorph_of_trivial_aux'''
  apply CovariantDerivative.myext
  intro X σ x
  -- These two statements are unfolding a bit too far: the first sorry holds,
  -- but the second one does not.
  -- However, the difference of these is true again.
  have A : cov (extend E (X x)) (extend E' (σ x)) x = cov X σ x := sorry
  have B : fderiv ℝ (extend E' (σ x) (x := x)) x (X x) = fderiv ℝ σ x (X x) := sorry
  simp [A, B]

end real

end CovariantDerivative

end
