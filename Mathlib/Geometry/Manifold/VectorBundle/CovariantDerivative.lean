import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

open Bundle Filter Function

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

def bar (a : 𝕜) : TangentSpace 𝓘(𝕜, 𝕜) a ≃L[𝕜] 𝕜 where
  toFun v := v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp

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
    → MDifferentiableAt I 𝓘(𝕜, 𝕜) f x
    → toFun X (f • σ) x = (f • toFun X σ) x + (bar _ <| mfderiv I 𝓘(𝕜, 𝕜) f x (X x)) • σ x
  do_not_read : ∀ (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M},
    ¬ MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x → toFun X σ x = 0

namespace CovariantDerivative

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
@[simp]
lemma zeroX (cov : CovariantDerivative I F V) (σ : Π x : M, V x) : cov.toFun 0 σ = 0 := by
  have := cov.addX (0 : (x : M) → TangentSpace I x) (0 : (x : M) → TangentSpace I x) σ
  simpa using this

@[simp]
lemma zeroσ (cov : CovariantDerivative I F V) (X : Π x : M, TangentSpace I x) : cov.toFun X 0 = 0 := by
  ext x
  have : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (0 : V x)) x := by
    sorry
    -- apply mdifferentiableAt_const (I := I) (I' := I.prod 𝓘(𝕜, F)) (c := (0 : V x)) (x := x) fails
  have := cov.addσ X (0 : (x : M) → V x) (0 : (x : M) → V x) x this this
  simpa using this

lemma smul_const_σ (cov : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (a : 𝕜) :
    cov.toFun X (a • σ) = a • cov.toFun X σ := by
  ext x
  by_cases hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x
  · simpa using cov.leibniz X σ (fun _ ↦ a) x hσ mdifferentiable_const.mdifferentiableAt
  have hσ₂ : cov.toFun X (a • σ) x = 0 := by
    by_cases ha: a = 0
    · simp [ha]
    refine cov.do_not_read X ?_
    contrapose! hσ
    simp at hσ
    have : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a⁻¹ • a • σ x)) x := by
      sorry -- have := hσ.const_smul a⁻¹ --(E' := H × F) fails to unify
    apply this.congr_of_eventuallyEq
    filter_upwards with x
    congr
    exact (eq_inv_smul_iff₀ ha).mpr rfl
  simp [cov.do_not_read X hσ, hσ₂]

/-- A convex combination of covariant derivatives is a covariant derivative. -/
@[simps]
def convexCombination (cov cov' : CovariantDerivative I F V) (t : 𝕜) :
    CovariantDerivative I F V where
  toFun X s := (t • (cov.toFun X s)) + (1 - t) • (cov'.toFun X s)
  addX X X' σ := by simp only [cov.addX, cov'.addX]; module
  smulX X σ f := by simp only [cov.smulX, cov'.smulX]; module
  addσ X σ σ' x hσ hσ' := by
    simp [cov.addσ X σ σ' x hσ hσ', cov'.addσ X σ σ' x hσ hσ']
    module
  leibniz X σ f x hσ hf := by
    simp [cov.leibniz X σ f x hσ hf, cov'.leibniz X σ f x hσ hf]
    module
  do_not_read X {σ} {x} hσ := by simp [cov.do_not_read X hσ, cov'.do_not_read X hσ]

end CovariantDerivative

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

@[simp]
theorem Bundle.Trivial.mdifferentiableAt_iff (σ : (x : E) → Trivial E E' x) (e : E) :
    MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (fun x ↦ TotalSpace.mk' E' x (σ x)) e ↔
    DifferentiableAt 𝕜 σ e := by
  sorry

attribute [simp] mdifferentiableAt_iff_differentiableAt

@[simps]
noncomputable def CovariantDerivative.trivial : CovariantDerivative 𝓘(𝕜, E) E'
  (Bundle.Trivial E E') where
  toFun X s := fun x ↦ fderiv 𝕜 s x (X x)
  addX X X' σ := by ext; simp
  smulX X σ c' := by ext; simp
  addσ X σ σ' e hσ hσ' := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
    rw [fderiv_add hσ hσ']
    rfl
  leibniz X σ f x hσ hf := by
    have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
      fderiv_smul (by simp_all) (by simp_all)
    simp [this, bar]
    rfl
  do_not_read X σ x hσ := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ
    simp [fderiv_zero_of_not_differentiableAt hσ]

end
