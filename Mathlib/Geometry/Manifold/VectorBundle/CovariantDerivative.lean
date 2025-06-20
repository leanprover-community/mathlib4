import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

open Bundle Filter Function

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]


section

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

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

lemma missing {f : E → 𝕜} {x : E} (Y : TangentSpace 𝓘(𝕜, E) x) :
  bar (f x) ((fderiv 𝕜 f x) Y) = (fderiv 𝕜 f x) Y := sorry

variable (x : M)
-- set_option diagnostics true
-- set_option trace.Meta.synthInstance.instances true in
-- #synth AddCommMonoid (V x  →L[𝕜] V x)

structure CovariantDerivative where
  toFun : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)
  addX : ∀ (X X' : Π x : M, TangentSpace I x) (σ : Π x : M, V x),
    toFun (X + X') σ = toFun X σ + toFun X' σ
  smulX : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → 𝕜),
    toFun (f • X) σ = f • toFun X σ
  addσ : ∀ (X : Π x : M, TangentSpace I x) (σ σ' : Π x : M, V x)(x : M),
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x
    → MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x
    → toFun X (σ + σ') x = toFun X σ x + toFun X σ' x
  -- smul_const_σ : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (a : 𝕜),
  --   toFun X (a • σ) = a • toFun X σ
  leibniz : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → 𝕜) (x : M),
    MDifferentiableAt I I.tangent (fun x ↦ (X x : TangentBundle I M)) x
    → MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x
    → MDifferentiableAt I 𝓘(𝕜, 𝕜) f x
    → toFun X (f • σ) x = (f • toFun X σ) x + (bar _ <| mfderiv I 𝓘(𝕜, 𝕜) f x (X x)) • σ x



lemma CovariantDerivative.smul_const_σ (cov : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (a : 𝕜) :
    cov.toFun X (a • σ) = a • cov.toFun X σ := by
  ext x
  by_cases hX : MDifferentiableAt I I.tangent (fun x ↦ (X x : TangentBundle I M)) x; swap
  · -- missing axiom: if X is not differentiable, the covariant derivative is zero
    have hσ₁ : cov.toFun X σ = 0 := sorry
    have hσ₂ : cov.toFun X (a • σ) = 0 := sorry
    simp [hσ₁, hσ₂]
  -- Thus, we know `X` is differentiable.
  by_cases hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x
  · have hσ' : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a • σ x)) x :=
      sorry
    have : MDifferentiableAt I 𝓘(𝕜, 𝕜) (fun x ↦ a) x :=
      (contMDiff_const.mdifferentiable (n := 1) (by norm_num)).mdifferentiableAt
    have aux := cov.leibniz X σ (fun _ ↦ a) x hX hσ this
    convert aux
    trans (a • cov.toFun X σ) x + 0
    · rw [add_zero]
    congr
    have : mfderiv I 𝓘(𝕜, 𝕜) (fun x ↦ a) x (X x) = 0 := sorry
    rw [this]
    simp
  -- missing axiom: "if σ is not differentiable, the covariant derivative is zero"
  have hσ₁ : cov.toFun X σ = 0 := sorry
  have hσ' : ¬ MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a • σ x)) x :=
    sorry
  have hσ₂ : cov.toFun X (a • σ) = 0 := sorry
  simp [hσ₁, hσ₂]

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

theorem Bundle.Trivial.mdifferentiableAt_iff (σ : (x : E) → Trivial E E' x) (e : E) :
    MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (fun x ↦ TotalSpace.mk' E' x (σ x)) e ↔
    DifferentiableAt 𝕜 σ e := by
  sorry

noncomputable def trivial_covariant_derivative : CovariantDerivative 𝓘(𝕜, E) E'
  (Bundle.Trivial E E') where
  toFun X s := fun x ↦ fderiv 𝕜 s x (X x)
  addX X X' σ := by ext; simp
  smulX X σ c' := by ext; simp
  addσ X σ σ' e hσ hσ' := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
    rw [fderiv_add hσ hσ']
    rfl
  leibniz := sorry

end
