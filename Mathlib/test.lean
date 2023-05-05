import Mathlib.Algebra.Module.LinearMap

--set_option pp.all true
--set_option trace.Meta.synthInstance true

-- succeeds
example {R₁ R₂ M₁ M₂ : Type _} [Semiring R₁] [Semiring R₂] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R₁ M₁] [Module R₂ M₂] (σ : R₁ →+* R₂) :
  SemilinearMapClass (M₁ →ₛₗ[σ] M₂) σ M₁ M₂ :=
inferInstance

-- used to fail, now succeeds
example {R₁ R₂ M₁ M₂ : Type _} [Ring R₁] [Semiring R₂] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R₁ M₁] [Module R₂ M₂] (σ : R₁ →+* R₂) :
  SemilinearMapClass (M₁ →ₛₗ[σ] M₂) σ M₁ M₂ :=
inferInstance

-- succeeds
set_option synthInstance.etaExperiment true in
example {R₁ R₂ M₁ M₂ : Type _} [Ring R₁] [Semiring R₂] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R₁ M₁] [Module R₂ M₂] (σ : R₁ →+* R₂) :
  SemilinearMapClass (M₁ →ₛₗ[σ] M₂) σ M₁ M₂ :=
inferInstance
