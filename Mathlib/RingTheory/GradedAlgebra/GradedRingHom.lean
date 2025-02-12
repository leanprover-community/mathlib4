import Mathlib.RingTheory.GradedAlgebra.Basic

variable {R : Type*} [CommSemiring R]
variable {A₁ ι₁ σ₁ : Type*} [DecidableEq ι₁] [AddMonoid ι₁] [Semiring A₁] [Algebra R A₁]
variable [SetLike σ₁ A₁] [AddSubmonoidClass σ₁ A₁] (𝒜 : ι₁ → σ₁) [GradedRing 𝒜]
variable {A₂ ι₂ σ₂ : Type*} [DecidableEq ι₂] [AddMonoid ι₂] [Semiring A₂] [Algebra R A₂]
variable [SetLike σ₂ A₂] [AddSubmonoidClass σ₂ A₂] (ℬ : ι₂ → σ₂) [GradedRing ℬ]

structure GradedRingHom extends RingHom A₁ A₂ where
  index_hom : ι₁ →+ ι₂
  grading_compat : ∀ (i : ι₁), AddSubmonoid.map toRingHom (𝒜 i) ≤ (ℬ (index_hom i))
