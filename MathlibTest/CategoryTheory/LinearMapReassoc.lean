module

public import Mathlib.Tactic.CategoryTheory.LinearMapReassoc

namespace Tests.LinearMapReassoc

universe u v

variable {R : Type u} [Semiring R]
  {M₀ M₁ M₂ M₃ : Type v}
  [AddCommMonoid M₀] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M₀] [Module R M₁] [Module R M₂] [Module R M₃]

@[reassoc]
lemma foo (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : M₁ →ₗ[R] M₃) (w : g ∘ₗ f = h) :
    g ∘ₗ f = h := w

/--
info: Tests.LinearMapReassoc.foo_assoc.{u, v} {R : Type u} [Semiring R] {M₁ M₂ M₃ : Type v} [AddCommMonoid M₁]
  [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
  (h : M₁ →ₗ[R] M₃) (w : g ∘ₗ f = h) {M₁✝ : Type v} [AddCommMonoid M₁✝] [Module R M₁✝] (h✝ : M₁✝ →ₗ[R] M₁) :
  g ∘ₗ f ∘ₗ h✝ = h ∘ₗ h✝
-/
#guard_msgs in
#check foo_assoc

example (e : M₀ →ₗ[R] M₁) (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (h : M₁ →ₗ[R] M₃) (w : g ∘ₗ f = h) :
    g ∘ₗ f ∘ₗ e = h ∘ₗ e := by
  rw [reassoc_of% foo]
  exact w

end Tests.LinearMapReassoc
