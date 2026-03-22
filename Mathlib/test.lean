import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

open Bundle

variable
  {M : Type*} {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [RiemannianBundle V]

variable {σ σ' : Π x : M, V x}

set_option trace.profiler true

#check fun x : M ↦ inner ℝ (σ x) (σ' x)
