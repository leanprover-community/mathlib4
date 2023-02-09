import Mathlib.Topology.Basic

example [TopologicalSpace X] [TopologicalSpace Y]
  (f₁ f₂ : X → Y) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
  (g : Y → ℝ) (hg : Continuous g) : continuous (λ x, (max (g (f₁ x)) (g (f₂ x))) + 1) :=
  by continuity
--by guard_proof_term { continuity } ((hg.comp hf₁).max (hg.comp hf₂)).add continuous_const
