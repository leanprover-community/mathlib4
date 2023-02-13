import Mathlib.Topology.Basic

variable [TopologicalSpace X] [TopologicalSpace Y]

example : Continuous (id : X → X) := by continuity

example {f : X → Y} {g : Y → X} (hf : Continuous f) (hg : Continuous g) :
  Continuous (fun x => f (g x)) := by continuity

example {f : X → Y} {g : Y → X} (hf : Continuous f) (hg : Continuous g) :
  Continuous (f ∘ g ∘ f) := by continuity

example {f : X → Y} {g : Y → X} (hf : Continuous f) (hg : Continuous g) :
  Continuous (f ∘ g) := by continuity

example (y : Y) : Continuous (fun (_ : X) ↦ y) := by continuity

example {f : Y → Y} (y : Y) : Continuous (f ∘ (fun (_ : X) => y)) := by continuity

example {g : X → X} (y : Y) : Continuous ((fun _ ↦ y) ∘ g) := by continuity

example {f : X → Y} (x : X) : Continuous (fun (_ : X) ↦ f x) := by continuity

-- Todo: more interesting examples when more algebra is ported

-- Porting note: port the tests from mathlib3 once we have the necessary theory files

/- Todo: restore this test
example [TopologicalSpace X] [TopologicalSpace Y]
  (f₁ f₂ : X → Y) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
  (g : Y → ℝ) (hg : Continuous g) : Continuous (fun x => (max (g (f₁ x)) (g (f₂ x))) + 1) :=
  by continuity -/
