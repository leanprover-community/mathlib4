import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousFunction.Basic

set_option autoImplicit true
section basic

variable [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {I : Type _} {X' : I → Type _} [∀ i, TopologicalSpace (X' i)]

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

example (f₁ f₂ : X → Y) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (g : Y → ℝ) (hg : Continuous g) : Continuous (fun x => (max (g (f₁ x)) (g (f₂ x))) + 1) := by
  continuity

example {κ ι : Type}
    (K : κ → Type) [∀ k, TopologicalSpace (K k)] (I : ι → Type) [∀ i, TopologicalSpace (I i)]
    (e : κ ≃ ι) (F : Π k, Homeomorph (K k) (I (e k))) :
    Continuous (fun (f : Π k, K k) (i : ι) => F (e.symm i) (f (e.symm i))) := by
  continuity

open Real

example : Continuous (fun x : ℝ => exp ((max x (-x)) + sin x)^2) := by
  continuity

example : Continuous (fun x : ℝ => exp ((max x (-x)) + sin (cos x))^2) := by
  continuity

-- Examples taken from `Topology.ContinuousFunction.Basic`:

example (b : Y) : Continuous (fun _ : X => b) := by continuity

example (f : C(X, Y)) (g : C(Y, Z)) : Continuous (g ∘ f) := by continuity

example (f : C(X, Y)) (g : C(X, Z)) : Continuous (fun x => (f x, g x)) := by continuity

example (f : C(X, Y)) (g : C(W, Z)) : Continuous (Prod.map f g) := --by continuity
  f.continuous.prod_map g.continuous

example (f : ∀ i, C(X, X' i)) : Continuous (fun a i => f i a) := by continuity

example (s : Set X) (f : C(X, Y)) : Continuous (f ∘ ((↑) : s → X)) := by continuity

-- Examples taken from `Topology.CompactOpen`:

example (b : Y) : Continuous (Function.const X b) := --by continuity
  continuous_const

example (b : Y) : Continuous (@Prod.mk Y X b) := by continuity

example (f : C(X × Y, Z)) (a : X) : Continuous (Function.curry f a) := --by continuity
  f.continuous.comp (continuous_const.prod_mk continuous_id)

end basic

/-! Some tests of the `comp_of_eq` lemmas -/

example {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {x₀ : α} (f : α → α → β)
  (hf : ContinuousAt (Function.uncurry f) (x₀, x₀)) :
  ContinuousAt (fun x ↦ f x x) x₀ := by
  fail_if_success { exact hf.comp (continuousAt_id.prod continuousAt_id) }
  exact hf.comp_of_eq (continuousAt_id.prod continuousAt_id) rfl
