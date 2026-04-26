import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic

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

-- This test points at an internal error in aesop. With fewer imports, `continuity` succeeds.
-- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/aesop.20error.20during.20proof.20reconstruction.2C.20goal.20not.20normalised/with/580202602.
/-- error: aesop: internal error during proof reconstruction: goal 31 was not normalised. -/
#guard_msgs in
example (f₁ f₂ : X → Y) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (g : Y → ℝ) (hg : Continuous g) : Continuous (fun x => (max (g (f₁ x)) (g (f₂ x))) + 1) := by
  continuity

section

attribute [-aesop] Continuous.comp'
attribute [aesop (rule_sets := [Continuous]) safe apply] Continuous.comp'
example (f₁ f₂ : X → Y) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (g : Y → ℝ) (hg : Continuous g) : Continuous (fun x => (max (g (f₁ x)) (g (f₂ x))) + 1) := by
  continuity

end

example {κ ι : Type}
    (K : κ → Type) [∀ k, TopologicalSpace (K k)] (I : ι → Type) [∀ i, TopologicalSpace (I i)]
    (e : κ ≃ ι) (F : Π k, Homeomorph (K k) (I (e k))) :
    Continuous (fun (f : Π k, K k) (i : ι) => F (e.symm i) (f (e.symm i))) := by
  continuity

open Real

section

attribute [-aesop] Continuous.comp'
attribute [aesop (rule_sets := [Continuous]) unsafe 99% apply] Continuous.comp'

/--
error: tactic 'aesop' failed, failed to prove the goal. Some goals were not explored because the maximum rule application depth (30) was reached. Set option 'maxRuleApplicationDepth' to increase the limit.
-/
#guard_msgs (substring := true) in
example : Continuous (fun x : ℝ => exp ((max x (-x)) + sin x)^2) := by
  continuity
  sorry

-- If we make this a safe rule instead, the test succeeds quickly.
attribute [-aesop] Continuous.comp'
attribute [aesop (rule_sets := [Continuous]) safe apply] Continuous.comp'

example : Continuous (fun x : ℝ => exp ((max x (-x)) + sin x)^2) := by
  continuity

-- The story for this more complicated example is similar.

example : Continuous (fun x : ℝ => exp ((max x (-x)) + sin (cos x))^2) := by
  continuity

end

-- Examples taken from `Topology.ContinuousMap.Basic`:

example (b : Y) : Continuous (fun _ : X => b) := by continuity

example (f : C(X, Y)) (g : C(Y, Z)) : Continuous (g ∘ f) := by continuity

example (f : C(X, Y)) (g : C(X, Z)) : Continuous (fun x => (f x, g x)) := by continuity

example (f : C(X, Y)) (g : C(W, Z)) : Continuous (Prod.map f g) := by continuity

example (f : ∀ i, C(X, X' i)) : Continuous (fun a i => f i a) := by continuity

example (s : Set X) (f : C(X, Y)) : Continuous (f ∘ ((↑) : s → X)) := by continuity

-- Examples taken from `Topology.CompactOpen`:

example (b : Y) : Continuous (Function.const X b) := --by continuity
  Continuous.const

example (b : Y) : Continuous (@Prod.mk Y X b) := by continuity

example (f : C(X × Y, Z)) (a : X) : Continuous (Function.curry f a) := --by continuity
  f.continuous.comp (Continuous.const.prodMk continuous_id)

end basic

/-! Some tests of the `comp_of_eq` lemmas -/

example {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {x₀ : α} (f : α → α → β)
  (hf : ContinuousAt (Function.uncurry f) (x₀, x₀)) :
  ContinuousAt (fun x ↦ f x x) x₀ := by
  fail_if_success { exact hf.comp (continuousAt_id.prod continuousAt_id) }
  exact hf.comp_of_eq (continuousAt_id.prodMk continuousAt_id) rfl
