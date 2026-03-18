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

example (f₁ f₂ : X → Y) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (g : Y → ℝ) (hg : Continuous g) : Continuous (fun x => (max (g (f₁ x)) (g (f₂ x))) + 1) := by
  continuity

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
Initial goal:
  W : Type ?u.507636
  X : Type ?u.507639
  Y : Type ?u.507642
  Z : Type ?u.507645
  inst✝⁴ : TopologicalSpace W
  inst✝³ : TopologicalSpace X
  inst✝² : TopologicalSpace Y
  inst✝¹ : TopologicalSpace Z
  I : Type ?u.507648
  X' : I → Type ?u.507653
  inst✝ : (i : I) → TopologicalSpace (X' i)
  ⊢ Continuous fun x => rexp (max x (-x) + sin x) ^ 2
Remaining goals after safe rules:
  case h.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf
  W : Type ?u.507636
  X : Type ?u.507639
  Y : Type ?u.507642
  Z : Type ?u.507645
  inst : TopologicalSpace W
  inst_1 : TopologicalSpace X
  inst_2 : TopologicalSpace Y
  inst_3 : TopologicalSpace Z
  I : Type ?u.507648
  X' : I → Type ?u.507653
  inst_4 : (i : I) → TopologicalSpace (X' i)
  ⊢ Continuous fun x => (Complex.exp (↑(max x (-x)) + Complex.sin ↑x)).1
The safe prefix was not fully expanded because the maximum number of rule applications (50) was reached.
-/
#guard_msgs in
example : Continuous (fun x : ℝ => exp ((max x (-x)) + sin x)^2) := by
  -- This invocation fails, with an error about maximal rule application depth being reached.
  -- continuity itself does not support passing further options.
  continuity
  sorry

/--
error: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : Continuous (fun x : ℝ => exp ((max x (-x)) + sin x)^2) := by
  -- Let's manually expand `continuity` to its aesop invocation, and pass that option.
  -- Now we get an error about simp's maximal recursion depth being reached.
  aesop (config := { terminal := true, maxRuleApplicationDepth := 200 }) (rule_sets := [Continuous])
  sorry

/--
error: tactic 'aesop' failed, maximum number of rule applications (200) reached. Set the 'maxRuleApplications' option to increase the limit.
Initial goal:
  W : Type ?u.1782759
  X : Type ?u.1782762
  Y : Type ?u.1782765
  Z : Type ?u.1782768
  inst✝⁴ : TopologicalSpace W
  inst✝³ : TopologicalSpace X
  inst✝² : TopologicalSpace Y
  inst✝¹ : TopologicalSpace Z
  I : Type ?u.1782771
  X' : I → Type ?u.1782776
  inst✝ : (i : I) → TopologicalSpace (X' i)
  ⊢ Continuous fun x => rexp (max x (-x) + sin x) ^ 2
Remaining goals after safe rules:
  case h.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf.hf
  W : Type ?u.1782759
  X : Type ?u.1782762
  Y : Type ?u.1782765
  Z : Type ?u.1782768
  inst : TopologicalSpace W
  inst_1 : TopologicalSpace X
  inst_2 : TopologicalSpace Y
  inst_3 : TopologicalSpace Z
  I : Type ?u.1782771
  X' : I → Type ?u.1782776
  inst_4 : (i : I) → TopologicalSpace (X' i)
  ⊢ Continuous fun x => (Complex.exp ↑(max x (-x) + sin x)).1
The safe prefix was not fully expanded because the maximum number of rule applications (50) was reached.
-/
#guard_msgs in
example : Continuous (fun x : ℝ => exp ((max x (-x)) + sin x)^2) := by
  -- If we disable simp, aesop fails to make meaningful progress.
  aesop (config := { terminal := true, maxRuleApplicationDepth := 200, enableSimp := false }) (rule_sets := [Continuous])
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
  continuous_const

example (b : Y) : Continuous (@Prod.mk Y X b) := by continuity

example (f : C(X × Y, Z)) (a : X) : Continuous (Function.curry f a) := --by continuity
  f.continuous.comp (continuous_const.prodMk continuous_id)

end basic

/-! Some tests of the `comp_of_eq` lemmas -/

example {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {x₀ : α} (f : α → α → β)
  (hf : ContinuousAt (Function.uncurry f) (x₀, x₀)) :
  ContinuousAt (fun x ↦ f x x) x₀ := by
  fail_if_success { exact hf.comp (continuousAt_id.prod continuousAt_id) }
  exact hf.comp_of_eq (continuousAt_id.prodMk continuousAt_id) rfl
