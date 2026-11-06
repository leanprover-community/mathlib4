import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pull
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open Complex NNReal

private axiom test_sorry : ∀ {α}, α

variable {A : Type*} [CStarAlgebra A]

/-! ### The motivating example

The `cfcₙ` over `ℝ` is pulled over `ℝ` (including its argument `1 - a ^ 2`), composed, and only
then converted to `ℂ`. This gives the function `x ↦ x + I * √(1 - x.re ^ 2)`, and the only side
condition is `IsSelfAdjoint a`, which is a hypothesis. -/

example {a : A} (ha : IsSelfAdjoint a) :
    a + I • cfcₙ (√·) (1 - a ^ 2) = cfc (fun x : ℂ ↦ x + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull ℂ a

/-! ### Algebraic operations

On an equation, both sides are pulled. If the functions differ, the remaining goal compares them,
and `cfc_congr` reduces it to a statement about the spectrum. -/

example {a : A} (ha : IsSelfAdjoint a) : 2 * a ^ 3 - star a + 1 = algebraMap ℝ A 3 := by
  cfc_pull ℝ a
  guard_target = cfc (fun x : ℝ ↦ 2 * x ^ 3 - star x + 1) a = cfc (fun _ : ℝ ↦ 3) a
  exact test_sorry

example {a : A} [IsStarNormal a] : star a + I • a = cfc (fun x : ℂ ↦ star x + I * x) a := by
  cfc_pull ℂ a

example {a : A} (ha : IsSelfAdjoint a) (r : ℝ) :
    r • (a + 2) - algebraMap ℝ A r = cfc (fun x : ℝ ↦ r * (x + 2) - r) a := by
  cfc_pull ℝ a

example {a : A} (ha : IsSelfAdjoint a) : a + a = cfc (fun x : ℝ ↦ 2 * x) a := by
  cfc_pull ℝ a
  apply cfc_congr
  intro x _
  ring

/-! ### `conv` mode -/

example {a : A} (ha : IsSelfAdjoint a) : a + I • cfcₙ (√·) (1 - a ^ 2) = 0 := by
  conv_lhs => cfc_pull ℂ a
  guard_target = cfc (fun x : ℂ ↦ x + I * ↑√(1 - x.re ^ 2)) a = 0
  exact test_sorry

example {a b : A} (ha : IsSelfAdjoint a) (h : a * a + 1 = b) :
    cfc (fun x : ℝ ↦ x * x + 1) a = b := by
  conv at h => lhs; cfc_pull ℝ a
  exact h

/-! ### Composition

An inner `cfc g b` is handled by pulling `b` and composing. The element `a` itself can be any
expression. -/

example {a : A} (ha : IsSelfAdjoint a) :
    cfc (fun x : ℝ ↦ x ^ 2) (cfc (fun x : ℝ ↦ x + 1) (a ^ 3)) =
      cfc (fun x : ℝ ↦ (x ^ 3 + 1) ^ 2) a := by
  cfc_pull ℝ a

example {a : A} (ha : IsSelfAdjoint a) :
    (a + 1) ^ 2 = cfc (fun x : ℝ ↦ x ^ 2) (a + 1) := by
  cfc_pull ℝ (a + 1)

/-! ### Changing the scalar ring -/

example {a : A} (ha : IsSelfAdjoint a) :
    cfc (fun x : ℝ ↦ x ^ 2) (a + 1) = cfc (fun x : ℂ ↦ (((x.re + 1) ^ 2 : ℝ) : ℂ)) a := by
  cfc_pull ℂ a

example [PartialOrder A] [StarOrderedRing A] {a : A} (ha : 0 ≤ a) :
    cfc (fun x : ℝ≥0 ↦ x * 2) a + a = cfc (fun x : ℝ ↦ ↑(x.toNNReal * 2) + x) a := by
  cfc_pull ℝ a

/-! ### Side goals

Hypotheses which the lemmas' default tactics cannot discharge are returned as goals, once each. -/

example {a : A} : a + 1 = cfc (fun x : ℝ ↦ x + 1) a := by
  cfc_pull ℝ a
  guard_target = IsSelfAdjoint a
  exact test_sorry

example {a : A} (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a)) :
    cfc f a + a = cfc (fun x ↦ f x + x) a := by
  cfc_pull ℝ a

/-! ### Extending the tactic

New operations are supported by tagging a lemma `cfc F a = P[cfc f a]` with `@[cfc_pull]`. -/

def twice (x : A) := x + x

lemma cfc_twice (f : ℝ → ℝ) (a : A) (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac) :
    cfc (fun x ↦ f x + f x) a = twice (cfc f a) :=
  cfc_add a f f

example {a : A} (_ha : IsSelfAdjoint a) : twice (a + 2) = 0 := by
  fail_if_success conv_lhs => cfc_pull ℝ a
  exact test_sorry

attribute [local cfc_pull] cfc_twice in
example {a : A} (ha : IsSelfAdjoint a) : twice (a + 2) = 0 := by
  conv_lhs => cfc_pull ℝ a
  guard_target = cfc (fun x : ℝ ↦ x + 2 + (x + 2)) a = 0
  exact test_sorry

/-! ### Failure -/

/-- error: cfc_pull: could not write
  a + b
in the form `cfc _ a` over ℝ -/
#guard_msgs in
example {a b : A} : a + b = 0 := by
  cfc_pull ℝ a
