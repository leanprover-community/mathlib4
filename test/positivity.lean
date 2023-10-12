import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Tests for the `positivity` tactic

This tactic proves goals of the form `0 ≤ a` and `0 < a`.
-/
set_option autoImplicit true

open Function Nat NNReal ENNReal

variable {ι α β : Type _}

/- ## Numeric goals -/

example : 0 ≤ 0 := by positivity

example : 0 ≤ 3 := by positivity

example : 0 < 3 := by positivity

/- ## Goals working directly from a hypothesis -/
-- set_option trace.Meta.debug true
-- sudo set_option trace.Tactic.positivity true
example {a : ℤ} (ha : 0 < a) : 0 < a := by positivity
example {a : ℤ} (ha : 0 < a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 0 < a) : a ≠ 0 := by positivity
example {a : ℤ} (ha : 0 ≤ a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : a ≠ 0) : a ≠ 0 := by positivity
example {a : ℤ} (ha : a = 0) : 0 ≤ a := by positivity

/- ### Reversing hypotheses -/

example {a : ℤ} (ha : a > 0) : 0 < a := by positivity
example {a : ℤ} (ha : a > 0) : 0 ≤ a := by positivity
example {a : ℤ} (ha : a > 0) : a ≠ 0 := by positivity
example {a : ℤ} (ha : a ≥ 0) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 0 ≠ a) : a ≠ 0 := by positivity
example {a : ℤ} (ha : 0 < a) : a > 0 := by positivity
example {a : ℤ} (ha : 0 < a) : a ≥ 0 := by positivity
example {a : ℤ} (ha : 0 < a) : 0 ≠ a := by positivity
example {a : ℤ} (ha : 0 ≤ a) : a ≥ 0 := by positivity
example {a : ℤ} (ha : a ≠ 0) : 0 ≠ a := by positivity
example {a : ℤ} (ha : a = 0) : a ≥ 0 := by positivity
example {a : ℤ} (ha : 0 = a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 0 = a) : a ≥ 0 := by positivity

/- ### Calling `norm_num` -/

example {a : ℤ} (ha : 3 = a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 3 = a) : a ≠ 0 := by positivity
example {a : ℤ} (ha : 3 = a) : 0 < a := by positivity
example {a : ℤ} (ha : a = -1) : a ≠ 0 := by positivity

example {a : ℤ} (ha : 3 ≤ a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 3 ≤ a) : a ≠ 0 := by positivity
example {a : ℤ} (ha : 3 ≤ a) : 0 < a := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 3 < a) : a ≠ 0 := by positivity
example {a : ℤ} (ha : 3 < a) : 0 < a := by positivity

example {a b : ℤ} (h : 0 ≤ a + b) : 0 ≤ a + b := by positivity

example {a : ℤ} (hlt : 0 ≤ a) (hne : a ≠ 0) : 0 < a := by positivity

section

variable [LinearOrderedField α]

example : (1/4 - 2/3 : ℚ) ≠ 0 := by positivity
example : (1/4 - 2/3 : α) ≠ 0 := by positivity

end

/- ## Tests of the @[positivity] plugin tactics (addition, multiplication, division) -/

-- example [Nonempty ι] [Zero α] {a : α} (ha : a ≠ 0) : const ι a ≠ 0 := by positivity
-- example [Zero α] [PartialOrder α] {a : α} (ha : 0 < a) : 0 ≤ const ι a := by positivity
-- example [Zero α] [PartialOrder α] {a : α} (ha : 0 ≤ a) : 0 ≤ const ι a := by positivity
-- example [Nonempty ι] [Zero α] [PartialOrder α] {a : α} (ha : 0 < a) : 0 < const ι a := by positivity

section ite
variable {p : Prop} [Decidable p] {a b : ℤ}

example (ha : 0 < a) (hb : 0 < b) : 0 < ite p a b := by positivity
example (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ ite p a b := by positivity
example (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ ite p a b := by positivity
example (ha : 0 < a) (hb : b ≠ 0) : ite p a b ≠ 0 := by positivity
example (ha : a ≠ 0) (hb : 0 < b) : ite p a b ≠ 0 := by positivity
example (ha : a ≠ 0) (hb : b ≠ 0) : ite p a b ≠ 0 := by positivity

end ite

example {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < min a b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ min a b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ min a b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ min a b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : min a b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : min a b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : min a b ≠ 0 := by positivity

example {a b : ℚ} (ha : 0 < a) : 0 < max a b := by positivity
example {a b : ℚ} (hb : 0 < b) : 0 < max a b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) : 0 ≤ max a b := by positivity
example {a b : ℚ} (hb : 0 ≤ b) : 0 ≤ max a b := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : max a b ≠ 0 := by positivity

example {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a * b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a * b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : a * b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : a * b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by positivity

example {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : a / b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : a / b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by positivity

example {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ a / b := by positivity
example {a : ℤ} (ha : 0 < a) : 0 < a / a := by positivity
example {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b := by positivity
example {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by positivity
example {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by positivity

example {a : ℚ} (ha : 0 < a) : 0 < a⁻¹ := by positivity
example {a : ℚ} (ha : 0 ≤ a) : 0 ≤ a⁻¹ := by positivity
example {a : ℚ} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by positivity

example {a : ℚ} (n : ℕ) (ha : 0 < a) : 0 < a ^ n := by positivity
example {a : ℚ} (n : ℕ) (ha : 0 ≤ a) : 0 ≤ a ^ n := by positivity
example {a : ℚ} (n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0 := by positivity
example {a : ℚ} : 0 ≤ a ^ 18 := by positivity
example {a : ℚ} (ha : a ≠ 0) : 0 < a ^ 18 := by positivity

example {a : ℚ} (ha : 0 < a) : 0 < |a| := by positivity
example {a : ℚ} (ha : a ≠ 0) : 0 < |a| := by positivity
example (a : ℚ) : 0 ≤ |a| := by positivity

-- example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by positivity
-- example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a • b := by positivity
-- example {a : ℤ} {b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a • b := by positivity
-- example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : a • b ≠ 0 := by positivity
-- example {a : ℤ} {b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : a • b ≠ 0 := by positivity
-- example {a : ℤ} {b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a • b ≠ 0 := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a + a := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 ≤ 3 + a + b + b + 14 := by positivity

-- example {H : Type _} [LinearOrderedAddCommGroup H] {a b : H} (ha : 0 < a) (hb : 0 ≤ b) :
--   0 ≤ a + a + b :=
-- by positivity

example {a : ℤ} (ha : 3 < a) : 0 < a + a := by positivity

example {a b : ℚ} (ha : 3 < a) (hb : 4 ≤ b) : 0 < 3 + a * b / 7 + b + 7 + 14 := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 < 3 + a * b / 7 + b + 7 + 14 := by positivity

/-! ### Exponentiation -/

example [OrderedSemiring α] [Nontrivial α] (a : α) : 0 < a ^ 0 := by positivity
example [LinearOrderedRing α] (a : α) : 0 ≤ a ^ 18 := by positivity
example [OrderedSemiring α] {a : α} {n : ℕ} (ha : 0 ≤ a) : 0 ≤ a ^ n := by positivity
example [StrictOrderedSemiring α] {a : α} {n : ℕ} (ha : 0 < a) : 0 < a ^ n := by positivity

example [LinearOrderedSemifield α] (a : α) : 0 < a ^ (0 : ℤ) := by positivity
-- example [LinearOrderedField α] (a : α) (n : ℤ) : 0 ≤ a ^ bit0 n := by positivity
-- example [LinearOrderedSemifield α] {a : α} {n : ℤ} (ha : 0 ≤ a) : 0 ≤ a ^ n := by positivity
-- example [LinearOrderedSemifield α] {a : α} {n : ℤ} (ha : 0 < a) : 0 < a ^ n := by positivity

-- example {a b : Cardinal.{u}} (ha : 0 < a) : 0 < a ^ b := by positivity
-- example {a b : Ordinal.{u}} (ha : 0 < a) : 0 < a ^ b := by positivity

example {a b : ℝ} (ha : 0 ≤ a) : 0 ≤ a ^ b := by positivity
example {a b : ℝ} (ha : 0 < a) : 0 < a ^ b := by positivity
example {a : ℝ≥0} {b : ℝ} (ha : 0 < a) : 0 < a ^ b := by positivity
-- example {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a ^ b := by positivity
-- example {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b := by positivity
example {a : ℝ} : 0 < a ^ 0 := by positivity

example {a : ℝ} (ha : 0 < a) : 0 ≤ ⌊a⌋ := by positivity
example {a : ℝ} (ha : 0 ≤ a) : 0 ≤ ⌊a⌋ := by positivity

example {a : ℝ} (ha : 0 < a) : 0 < ⌈a⌉₊ := by positivity
example {a : ℝ} (ha : 0 < a) : 0 < ⌈a⌉ := by positivity
example {a : ℝ} (ha : 0 ≤ a) : 0 ≤ ⌈a⌉ := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 2 + a := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity

example {a : ℤ} (ha : 3 < a) : 0 < a ^ 2 + a := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : b ≥ 4) : 0 ≤ 3 * a ^ 2 * b + b * 7 + 14 := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : b ≥ 4) : 0 < 3 * a ^ 2 * b + b * 7 + 14 := by positivity

example {a : ℤ} : 0 ≤ |a| := by positivity

example {a : ℤ} : 0 < |a| + 3 := by positivity

example {n : ℤ} (hn : 0 < n) : 0 < n.natAbs := by positivity
example {n : ℤ} (hn : n ≠ 0) : 0 < n.natAbs := by positivity
example {n : ℤ} : 0 ≤ n.natAbs := by positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity

example : 0 < NNReal.sqrt 5 := by positivity
example : 0 ≤ Real.sqrt (-5) := by positivity
example : 0 < Real.sqrt 5 := by positivity

example {a : ℝ} (_ha : 0 ≤ a) : 0 ≤ Real.sqrt a := by positivity

example {a : ℝ} (ha : 0 ≤ a) : 0 < Real.sqrt (a + 3) := by positivity

example {a b : ℤ} (ha : 3 < a) : 0 ≤ min a (b ^ 2) := by positivity

-- -- test that the tactic can ignore arithmetic operations whose associated extension tactic requires
-- -- more typeclass assumptions than are available
-- example {R : Type _} [Zero R] [Div R] [LinearOrder R] {a b c : R} (h1 : 0 < a) (h2 : 0 < b)
--   (h3 : 0 < c) :
--   0 < max (a / b) c :=
-- by positivity

example : 0 ≤ max 3 4 := by positivity

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity

example {b : ℤ} : 0 ≤ max (b ^ 2) 0 := by positivity

example : 0 ≤ max (0:ℤ) (-3) := by positivity

example : 0 ≤ max (-3 : ℤ) 5 := by positivity

-- example [OrderedSemiring α] [OrderedAddCommMonoid β] [SMulWithZero α β]
--   [OrderedSMul α β] {a : α} (ha : 0 < a) {b : β} (hb : 0 < b) : 0 ≤ a • b := by positivity

example (n : ℕ) : 0 < n.succ := by positivity
example (n : ℕ) : 0 < n ! := by positivity
-- example (n k : ℕ) : 0 < n.asc_factorial k := by positivity

-- example {α : Type _} (s : Finset α) (hs : s.Nonempty) : 0 < s.card := by positivity
-- example {α : Type _} [Fintype α] [Nonempty α] : 0 < Fintype.card α := by positivity

example {r : ℝ} : 0 < Real.exp r := by positivity

example {n : ℕ} : 0 ≤ Real.log n := by positivity
example {n : ℤ} : 0 ≤ Real.log n := by positivity
example : 0 < Real.log 2 := by positivity
example : 0 < Real.log 1.01 := by positivity
example : 0 ≠ Real.log 0.99 := by positivity
example : 0 < Real.log (-2) := by positivity
example : 0 < Real.log (-1.01) := by positivity
example : 0 ≠ Real.log (-0.99) := by positivity
example : 0 ≤ Real.log 1 := by positivity
example : 0 ≤ Real.log 0 := by positivity
example : 0 ≤ Real.log (-1) := by positivity

example {V : Type _} [NormedCommGroup V] (x : V) : 0 ≤ ‖x‖ := by positivity
example {V : Type _} [NormedAddCommGroup V] (x : V) : 0 ≤ ‖x‖ := by positivity

example [MetricSpace α] (x y : α) : 0 ≤ dist x y := by positivity
example [MetricSpace α] {s : Set α} : 0 ≤ Metric.diam s := by positivity

-- example {E : Type _} [AddGroup E] {p : AddGroupSeminorm E} {x : E} : 0 ≤ p x := by positivity
-- example {E : Type _} [Group E] {p : GroupSeminorm E} {x : E} : 0 ≤ p x := by positivity

-- example {r : α → β → Prop} [∀ a, DecidablePred (r a)] {s : Finset α} {t : Finset β} :
--   0 ≤ Rel.edgeDensity r s t := by positivity
-- example {G : SimpleGraph α} [DecidableRel G.adj] {s t : finset α} :
--   0 ≤ G.edgeDensity s t := by positivity

/- ### Canonical orders -/

example {a : ℕ} : 0 ≤ a := by positivity
-- example {a : ℚ≥0} : 0 ≤ a := by positivity
example {a : ℝ≥0} : 0 ≤ a := by positivity
example {a : ℝ≥0∞} : 0 ≤ a := by positivity

/- ### Coercions -/

example {a : ℕ} : (0 : ℤ) ≤ a := by positivity
example {a : ℕ} : (0 : ℚ) ≤ a := by positivity
example {a : ℕ} (ha : 0 < a) : (0 : ℤ) < a := by positivity
example {a : ℕ} (ha : 0 < a) : (0 : ℚ) < a := by positivity
example {a : ℤ} (ha : a ≠ 0) : (a : ℚ) ≠ 0 := by positivity
example {a : ℤ} (ha : 0 ≤ a) : (0 : ℚ) ≤ a := by positivity
example {a : ℤ} (ha : 0 < a) : (0 : ℚ) < a := by positivity
-- example {a : ℚ} (ha : a ≠ 0) : (a : ℝ) ≠ 0 := by positivity
-- example {a : ℚ} (ha : 0 ≤ a) : (0 : ℝ) ≤ a := by positivity
-- example {a : ℚ} (ha : 0 < a) : (0 : ℝ) < a := by positivity
example {r : ℝ≥0} : (0 : ℝ) ≤ r := by positivity
example {r : ℝ≥0} (hr : 0 < r) : (0 : ℝ) < r := by positivity
-- example {r : ℝ≥0} (hr : 0 < r) : (0 : ℝ≥0∞) < r := by positivity
-- -- example {r : ℝ≥0} : (0 : ereal) ≤ r := by positivity -- TODO: Handle `coe_trans`
-- -- example {r : ℝ≥0} (hr : 0 < r) : (0 : ereal) < r := by positivity
-- example {r : ℝ} (hr : 0 ≤ r) : (0 : ereal) ≤ r := by positivity
-- example {r : ℝ} (hr : 0 < r) : (0 : ereal) < r := by positivity
-- example {r : ℝ} (hr : 0 ≤ r) : (0 : hyperreal) ≤ r := by positivity
-- example {r : ℝ} (hr : 0 < r) : (0 : hyperreal) < r := by positivity
-- example {r : ℝ≥0∞} : (0 : ereal) ≤ r := by positivity
-- example {r : ℝ≥0∞} (hr : 0 < r) : (0 : ereal) < r := by positivity

-- example {α : Type _} [OrderedRing α] {n : ℤ} : 0 ≤ ((n ^ 2 : ℤ) : α) := by positivity
-- example {r : ℝ≥0} : 0 ≤ ((r : ℝ) : ereal) := by positivity
-- example {r : ℝ≥0} : 0 < ((r + 1 : ℝ) : ereal) := by positivity

/- ## Other extensions -/

example [Zero β] [PartialOrder β] [NonnegHomClass F α β] (f : F) (x : α) : 0 ≤ f x := by positivity

example [OrderedSemiring S] [Semiring R] (abv : R → S) [IsAbsoluteValue abv] (x : R) :
    0 ≤ abv x := by
  positivity

example : (0 : ℝ) < ↑(3 : ℝ≥0) := by positivity
example (x : ℝ≥0) : (0:ℝ) ≤ ↑x := by positivity

/- ## Tests that the tactic is agnostic on reversed inequalities -/

example {a : ℤ} (ha : a > 0) : 0 ≤ a := by positivity

example {a : ℤ} (ha : 0 < a) : a ≥ 0 := by positivity

example {a : ℤ} (ha : a > 0) : a ≥ 0 := by positivity

/-
## Test for meta-variable instantiation

Reported on
https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/New.20tactic.3A.20.60positivity.60/near/300639970
-/

example : 0 ≤ 0 := by apply le_trans _ (le_refl _); positivity
