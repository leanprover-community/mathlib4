import Mathlib.Algebra.Group.Fin
import Mathlib.Tactic.SlimCheck
import Mathlib.Tactic.SuccessIfFailWithMsg
import Mathlib.Data.Finsupp.Notation
import Mathlib.Testing.SlimCheck.Functions
import Mathlib.Tactic.Have
import Mathlib.Data.Nat.Prime

private axiom test_sorry : ∀ {α}, α

/--
warning: Gave up 90 times
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (z : Nat) (h : z = 37) : z ≠ 0 := by
  slim_check (config := { randomSeed := some 257 })

/--
info: Success
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (z : Nat) (h : z ≤ 37) : z ≤ 37 := by
  slim_check (config := { randomSeed := some 257 })

-- Porting note:
-- These are the tests from mathlib3, updated to Lean 4 syntax.
-- Many of these fail, I think because of missing `Testable` instances.
-- Hopefully Henrik Böving and/or Simon Hudon could look at this.

example : true := by
  have : ∀ i j : ℕ, i < j → j < i := by
    success_if_fail_with_msg "
===================
Found problems!
i := 0
j := 1
guard: 0 < 1
issue: 1 < 0 does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example : true := by
  have : (∀ x : ℕ, 2 ∣ x → x < 100) := by
    success_if_fail_with_msg "
===================
Found problems!
x := 104
guard: ⋯
issue: 104 < 100 does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257, maxSize := 200 })
    exact test_sorry
  trivial

-- example (xs : List ℕ) (w : ∃ x ∈ xs, x < 3) : true := by
--   have : ∀ y ∈ xs, y < 5
--   success_if_fail_with_msg
-- "
-- ===================
-- Found problems!

-- xs := [5, 5, 0, 1]
-- x := 0
-- y := 5
-- issue: 5 < 5 does not hold
-- (5 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial

example (x : ℕ) (_h : 2 ∣ x) : true := by
  have : x < 100 := by
    success_if_fail_with_msg
    "
===================
Found problems!
x := 104
guard: ⋯
issue: 104 < 100 does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257, maxSize := 200 })
    exact test_sorry
  trivial

example (α : Type) (xs ys : List α) : true := by
  have : xs ++ ys = ys ++ xs := by
    success_if_fail_with_msg
    "
===================
Found problems!
α := \"ℤ\"
xs := [0, 0]
ys := [-1]
issue: [0, 0, -1] = [-1, 0, 0] does not hold
(2 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example : true := by
  have _this : ∀ x ∈ [1,2,3], x < 4
  · slim_check (config := { randomSeed := some 257, quiet := true })
    -- success
  trivial

-- Making sure that the context is used
example : true := by
  have _this : ∀ n : ℕ, n = n
  · intro n
    cases n
    · slim_check (config := { randomSeed := some 257, quiet := true })
    · rfl
    -- success
  trivial

open Function SlimCheck

-- Porting note: the "small" functor provided in mathlib3's `Sampleable.lean` was not ported,
-- so we should not expect this to work.
-- example (f : ℤ → ℤ) (h : Injective f) : true := by
--   have : Monotone (f ∘ small.mk)
--   success_if_fail_with_msg
--     "
-- ===================
-- Found problems!

-- f := [2 ↦ 3, 3 ↦ 9, 4 ↦ 6, 5 ↦ 4, 6 ↦ 2, 8 ↦ 5, 9 ↦ 8, x ↦ x]
-- x := 3
-- y := 4
-- guard: 3 ≤ 4 (by construction)
-- issue: 9 ≤ 6 does not hold
-- (5 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial

example (f : ℤ → ℤ) (_h : Injective f) (g : ℤ → ℤ) (_h : Injective g) (i : ℤ) : true := by
  have : f i = g i := by
    success_if_fail_with_msg
"
===================
Found problems!
f := [x ↦ x]
guard: ⋯ (by construction)
g := [0 ↦ 0, 1 ↦ 3, 2 ↦ 1, 3 ↦ 2, x ↦ x]
guard: ⋯ (by construction)
i := 1
issue: 1 = 3 does not hold
(2 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (f : ℤ → ℤ) (_h : Injective f) : true := by
  have : Monotone f := by
    success_if_fail_with_msg
    "
===================
Found problems!
f := [-2 ↦ 8, -3 ↦ -5, -5 ↦ -3, 8 ↦ -2, x ↦ x]
guard: ⋯ (by construction)
x := -2
y := 0
guard: -2 ≤ 0
issue: 8 ≤ 0 does not hold
(7 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (f : ℤ → ℤ) : true := by
  have : Injective f := by
    success_if_fail_with_msg
    "
===================
Found problems!
f := [_ ↦ 0]
x := 0
y := 1
guard: 0 = 0
issue: 0 = 1 does not hold
(5 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (f : ℤ → ℤ) : true := by
  have : Monotone f := by
    success_if_fail_with_msg
    "
===================
Found problems!
f := [-2 ↦ 5, -4 ↦ 1, _ ↦ -1]
x := -2
y := 0
guard: -2 ≤ 0
issue: 5 ≤ -1 does not hold
(5 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

open scoped List in
example (xs ys : List ℤ) (_h : xs ~ ys) : true := by
  have : Array.qsort ⟨xs⟩ (fun x y => x != y) = Array.qsort ⟨ys⟩ (fun x y => x != y) := by
    success_if_fail_with_msg
    "
===================
Found problems!
xs := [0, -2]
ys := [-2, 0]
guard: ⋯
issue: #[0, -2] = #[-2, 0] does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257, maxSize := 3, numRetries := 2 })
    exact test_sorry
  trivial

example (x y : ℕ) : true := by
  have : y ≤ x → x + y < 100 := by
    success_if_fail_with_msg
    "
===================
Found problems!
x := 61
y := 52
guard: 52 ≤ 61
issue: 113 < 100 does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (x : ℤ) : true := by
  have : x ≤ 3 → 3 ≤ x := by
    success_if_fail_with_msg
    "
===================
Found problems!
x := 0
guard: 0 ≤ 3
issue: 3 ≤ 0 does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (x y : ℤ) : true := by
  have : y ≤ x → x + y < 100 := by
    success_if_fail_with_msg
    "
===================
Found problems!
x := 55
y := 51
guard: 51 ≤ 55
issue: 106 < 100 does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (x y : Prop) : true := by
  have : x ∨ y → y ∧ x := by
    success_if_fail_with_msg
    "
===================
Found problems!
x := false
y := true
guard: false ∨ true
issue: false does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (x y : Prop) : true := by
  have : (¬x ↔ y) → y ∧ x := by
    success_if_fail_with_msg
    "
===================
Found problems!
x := false
y := true
guard: false ≠ true ↔ true
issue: false does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (x y : Prop) : true := by
  -- deterministic
  have : (x ↔ y) → y ∨ x := by
    success_if_fail_with_msg
  "
===================
Found problems!
x := false
y := false
guard: false ↔ false
issue: false does not hold
issue: false does not hold
(0 shrinks)
-------------------
"
      slim_check
    exact test_sorry
  trivial

example (x y : Prop) : true := by
  -- deterministic
  have : y ∨ x := by
    success_if_fail_with_msg
  "
===================
Found problems!
x := false
y := false
issue: false does not hold
issue: false does not hold
(0 shrinks)
-------------------
"
      slim_check
    exact test_sorry
  trivial

example (x y : Prop) : true := by
  have : x ↔ y := by
    success_if_fail_with_msg
    "
===================
Found problems!
x := false
y := true
issue: false does not hold
issue: true ≠ true does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

-- TODO: fails without this line!
attribute [-instance] Finsupp.instRepr in

example (f : ℕ →₀ ℕ) : true := by
  have : f = 0 := by
    success_if_fail_with_msg
    "
===================
Found problems!
f := [1 ↦ 1, _ ↦ 0]
issue: ⋯ does not hold
(1 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (f : Π₀ _n : ℕ, ℕ) : true := by
  have : f.update 0 0 = 0 := by
    success_if_fail_with_msg
    "
===================
Found problems!
f := [1 ↦ 1, _ ↦ 0]
issue: ⋯ does not hold
(1 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (n : ℕ) : true := by
  have : ∑ f : Unit → Fin (n + 1), f () = 0 := by
    success_if_fail_with_msg "
===================
Found problems!
n := 1
issue: 1 = 0 does not hold
(0 shrinks)
-------------------
"
      slim_check (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/slim_check.20question/near/412709012
/--
info: Success
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (q : ℕ) : q = 0 ∨ q ≥ 2 ∨
    8 = ∑ k ∈ Finset.range 2, 5 ^ k * Nat.choose (2 * q + 1) (2 * k + 1) := by
  slim_check

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/slim_check.20giving.20wrong.20counterexamples.3F/near/420008365
open Nat in
/--
info: Success
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem testBit_pred :
    testBit (pred x) i = (decide (0 < x) &&
      (Bool.xor ((List.range i).all fun j => ! testBit x j) (testBit x i))) := by
  slim_check

-- https://github.com/leanprover-community/mathlib4/issues/12565
-- Make `slim_check` handle `Fact` instances.
/--
error:
===================
Found problems!
a := 7
guard: ⋯
issue: ⋯ does not hold
issue: ⋯ does not hold
(0 shrinks)
-------------------
-/
#guard_msgs in
example {a : ℕ} [Fact a.Prime] : (a + 1).Prime ∨ (a + 2).Prime := by
  slim_check (config := { randomSeed := some 257 })
