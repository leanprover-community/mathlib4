import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.SuccessIfFailWithMsg
import Mathlib.Testing.Plausible.Functions
import Mathlib.Testing.Plausible.Sampleable
import Plausible

private axiom test_sorry : ∀ {α}, α

/--
error:
===================
Found a counter-example!
x := 104
guard: ⋯
issue: 104 < 100 does not hold
(0 shrinks)
-------------------
-/
#guard_msgs in
example : ∀ x : ℕ, 2 ∣ x → x < 100 := by
  plausible (config := { randomSeed := some 257, maxSize := 200 })

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
--     plausible (config := { randomSeed := some 257 })
--   admit
--   trivial

example (x : ℕ) (_h : 2 ∣ x) : true := by
  have : x < 100 := by
    success_if_fail_with_msg
    "
===================
Found a counter-example!
x := 104
guard: ⋯
issue: 104 < 100 does not hold
(0 shrinks)
-------------------
"
      plausible (config := { randomSeed := some 257, maxSize := 200 })
    exact test_sorry
  trivial

open Function Plausible

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
--     plausible (config := { randomSeed := some 257 })
--   admit
--   trivial

/--
error:
===================
Found a counter-example!
f := [x ↦ x]
guard: ⋯ (by construction)
g := [0 => 0, 1 => 3, 2 => 1, 3 => 2, x ↦ x]
guard: ⋯ (by construction)
i := 1
issue: 1 = 3 does not hold
(2 shrinks)
-------------------
-/
#guard_msgs in
example (f : ℤ → ℤ) (_h : Injective f) (g : ℤ → ℤ) (_h : Injective g) (i : ℤ) : f i = g i := by
  plausible (config := { randomSeed := some 257 })

/--
error:
===================
Found a counter-example!
f := [-2 => 8, -3 => -5, -5 => -3, 8 => -2, x ↦ x]
guard: ⋯ (by construction)
x := -2
y := 0
guard: -2 ≤ 0
issue: 8 ≤ 0 does not hold
(7 shrinks)
-------------------
-/
#guard_msgs in
example (f : ℤ → ℤ) (_h : Injective f) : Monotone f := by
  plausible (config := { randomSeed := some 257 })

/--
error:
===================
Found a counter-example!
f := [_ => 0]
x := 0
y := 1
guard: 0 = 0
issue: 0 = 1 does not hold
(5 shrinks)
-------------------
-/
#guard_msgs in
example (f : ℤ → ℤ) : Injective f := by
  plausible (config := { randomSeed := some 257 })

/--
error:
===================
Found a counter-example!
f := [-2 => 5, -4 => 0, _ => 0]
x := -2
y := 1
guard: -2 ≤ 1
issue: 5 ≤ 0 does not hold
(3 shrinks)
-------------------
-/
#guard_msgs in
example (f : ℤ → ℤ) : Monotone f := by
  plausible (config := { randomSeed := some 257 })

-- TODO: fails without this line!
attribute [-instance] Finsupp.instRepr in

example (f : ℕ →₀ ℕ) : true := by
  have : f = 0 := by
    success_if_fail_with_msg
    "
===================
Found a counter-example!
f := [1 => 1, _ => 0]
issue: ⋯ does not hold
(1 shrinks)
-------------------
"
      plausible (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (f : Π₀ _n : ℕ, ℕ) : true := by
  have : f.update 0 0 = 0 := by
    success_if_fail_with_msg
    "
===================
Found a counter-example!
f := [1 => 1, _ => 0]
issue: ⋯ does not hold
(1 shrinks)
-------------------
"
      plausible (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

example (n : ℕ) : true := by
  have : ∑ f : Unit → Fin (n + 1), f () = 0 := by
    success_if_fail_with_msg "
===================
Found a counter-example!
n := 1
issue: 1 = 0 does not hold
(0 shrinks)
-------------------
"
      plausible (config := { randomSeed := some 257 })
    exact test_sorry
  trivial

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/slim_check.20question/near/412709012
/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (q : ℕ) : q = 0 ∨ q ≥ 2 ∨
    8 = ∑ k ∈ Finset.range 2, 5 ^ k * Nat.choose (2 * q + 1) (2 * k + 1) := by
  plausible

-- https://github.com/leanprover-community/mathlib4/issues/12565
-- Make `plausible` handle `Fact` instances.
/--
error:
===================
Found a counter-example!
a := 7
guard: ⋯
issue: ⋯ does not hold
issue: ⋯ does not hold
(0 shrinks)
-------------------
-/
#guard_msgs in
example {a : ℕ} [Fact a.Prime] : (a + 1).Prime ∨ (a + 2).Prime := by
  plausible (config := { randomSeed := some 257 })

/--
error:
===================
Found a counter-example!
x := 4
issue: 64 < 42 does not hold
(0 shrinks)
-------------------
-/
#guard_msgs in
example (x : PNat) : x^3 < 2*x^2 + 10:= by
  plausible (config := { randomSeed := some 257 })
