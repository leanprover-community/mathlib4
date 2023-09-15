import Mathlib.Tactic.SlimCheck
import Mathlib.Tactic.SuccessIfFailWithMsg
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.DFinsupp.Basic

-- Porting note:
-- These are the tests from mathlib3, updated to Lean 4 syntax.
-- Many of these fail, I think because of missing `Testable` instances.
-- Hopefully Henrik Böving and/or Simon Hudon could look at this.

example : true := by
  have : ∀ i j : ℕ, i < j → j < i
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
  admit
  trivial

-- example : true := by
--   have : (∀ x : ℕ, 2 ∣ x → x < 100)
--   success_if_fail_with_msg
--   "
-- ===================
-- Found problems!

-- x := 104
-- issue: 104 < 100 does not hold
-- (2 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial

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

-- example (x : ℕ) (h : 2 ∣ x) : true := by
--   have : x < 100
--   success_if_fail_with_msg
--     "
-- ===================
-- Found problems!

-- x := 104
-- issue: 104 < 100 does not hold
-- (2 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial

-- example (α : Type) (xs ys : List α) : true := by
--   have : xs ++ ys = ys ++ xs
--   success_if_fail_with_msg
--     "
-- ===================
-- Found problems!

-- α := ℤ
-- xs := [0]
-- ys := [1]
-- issue: [0, 1] = [1, 0] does not hold
-- (4 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial

example : true := by
  have _this : ∀ x ∈ [1,2,3], x < 4
  slim_check (config := { randomSeed := some 257, quiet := true })
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

-- example (f : ℤ → ℤ) (h : Injective f) (g : ℤ → ℤ) (h : Injective g) (i) : true := by
--   have : f i = g i
--   success_if_fail_with_msg
-- "
-- ===================
-- Found problems!

-- f := [x ↦ x]
-- g := [1 ↦ 2, 2 ↦ 1, x ↦ x]
-- i := 1
-- issue: 1 = 2 does not hold
-- (5 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial

-- example (f : ℤ → ℤ) (h : Injective f) : true := by
--   have : Monotone f
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

-- example (f : ℤ → ℤ) : true := by
--   have : Injective f
--   success_if_fail_with_msg
--     "
-- ===================
-- Found problems!

-- f := [_ ↦ 0]
-- x := 0
-- y := -1
-- guard: 0 = 0
-- issue: 0 = -1 does not hold
-- (0 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial

-- example (f : ℤ → ℤ) : true := by
--   have : Monotone f
--   success_if_fail_with_msg
--     "
-- ===================
-- Found problems!

-- f := [-6 ↦ 97, 0 ↦ 0, _ ↦ 4]
-- x := -6
-- y := -2
-- guard: -6 ≤ -2 (by construction)
-- issue: 97 ≤ 4 does not hold
-- (5 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial

-- Porting note: In Lean 4, we have Array.qsort, not List.qsort, so this test will need modifying.
-- example (xs ys : List ℤ) (h : xs ~ ys) : true := by
--   have : List.qsort (fun x y => x ≠ y) xs = List.qsort (fun x y => x ≠ y) ys
--   success_if_fail_with_msg
--     "
-- ===================
-- Found problems!

-- xs := [0, 1]
-- ys := [1, 0]
-- guard: [0, 1] ~ [1, 0] (by construction)
-- issue: [0, 1] = [1, 0] does not hold
-- (4 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial

example (x y : ℕ) : true := by
  have : y ≤ x → x + y < 100
  success_if_fail_with_msg
    "
===================
Found problems!
x := 68
y := 34
guard: 34 ≤ 68
issue: 102 < 100 does not hold
(0 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

example (x : ℤ) : true := by
  have : x ≤ 3 → 3 ≤ x
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
  admit
  trivial

example (x y : ℤ) : true := by
  have : y ≤ x → x + y < 100
  success_if_fail_with_msg
    "
===================
Found problems!
x := 73
y := 73
guard: 73 ≤ 73
issue: 146 < 100 does not hold
(0 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

example (x y : Prop) : true := by
  have : x ∨ y → y ∧ x
  success_if_fail_with_msg
    "
===================
Found problems!
x := true
y := false
guard: true ∨ false
issue: false does not hold
(0 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

example (x y : Prop) : true := by
  have : (¬x ↔ y) → y ∧ x
  success_if_fail_with_msg
    "
===================
Found problems!
x := true
y := false
guard: true ≠ true ↔ false
issue: false does not hold
(0 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

example (x y : Prop) : true := by
  -- deterministic
  have : (x ↔ y) → y ∨ x
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
  admit
  trivial

example (x y : Prop) : true := by
  -- deterministic
  have : y ∨ x
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
  admit
  trivial

example (x y : Prop) : true := by
  have : x ↔ y
  success_if_fail_with_msg
    "
===================
Found problems!
x := true
y := false
issue: false does not hold
issue: true ≠ true does not hold
(0 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

-- example (f : ℕ →₀ ℕ) : true := by
--   have : f = 0
--   success_if_fail_with_msg
--     "
-- ===================
-- Found problems!

-- f := [0 ↦ 1, _ ↦ 0]
-- issue: finsupp.single 0 1 = 0 does not hold
-- (2 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial

-- example (f : Π₀ n : ℕ, ℕ) : true := by
--   have : f.update 0 0 = 0
--   success_if_fail_with_msg
--     "
-- ===================
-- Found problems!

-- f := [1 ↦ 1, _ ↦ 0]
-- (1 shrinks)
-- -------------------
-- "
--     slim_check (config := { randomSeed := some 257 })
--   admit
--   trivial
