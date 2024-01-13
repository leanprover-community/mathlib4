import Mathlib.Tactic.SlimCheck
import Mathlib.Tactic.SuccessIfFailWithMsg
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.DFinsupp.Basic
import Mathlib.Testing.SlimCheck.Functions

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

example : true := by
  have : (∀ x : ℕ, 2 ∣ x → x < 100)
  success_if_fail_with_msg
  "
===================
Found problems!
x := 116
guard: ⋯
issue: 116 < 100 does not hold
(0 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257, maxSize := 200 })
  admit
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

example (x : ℕ) (h : 2 ∣ x) : true := by
  have : x < 100
  success_if_fail_with_msg
    "
===================
Found problems!
x := 116
guard: ⋯
issue: 116 < 100 does not hold
(0 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257, maxSize := 200 })
  admit
  trivial

example (α : Type) (xs ys : List α) : true := by
  have : xs ++ ys = ys ++ xs
  success_if_fail_with_msg
    "
===================
Found problems!
α := \"ℤ\"
xs := [0]
ys := [1]
issue: [0, 1] = [1, 0] does not hold
(4 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

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

example (f : ℤ → ℤ) (h : Injective f) (g : ℤ → ℤ) (h : Injective g) (i : ℤ) : true := by
  have : f i = g i
  success_if_fail_with_msg
"
===================
Found problems!
f := [x ↦ x]
guard: ⋯ (by construction)
g := [-2 ↦ 0, 0 ↦ -2, x ↦ x]
guard: ⋯ (by construction)
i := 0
issue: 0 = -2 does not hold
(3 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

example (f : ℤ → ℤ) (h : Injective f) : true := by
  have : Monotone f
  success_if_fail_with_msg
    "
===================
Found problems!
f := [-1 ↦ -1, 0 ↦ 0, 1 ↦ 7, 2 ↦ 2, 3 ↦ 1, 4 ↦ 3, 5 ↦ 5, 6 ↦ 6, 7 ↦ 8, 8 ↦ 4, x ↦ x]
guard: ⋯ (by construction)
x := 1
y := 3
guard: ⋯
issue: 7 ≤ 1 does not hold
(4 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

example (f : ℤ → ℤ) : true := by
  have : Injective f
  success_if_fail_with_msg
    "
===================
Found problems!
f := [_ ↦ 0]
x := 0
y := 1
guard: 0 = 0
issue: 0 = 1 does not hold
(3 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

example (f : ℤ → ℤ) : true := by
  have : Monotone f
  success_if_fail_with_msg
    "
===================
Found problems!
f := [-3 ↦ 0, -4 ↦ -1, 4 ↦ 3, _ ↦ -2]
x := -4
y := 1
guard: ⋯
issue: -1 ≤ -2 does not hold
(2 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

open scoped List in
example (xs ys : List ℤ) (h : xs ~ ys) : true := by
  have : Array.qsort ⟨xs⟩ (fun x y => x != y) = Array.qsort ⟨ys⟩ (fun x y => x != y)
  success_if_fail_with_msg
    "
===================
Found problems!
xs := [-2, -1]
ys := [-1, -2]
guard: ⋯
issue: #[-2, -1] = #[-1, -2] does not hold
(0 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257, maxSize := 3, numRetries := 1 })
  admit
  trivial

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
guard: ¬true ↔ false
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

-- TODO: fails without this line!
attribute [-instance] Finsupp.instReprFinsupp in

example (f : ℕ →₀ ℕ) : true := by
  have : f = 0
  success_if_fail_with_msg
    "
===================
Found problems!
f := [2 ↦ 1, _ ↦ 0]
issue: ⋯ does not hold
(3 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

example (f : Π₀ n : ℕ, ℕ) : true := by
  have : f.update 0 0 = 0
  success_if_fail_with_msg
    "
===================
Found problems!
f := [2 ↦ 1, _ ↦ 0]
issue: ⋯ does not hold
(3 shrinks)
-------------------
"
    slim_check (config := { randomSeed := some 257 })
  admit
  trivial

open scoped BigOperators
example (q : ℕ) : q = 0 ∨ q ≥ 2 ∨
    8 = ∑ k in Finset.range 2, 5 ^ k * Nat.choose (2 * q + 1) (2 * k + 1) := by
  success_if_fail_with_msg "no goals to be solved"
    slim_check
  sorry
