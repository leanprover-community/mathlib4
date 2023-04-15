import Mathlib.Tactic.NthRewrite
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Vector
import Mathlib.Data.Nat.Basic

example [AddZeroClass G] {a : G} (h : a = a): a = (a + 0) := by
  nth_rewrite 2 [←add_zero a] at h
  exact h

example [AddZeroClass G] {a : G} : a + a = a + (a + 0) := by
  nth_rw 2 [←add_zero a]

structure F :=
(a : ℕ)
(v : Vector ℕ a)
(p : v.val = [])

example (f : F) : f.v.val = [] := by
  nth_rw 1 [f.p]

structure Cat :=
  (O : Type)
  (H : O → O → Type)
  (i : (o : O) →  H o o)
  (c : {X Y Z : O} → (f : H X Y) → (g : H Y Z) → H X Z)
  (li : ∀ {X Y : O} (f : H X Y), c (i X) f = f)
  (ri : ∀ {X Y : O} (f : H X Y), c f (i Y) = f)
  (a : ∀ {W X Y Z : O} (f : H W X) (g : H X Y) (h : H Y Z), c (c f g) h = c f (c g h))

example (C : Cat) (W X Y Z : C.O) (f : C.H X Y) (g : C.H W X) (h _k : C.H Y Z) :
    C.c (C.c g f) h = C.c g (C.c f h) := by
  nth_rw 1 [C.a]

example (C : Cat) (X Y : C.O) (f : C.H X Y) : C.c f (C.i Y) = f := by
  nth_rw 1 [C.ri]

-- Porting note: the next test fails because `nth_rewrite` has unfortunately changed behaviour
-- since mathlib3.

-- example (x y z : ℕ) (h1 : x = y) (h2 : y = z) :
--   x + x + x + y = y + y + x + x := by
--   nth_rewrite 3 [h1, h2] -- h2 is not used
--   nth_rewrite 3 [h2]
--   repeat { rw [h1] }
--   repeat { rw [h2] }

-- Porting note:
-- The remaining tests haven't been ported from Lean3 yet because we don't have an implementation
-- of `nth_rewrite_lhs`.

-- -- The next two examples fail when using the kabstract backend.

-- axiom foo : [1] = [2]

-- example : [[1], [1], [1]] = [[1], [2], [1]] := by
--   nth_rewrite_lhs 2 [foo]

-- axiom foo' : [6] = [7]
-- axiom bar' : [[5],[5]] = [[6],[6]]

-- example : [[7],[6]] = [[5],[5]] :=
-- begin
--   nth_rewrite_lhs 0 foo',
--   nth_rewrite_rhs 0 bar',
--   nth_rewrite_lhs 0 ←foo',
--   nth_rewrite_lhs 0 ←foo',
-- end

-- axiom wowzer : (3, 3) = (5, 2)
-- axiom kachow (n : ℕ) : (4, n) = (5, n)
-- axiom pchew (n : ℕ) : (n, 5) = (5, n)
-- axiom smash (n m : ℕ) : (n, m) = (1, 1)

-- example : [(3, 3), (5, 9), (5, 9)] = [(4, 5), (3, 6), (1, 1)] :=
-- begin
--   nth_rewrite_lhs 0 wowzer,
--   nth_rewrite_lhs 2 ←pchew,
--   nth_rewrite_rhs 0 pchew,

--   nth_rewrite_rhs 0 smash,
--   nth_rewrite_rhs 1 smash,
--   nth_rewrite_rhs 2 smash,
--   nth_rewrite_lhs 0 smash,
--   nth_rewrite_lhs 1 smash,
--   nth_rewrite_lhs 2 smash,
-- end

-- example (a b c : ℕ) : c + a + b = a + c + b :=
-- begin
--   nth_rewrite_rhs 1 add_comm,
-- end
-- -- With the `kabstract` backend, we only find one rewrite, even though there are obviously two.
-- -- The problem is that `(a + b) + c` matches directly, so the WHOLE THING gets replaced with a
-- -- metavariable, per the `kabstract` strategy. This is devastating to the search, since we cannot
-- -- see inside this metavariable.

-- -- I still think it's fixable. Because all applications have an order, I'm pretty sure we can't
-- -- miss any rewrites if we also look inside every thing we chunk-up into a metavariable as well.
-- -- In almost every case this will bring up no results (with the exception of situations like this
-- -- one), so there should be essentially no change in complexity.

-- example (x y : Prop) (h₁ : x ↔ y) (h₂ : x ↔ x ∧ x) : x ∧ x ↔ x :=
-- begin
--   nth_rewrite_rhs 1 [h₁] at h₂,
--   nth_rewrite_rhs 0 [← h₁] at h₂,
--   nth_rewrite_rhs 0 h₂,
-- end

-- example (x y : ℕ) (h₁ : x = y) (h₂ : x = x + x) : x + x = x :=
-- begin
--   nth_rewrite_rhs 1 [h₁] at h₂,
--   nth_rewrite_rhs 0 [← h₁] at h₂,
--   nth_rewrite_rhs 0 h₂,
-- end
