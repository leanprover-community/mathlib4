import Mathlib.Tactic.NthRewrite
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Vector.Defs
import Mathlib.Algebra.Ring.Nat

set_option autoImplicit true

example [AddZeroClass G] {a : G} (h : a = a): a = (a + 0) := by
  nth_rewrite 2 [← add_zero a] at h
  exact h

example [AddZeroClass G] {a : G} : a + a = a + (a + 0) := by
  nth_rw 2 [← add_zero a]

structure F :=
  (a : ℕ)
  (v : Vector ℕ a)
  (p : v.val = [])

example (f : F) : f.v.val = [] := by
  nth_rw 1 [f.p]

structure Cat :=
  (O : Type)
  (H : O → O → Type)
  (i : (o : O) → H o o)
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

axiom foo : [1] = [2]

example : [[1], [1], [1]] = [[1], [2], [1]] := by
  nth_rw 2 [foo]

axiom foo' : [6] = [7]
axiom bar' : [[5],[5]] = [[6],[6]]

example : [[7],[6]] = [[5],[5]] := by
  nth_rewrite 1 [foo']
  nth_rewrite 1 [bar']
  nth_rewrite 1 [← foo']
  nth_rewrite 1 [← foo']
  rfl

-- Porting note:
-- The next two tests fail because the `nth_rewrite` we have in mathlib4
-- is just a syntactic wrapper around the `Occurrences` argument
-- for the internal rewriting functions,
-- and not actually a port of the mathlib3 tactic.
-- Thus is suffers from the exact same problem:
-- when a lemma matches in several different ways,
-- we cannot rewrite via the later ones because of stuck metavariables.

-- example (a b c : ℕ) : c + a + b = a + c + b := by
--   nth_rewrite 4 [add_comm]

-- axiom wowzer : (3, 3) = (5, 2)
-- axiom kachow (n : ℕ) : (4, n) = (5, n)
-- axiom pchew (n : ℕ) : (n, 5) = (5, n)
-- axiom smash (n m : ℕ) : (n, m) = (1, 1)

-- example : [(3, 3), (5, 9), (5, 9)] = [(4, 5), (3, 6), (1, 1)] := by
--   nth_rewrite 1 [wowzer]
--   nth_rewrite 3 [← pchew]
--   nth_rewrite 1 [pchew]

--   nth_rewrite 1 [smash]
--   nth_rewrite 2 [smash]
--   nth_rewrite 3 [smash]
--   nth_rewrite 4 [smash]
--   nth_rewrite 5 [smash]
--   nth_rewrite 6 [smash]

example (x y : Prop) (h₁ : x ↔ y) (h₂ : x ↔ x ∧ x) : x ∧ x ↔ x := by
  nth_rewrite 3 [h₁] at h₂
  nth_rewrite 1 [← h₁] at h₂
  nth_rewrite 3 [h₂]
  rfl

example (x y : ℕ) (h₁ : x = y) (h₂ : x = x + x) : x + x = x := by
  nth_rewrite 3 [h₁] at h₂
  nth_rewrite 1 [← h₁] at h₂
  nth_rewrite 3 [h₂]
  rfl
