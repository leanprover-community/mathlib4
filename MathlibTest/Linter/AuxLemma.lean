module

public import Mathlib.Tactic.Linter.AuxLemma
public import Mathlib.Init
public import Init.Data.Iterators.Combinators.Monadic.FilterMap

/-!
# Tests for the `auxLemma` linter

The important tests here reference *genuinely* auto-generated declarations (`match_1`,
`_proof_1`, `_sizeOf_1`), produced by the elaborator from the definitions below. If Lean's
naming scheme for these auxiliary declarations ever changes, these tests break — which is the
point: the linter would otherwise silently stop catching anything.
-/

set_option linter.auxLemma true

-- A `match`-based definition generates an auxiliary `foo.match_1`.
def foo : Nat → Nat
  | 0 => 0
  | n + 1 => n

-- A structure with a proof field, plus an instance discharging it by tactic, generates
-- `s._proof_1`; the structure itself generates `S._sizeOf_1`.
structure S where
  n : Nat
  h : 0 < n

def s : S where
  n := 1
  h := by decide

/--
warning: `foo.match_1` refers to an auto-generated auxiliary declaration. These are not stable across refactors; consider using a different approach.

Note: This linter can be disabled with `set_option linter.auxLemma false`
-/
#guard_msgs in
example := @foo.match_1

/--
warning: `s._proof_1` refers to an auto-generated auxiliary declaration. These are not stable across refactors; consider using a different approach.

Note: This linter can be disabled with `set_option linter.auxLemma false`
-/
#guard_msgs in
example := s._proof_1

-- `_sizeOf_1` is a compiler-internal that cannot be used as a term value, so we reference it
-- with `#check` and only guard the linter warning (ignoring the `#check` info output).
/--
warning: `S._sizeOf_1` refers to an auto-generated auxiliary declaration. These are not stable across refactors; consider using a different approach.

Note: This linter can be disabled with `set_option linter.auxLemma false`
-/
#guard_msgs(drop info, warning) in
#check @S._sizeOf_1

-- No warning on ordinary references, including names that merely resemble the auxiliary
-- patterns but lack the trailing digits (e.g. `Nat.rec`, `foo`).
#guard_msgs in
example := @foo

#guard_msgs in
example := @Nat.rec

-- The linter can be turned off.
set_option linter.auxLemma false in
#guard_msgs in
example := @foo.match_1

-- copied from `Std.Iterators.Types.FilterMap.instIterator` at the time of writing this test
-- `_aux_1` refers to the first field of the instance `fooAux`
open Std Iterators in
universe w w' w'' in
instance fooAux {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Monad n]
    [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α} {f : β → PostconditionT n γ} :
    Iterator (Types.Map α m n lift f) n γ :=
  inferInstanceAs <| Iterator (Types.FilterMap α m n lift _) n γ

/--
warning: `fooAux._aux_1` refers to an auto-generated auxiliary declaration. These are not stable across refactors; consider using a different approach.

Note: This linter can be disabled with `set_option linter.auxLemma false`
-/
#guard_msgs(drop info,warning) in
#check fooAux._aux_1

-- minimised from `BitVec.lt_of_msb_false_of_msb_true` at the time of writing this test
structure Foo where
  data : Nat

def Foo.bar (_x : Foo) : Bool := false

instance : LT (Foo) := ⟨fun x y ↦ x.data < y.data⟩

axiom silentSorry {α} : α
@[simp]
theorem fooBar {x y : Foo} (_hx : x.bar = false) (_hy : y.bar = true) : x < y := silentSorry
/--
warning: `fooBar._simp_1` refers to an auto-generated auxiliary declaration. These are not stable across refactors; consider using a different approach.

Note: This linter can be disabled with `set_option linter.auxLemma false`
-/
#guard_msgs in
example {x y : Foo} := fooBar._simp_1 (x := x) (y := y)
