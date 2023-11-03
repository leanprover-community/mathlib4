import Std.Tactic.GuardMsgs
import Mathlib.Mathport.Notation
import Mathlib.Init.Data.Nat.Lemmas

set_option pp.unicode.fun true
set_option autoImplicit true

namespace Test

-- set_option trace.notation3 true

def Filter (α : Type) : Type := (α → Prop) → Prop
def Filter.atTop [Preorder α] : Filter α := fun _ => True
def Filter.eventually (p : α → Prop) (f : Filter α) := f p

notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r

/-- info: ∀ᶠ (x : ℕ) (y : ℕ) in Filter.atTop, x < y : Prop -/
#guard_msgs in #check ∀ᶠ (x : Nat) (y) in Filter.atTop, x < y
/-- info: ∀ᶠ (x : ℕ) in Filter.atTop, x < 3 : Prop -/
#guard_msgs in #check ∀ᶠ x in Filter.atTop, x < 3

-- Testing lambda expressions:
notation3 "∀ᶠ' " f ", " p => Filter.eventually (fun x => (p : _ → _) x) f
/-- info: ∀ᶠ' Filter.atTop, fun x ↦ x < 3 : Prop -/
#guard_msgs in #check ∀ᶠ' Filter.atTop, fun x => x < 3

def foobar (p : α → Prop) (f : Prop) := ∀ x, p x = f

notation3 "∀ᶠᶠ " (...) " in " f ": "
  r1:(scoped p => Filter.eventually p f) ", " r2:(scoped p => foobar p r1) => r2

/-- info: ∀ᶠᶠ (x : ℕ) (y : ℕ) in Filter.atTop: x < y, x = y : Prop -/
#guard_msgs in #check ∀ᶠᶠ (x : Nat) (y) in Filter.atTop: x < y, x = y
/-- info: ∀ᶠᶠ (x : ℕ) in Filter.atTop: x < 3, x = 1 : Prop -/
#guard_msgs in #check ∀ᶠᶠ x in Filter.atTop: x < 3, x = 1
/-- info: ∀ᶠᶠ (x : ℕ) in Filter.atTop: x < 3, x = 1 : Prop -/
#guard_msgs in #check foobar (fun x ↦ Eq x 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)
/-- info: foobar (fun y ↦ y = 1) (∀ᶠ (x : ℕ) in Filter.atTop, x < 3) : Prop -/
#guard_msgs in #check foobar (fun y ↦ Eq y 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)

notation3 "∃' " (...) ", " r:(scoped p => Exists p) => r
/-- info: ∃' (x : ℕ) (_ : x < 3), x < 3 : Prop -/
#guard_msgs in #check ∃' x < 3, x < 3

def func (x : α) : α := x
notation3 "func! " (...) ", " r:(scoped p => func p) => r
-- Make sure it handles additional arguments. Should not consume `(· * 2)`.
-- Note: right now this causes the notation to not pretty print at all.
/-- info: func (fun x ↦ x) fun x ↦ x * 2 : ℕ → ℕ -/
#guard_msgs in #check (func! (x : Nat → Nat), x) (· * 2)

structure MyUnit where
notation3 "~{" (x"; "* => foldl (a b => (a, b)) MyUnit) "}~" => x
/-- info: ~{1; true; ~{2}~}~ : ((Type × ℕ) × Bool) × Type × ℕ -/
#guard_msgs in #check ~{1; true; ~{2}~}~
/-- info: ~{}~ : Type -/
#guard_msgs in #check ~{}~

structure MyUnit' where
instance : OfNat MyUnit' (nat_lit 0) := ⟨{}⟩
notation3 "MyUnit'0" => (0 : MyUnit')
/-- info: MyUnit'0 : MyUnit' -/
#guard_msgs in #check (0 : MyUnit')
/-- info: 0 : ℕ -/
#guard_msgs in #check 0

notation3 "%[" (x", "* => foldr (a b => a :: b) []) "]" => x
/-- info: %[1, 2, 3] : List ℕ -/
#guard_msgs in #check %[1, 2, 3]

def foo (a : Nat) (f : Nat → Nat) := a + f a
def bar (a b : Nat) := a * b
notation3 "*[" x "] " (...) ", " v:(scoped c => bar x (foo x c)) => v
/-- info: *[1] (x : ℕ) (y : ℕ), x + y : ℕ -/
#guard_msgs in #check *[1] (x) (y), x + y
/-- info: bar 1 : ℕ → ℕ -/
#guard_msgs in #check bar 1

-- Checking that the `<|` macro is expanded when making matcher
def foo' (a : Nat) (f : Nat → Nat) := a + f a
def bar' (a b : Nat) := a * b
notation3 "*'[" x "] " (...) ", " v:(scoped c => bar' x <| foo' x c) => v
/-- info: *'[1] (x : ℕ) (y : ℕ), x + y : ℕ -/
#guard_msgs in #check *'[1] (x) (y), x + y
/-- info: bar' 1 : ℕ → ℕ -/
#guard_msgs in #check bar' 1

-- Need to give type ascription to `p` so that `p x` elaborates when making matcher
notation3 "MyPi " (...) ", " r:(scoped p => (x : _) → (p : _ → _) x) => r
/-- info: MyPi (x : ℕ) (y : ℕ), x < y : Prop -/
#guard_msgs in #check MyPi (x : Nat) (y : Nat), x < y

-- The notation parses fine, but the delaborator never succeeds, which is expected
def myId (x : α) := x
notation3 "BAD " c "; " (x", "* => foldl (a b => b) c) " DAB" => myId x
/-- info: myId 3 : ℕ -/
#guard_msgs in #check BAD 1; 2, 3 DAB

section
variable (x : Nat)
local notation3 "y" => x + 1
/-- info: y : ℕ -/
#guard_msgs in #check y
/-- info: y : ℕ -/
#guard_msgs in #check x + 1
end

section
variable (α : Type u) [Add α]
local notation3 x " +α " y => (x + y : α)
variable (x y : α)
/-- info: x +α y : α -/
#guard_msgs in #check x +α y
/-- info: x +α y : α -/
#guard_msgs in #check x + y
/-- info: 1 + 2 : ℕ -/
#guard_msgs in #check 1 + 2
end

def idStr : String → String := id

/--
error: application type mismatch
  idStr Nat.zero
argument
  Nat.zero
has type
  ℕ : Type
but is expected to have type
  String : Type
---
warning: Was not able to generate a pretty printer for this notation. If you do not expect it to be
pretty printable, then you can use `notation3 (prettyPrint := false)`. If the notation expansion
refers to section variables, be sure to do `local notation3`. Otherwise, you might be able to adjust
the notation expansion to make it matchable; pretty printing relies on deriving an expression
matcher from the expansion. (Use `set_option trace.notation3 true` to get some debug information.)
-/
#guard_msgs in
notation3 "error" => idStr Nat.zero

section
/--
warning: Was not able to generate a pretty printer for this notation. If you do not expect it to be
pretty printable, then you can use `notation3 (prettyPrint := false)`. If the notation expansion
refers to section variables, be sure to do `local notation3`. Otherwise, you might be able to adjust
the notation expansion to make it matchable; pretty printing relies on deriving an expression
matcher from the expansion. (Use `set_option trace.notation3 true` to get some debug information.)
-/
#guard_msgs (warning, drop error) in local notation3 "#" n => Fin.mk n (by decide)
end

section
local notation3 (prettyPrint := false) "#" n => Fin.mk n (by decide)

example : Fin 5 := #1

/--
error: failed to reduce to 'true'
  false
-/
#guard_msgs in example : Fin 5 := #6

end

section test_scoped

scoped[MyNotation] notation3 "π" => (3 : Nat)

/-- error: unknown identifier 'π' -/
#guard_msgs in #check π

open scoped MyNotation

/-- info: π : ℕ -/
#guard_msgs in #check π

end test_scoped

section FlexibleBinders

def Filter.top {α : Type} : Filter α := fun s => ∀ x, s x

section
open Mathlib.FlexibleBinders

syntax "filter%" : flexibleBindersDom

macro_rules
  | `(binder%(filter%, $e ∈ $f)) => do
    let (e, ty) ← destructAscription e
    `(binderResolved%($ty, $e, $f))

end

notation3 "∀ᶠ' " (...) ", "
    r:(scoped filter% p => Filter.eventually p Filter.top,
       bounded := f p => Filter.eventually p f) => r

/-- info: ∀ᶠ' (x : ℕ), 1 < x : Prop -/
#guard_msgs in #check ∀ᶠ' x : Nat, 1 < x
/-- info: fun f ↦ ∀ᶠ' x ∈ f, 1 < x : Filter ℕ → Prop -/
#guard_msgs in #check fun (f : Filter Nat) => ∀ᶠ' x ∈ f, 1 < x

/-- info: foobar (fun y ↦ y = 1) (∀ᶠ' x ∈ Filter.atTop, x < π) : Prop -/
#guard_msgs in #check foobar (fun y ↦ Eq y 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)

inductive ExistsF {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : ExistsF p

notation3 "∃F " (...) ", " r:(scoped p => Exists p, prop := p r => p ∧ r) => r

/-- info: ∃F (x : ℕ), x = x : Prop -/
#guard_msgs in #check ∃F (x : Nat), x = x
/-- info: ∃F (x : ℕ) (y : ℕ), y < x ∧ x = y : Prop -/
#guard_msgs in #check ∃F (x : Nat) (y < x), x = y
/-- info: ∃F (x : ℕ), x < 10 ∧ ∃F (y : ℕ), y < 10 ∧ x + y = 1 : Prop -/
#guard_msgs in #check ∃F x y < 10, x + y = 1

structure Finset (α : Type _) where
  s : α → Prop

class Fintype (α : Type _) where
  univ : Finset α

def Finset.univ {α : Type _} [Fintype α] : Finset α := Fintype.univ

def Set (α : Type _) := α → Prop
instance {α : Type _} : Membership α (Set α) := ⟨fun x s => s x⟩
instance {α : Type _} : CoeSort (Set α) (Type _) := ⟨fun s => {x // x ∈ s}⟩
def Set.toFinset {α : Type _} (s : Set α) [Fintype s] : Finset α := .mk s

def Finset.sum {α : Type _} (_s : Finset α) (_f : α → Nat) : Nat := 0

namespace FinsetFlex
open Lean Meta Mathlib.FlexibleBinders

/-- `finset% t` elaborates `t` as a `Finset`.
If `t` is a `Set`, then inserts `Set.toFinset`.
Does not make use of the expected type. Useful for big operators over finsets.
```
#check finset% Finset.range 2 -- Finset Nat
#check finset% (Set.univ : Set Bool) -- Finset Bool
```
-/
elab (name := finsetStx) "finset% " t:term : term => do
  let u ← mkFreshLevelMVar
  let ty ← mkFreshExprMVar (mkSort (.succ u))
  let x ← Elab.Term.elabTerm t (mkApp (.const ``Finset [u]) ty)
  let xty ← whnfR (← inferType x)
  if xty.isAppOfArity ``Set 1 then
    Elab.Term.elabAppArgs (.const ``Set.toFinset [u]) #[] #[.expr x] none false false
  else
    return x

-- open Lean.Elab.Term.Quotation in
-- /-- `quot_precheck` for the `finset%` syntax. -/
-- @[quot_precheck Test.FinsetFlex.finsetStx] def precheckFinsetStx : Precheck
--   | `(finset% $t) => precheck t
--   | _ => Elab.throwUnsupportedSyntax

/-- For the `finset` domain, `(x ∈ s)` is a binder over `s` as a `Finset`. -/
macro_rules
  | `(binder%(finset%, $e ∈ $s)) => do
    let (e, ty) ← destructAscription e
    `(binderResolved%($ty, $e, finset% $s))
end FinsetFlex

notation3 "∑ " (...) ", "
    r:(scoped finset% p => Finset.sum Finset.univ p,
       --prop := p b => Finset.sum Finset.univ (fun (_ : PLift p) => b),
       prop := p b => if p then b else 0,
       bounded := s p => Finset.sum (finset% s) p) => r

instance (n : Nat) : Fintype (Fin n) := .mk (.mk fun _ => False)
instance {p : Prop} [Decidable p] : Fintype (PLift p) := .mk (.mk fun _ => False)
section
variable (s : Finset Nat) (s' : Set Nat) [Fintype s']

/-- info: ∑ (x : Fin 37) (y ∈ s), ↑x + y : ℕ -/
#guard_msgs in #check ∑ (x : Fin 37) (y ∈ s), x + y
/-- info: ∑ x ∈ Set.toFinset s', x : ℕ -/
#guard_msgs in #check ∑ x ∈ s', x
/-- info: ∑ (x : Fin 37), if x < 10 then ∑ (y : Fin 37), if y < 10 then ↑x + ↑y else 0 else 0 : ℕ -/
#guard_msgs in #check ∑ (x y : Fin 37) < 10, x + y

/-- info: MyPi x ∈ s', 0 < x : Prop -/
#guard_msgs in #check MyPi x ∈ s', 0 < x
end

/-
variable (s : Finset α) (u : α → Finset β) (f : α → β → ℕ)
#check ∑ (x ∈ s) × (y ∈ u x), f x y
/-
∑ x ∈ Finset.sigma s fun x ↦ u x,
  match x with
  | { fst := x, snd := y } => f x y : ℕ
-/
#test_flexible_binders finset% => x y ∈ s when x = x

variable (s : Finset Nat)
#check ∑ x ∈ s when x < 10, 2 * x
/-
∑ x ∈ Finset.filter (fun x ↦ x < 10) s, 2 * x : ℕ
-/
#check ∑ x y ∈ s when x < y, 2 * x * y
/-
∑ (x ∈ s) (y ∈ Finset.filter (fun y ↦ x < y) s), 2 * x * y : ℕ
-/

#test_flexible_binders finset% => (x ∈ s) × (y ∈ u x)
-/


end FlexibleBinders
