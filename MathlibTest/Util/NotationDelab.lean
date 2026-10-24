module

public import Mathlib.Util.Notation3
public import Mathlib.Data.Nat.Basic

set_option linter.style.setOption false
set_option pp.unicode.fun true
set_option autoImplicit true

namespace Test

-- set_option trace.notationDelab true

def Filter (α : Type) : Type := (α → Prop) → Prop
def Filter.atTop [Preorder α] : Filter α := fun _ => True
def Filter.eventually (p : α → Prop) (f : Filter α) := f p

notation +delab "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r

/-- info: ∀ᶠ (x : ℕ) (y : ℕ) in Filter.atTop, x < y : Prop -/
#guard_msgs in #check ∀ᶠ (x : Nat) (y) in Filter.atTop, x < y
/-- info: ∀ᶠ (x : ℕ) in Filter.atTop, x < 3 : Prop -/
#guard_msgs in #check ∀ᶠ x in Filter.atTop, x < 3

/-!
Test that `pp.tagAppFns` causes tokens to be tagged with head constant.
-/

open Lean in
meta def findWithTag (tag : Nat) (f : Format) : List Format :=
  match f with
  | .nil => []
  | .line => []
  | .align _ => []
  | .text _ => []
  | .nest _ f' => findWithTag tag f'
  | .append f' f'' => findWithTag tag f' ++ findWithTag tag f''
  | .group f' _ => findWithTag tag f'
  | .tag t f' => (if t = tag then [f'] else []) ++ findWithTag tag f'

open Lean Elab Term in
meta def testTagAppFns (n : Name) : TermElabM Unit := do
  let stx ← `(∀ᶠ x in Filter.atTop, x < 3)
  let e ← elabTermAndSynthesize stx none
  let f ← Meta.ppExprWithInfos e
  -- Find tags for the constant `n`
  let tags : Array Nat := f.infos.foldl (init := #[]) fun tags tag info =>
    match info with
    | .ofTermInfo info | .ofDelabTermInfo info =>
      if info.expr.isConstOf n then
        tags.push tag
      else
        tags
    | _ => tags
  let fmts := tags.map (findWithTag · f.fmt)
  unless fmts.all (!·.isEmpty) do throwError "missing tag"
  let fmts := fmts.toList.flatten
  logInfo m!"{repr <| fmts.map (·.pretty.trimAscii.copy)}"

section
/-- info: [] -/
#guard_msgs in #eval testTagAppFns ``Filter.eventually
set_option pp.tagAppFns true
/-- info: ["∀ᶠ", "in", ","] -/
#guard_msgs in #eval testTagAppFns ``Filter.eventually
end


-- Testing lambda expressions:
notation +delab "∀ᶠ' " f ", " p => Filter.eventually (fun x => (p : _ → _) x) f
/-- info: ∀ᶠ' Filter.atTop, fun x ↦ x < 3 : Prop -/
#guard_msgs in #check ∀ᶠ' Filter.atTop, fun x => x < 3

def foobar (p : α → Prop) (f : Prop) := ∀ x, p x = f

notation +delab "∀ᶠᶠ " (...) " in " f ": "
  r1:(scoped p => Filter.eventually p f) ", " r2:(scoped p => foobar p r1) => r2

/-- info: ∀ᶠᶠ (x : ℕ) (y : ℕ) in Filter.atTop: x < y, x = y : Prop -/
#guard_msgs in #check ∀ᶠᶠ (x : Nat) (y) in Filter.atTop: x < y, x = y
/-- info: ∀ᶠᶠ (x : ℕ) in Filter.atTop: x < 3, x = 1 : Prop -/
#guard_msgs in #check ∀ᶠᶠ x in Filter.atTop: x < 3, x = 1
/-- info: ∀ᶠᶠ (x : ℕ) in Filter.atTop: x < 3, x = 1 : Prop -/
#guard_msgs in #check foobar (fun x ↦ Eq x 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)
/-- info: foobar (fun y ↦ y = 1) (∀ᶠ (x : ℕ) in Filter.atTop, x < 3) : Prop -/
#guard_msgs in #check foobar (fun y ↦ Eq y 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)

notation +delab "∃' " (...) ", " r:(scoped p => Exists p) => r
/-- info: ∃' (a : ℕ) (_ : a < 3), a < 3 : Prop -/
#guard_msgs in #check ∃' a < 3, a < 3
/-- info: ∃' (x : ℕ) (_ : x < 3), True : Prop -/
#guard_msgs in #check ∃' _ < 3, True
/-- info: ∃' (x : ℕ) (_ : x < 1) (x_1 : ℕ) (_ : x_1 < 2), x = 0 : Prop -/
#guard_msgs in #check ∃' (x < 1) (_ < 2), x = 0

def func (x : α) : α := x
notation +delab "func! " (...) ", " r:(scoped p => func p) => r
/-- info: (func! (x : ℕ → ℕ), x) fun x ↦ x * 2 : ℕ → ℕ -/
#guard_msgs in #check (func! (x : Nat → Nat), x) (· * 2)

structure MyUnit where
notation +delab "~{" (x"; "* => foldl (a b => (a, b)) MyUnit) "}~" => x
/-- info: ~{1; true; ~{2}~}~ : ((Type × ℕ) × Bool) × Type × ℕ -/
#guard_msgs in #check ~{1; true; ~{2}~}~
/-- info: ~{}~ : Type -/
#guard_msgs in #check ~{}~

structure MyUnit' where
instance : OfNat MyUnit' (nat_lit 0) := ⟨{}⟩
notation +delab "MyUnit'0" => (0 : MyUnit')
/-- info: MyUnit'0 : MyUnit' -/
#guard_msgs in #check (0 : MyUnit')
/-- info: 0 : ℕ -/
#guard_msgs in #check 0

notation +delab "%[" (x", "* => foldr (a b => a :: b) []) "]" => x
/-- info: %[1, 2, 3] : List ℕ -/
#guard_msgs in #check %[1, 2, 3]

def foo (a : Nat) (f : Nat → Nat) := a + f a
def bar (a b : Nat) := a * b
notation +delab "*[" x "] " (...) ", " v:(scoped c => bar x (foo x c)) => v
/-- info: *[1] (x : ℕ) (y : ℕ), x + y : ℕ -/
#guard_msgs in #check *[1] (x) (y), x + y
/-- info: bar 1 : ℕ → ℕ -/
#guard_msgs in #check bar 1

-- Checking that the `<|` macro is expanded when making matcher
def foo' (a : Nat) (f : Nat → Nat) := a + f a
def bar' (a b : Nat) := a * b
notation +delab "*'[" x "] " (...) ", " v:(scoped c => bar' x <| foo' x c) => v
/-- info: *'[1] (x : ℕ) (y : ℕ), x + y : ℕ -/
#guard_msgs in #check *'[1] (x) (y), x + y
/-- info: bar' 1 : ℕ → ℕ -/
#guard_msgs in #check bar' 1

-- Need to give type ascription to `p` so that `p x` elaborates when making matcher
notation +delab "MyPi " (...) ", " r:(scoped p => (x : _) → (p : _ → _) x) => r
/-- info: MyPi (x : ℕ) (y : ℕ), x < y : Prop -/
#guard_msgs in #check MyPi (x : Nat) (y : Nat), x < y

-- The notation parses fine, but the delaborator never succeeds, which is expected
def myId (x : α) := x
notation +delab "BAD " c "; " (x", "* => foldl (a b => b) c) " DAB" => myId x
/-- info: myId 3 : ℕ -/
#guard_msgs in #check BAD 1; 2, 3 DAB

section
variable (x : Nat)
local notation +delab "y" => x + 1
/-- info: y : ℕ -/
#guard_msgs in #check y
/-- info: y : ℕ -/
#guard_msgs in #check x + 1
end

section
variable (α : Type u) [Add α]
local notation +delab x " +α " y => (x + y : α)
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
error: Application type mismatch: The argument
  Nat.zero
has type
  ℕ
but is expected to have type
  String
in the application
  idStr Nat.zero
---
warning: Was not able to generate a pretty printer for this notation. If you do not expect it to be pretty printable, then you can use `macro` or `syntax` and `macro_rules` instead. If the notation expansion refers to section variables, be sure to do `local notation +delab`. Otherwise, you might be able to adjust the notation expansion to make it matchable; pretty printing relies on deriving an expression matcher from the expansion. (Use `set_option trace.notationDelab true` to get some debug information.)
-/
#guard_msgs in
notation +delab "error" => idStr Nat.zero

section
/--
warning: Was not able to generate a pretty printer for this notation. If you do not expect it to be
pretty printable, then you can use `macro` or `syntax` and `macro_rules` instead. If the notation
expansion refers to section variables, be sure to do `local notation +delab`. Otherwise, you might
be able to adjust the notation expansion to make it matchable; pretty printing relies on deriving an expression
matcher from the expansion. (Use `set_option trace.notationDelab true` to get some debug information.)
-/
#guard_msgs (warning, drop error) in local notation +delab "#" n => Fin.mk n (by decide)
end

section test_scoped

scoped[MyNotation] notation +delab "π" => (3 : Nat)

/-- error: Unknown identifier `π` -/
#guard_msgs in #check π

open scoped MyNotation

/-- info: π : ℕ -/
#guard_msgs in #check π

end test_scoped

/-!
Verifying that delaborator does not match the exact `Inhabited` instance.
Instead, it matches that it's an application of `Inhabited.default` whose first argument is `Nat`.
-/
/--
trace: [notationDelab] syntax declaration has name Test.termδNat
---
trace: [notationDelab] Generating matcher for pattern default
[notationDelab] Matcher creation succeeded; assembling delaborator
[notationDelab] matcher:
      matchApp✝ (matchApp✝ (matchExpr✝ (Expr.isConstOf✝ · `Inhabited.default)) (matchExpr✝ (Expr.isConstOf✝ · `Nat)))
          pure✝ >=>
        pure✝
[notationDelab] Creating delaborator for key Mathlib.NotationDelab.DelabKey.app (some `Inhabited.default) 2
-/
#guard_msgs in
set_option trace.notationDelab true in
notation +delab "δNat" => (default : Nat)

/-- info: δNat : ℕ -/
#guard_msgs in #check (default : Nat)
/-- info: δNat : ℕ -/
#guard_msgs in #check @default Nat (Inhabited.mk 5)


notation +delab "(" "ignorez " "SVP" ")" => Sort _
notation +delab "Objet " "mathématique " "supérieur" => Type _
notation +delab "Énoncé" => Prop
notation +delab "Objet " "mathématique" => Type
/-- info: 1 = 1 : Énoncé -/
#guard_msgs in #check 1 = 1
/-- info: Énoncé : Objet mathématique -/
#guard_msgs in #check Prop
/-- info: Nat : Objet mathématique -/
#guard_msgs in #check Nat
/-- info: Objet mathématique : Objet mathématique supérieur -/
#guard_msgs in #check Type
/-- info: PSum.{u, v} (α : (ignorez SVP)) (β : (ignorez SVP)) : (ignorez SVP) -/
#guard_msgs in #check PSum

end Test

/--
warning: syntax 'Mathlib.NotationDelab.notation3' has been deprecated: use `notation +delab` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
notation3 "deprecatedNotation3" => (0 : Nat)

/--
warning: macro 'Mathlib.Tactic.scopedNS' produces deprecated syntax 'Mathlib.NotationDelab.notation3': use `notation +delab` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
scoped[MyNotation] notation3 "deprecatedScopedNotation3" => (0 : Nat)
