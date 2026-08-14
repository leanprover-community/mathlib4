module

public import Mathlib.Tactic.Linter.PrivateProof
public import Mathlib.Util.PrivateProof

/-!
# Tests for the `privateProof` linter

The linter only looks at commands elaborated with `backward.privateInPublic` set to `true`, so
every test below sets it. The private declarations themselves also need it, since otherwise they
are not exported at all and cannot be referenced from an exporting environment regardless.
-/

public section

set_option linter.privateProof true
set_option backward.privateInPublic.warn false

structure Foo where
  n : Nat
  h : n = 0

class MyPreorder (α : Type) where
  le : α → α → Prop
  le_refl : ∀ a, le a a

set_option backward.privateInPublic true in
private theorem eq0 : (0 : Nat) = 0 := rfl

set_option backward.privateInPublic true in
private theorem eq0' : ∀ n : Nat, n = 0 → n = 0 := fun _ h => h

set_option backward.privateInPublic true in
private theorem fooLeRefl (a : Foo) : a.n ≤ a.n := Nat.le_refl _

@[expose] def FEq (_ : (0 : Nat) = 0) := Bool

/-!
## Positive tests
-/

-- A bare constant proof in the value of an exposed definition: nothing in the infotree starts
-- where `eq0` does, and the preceding token is `,`, so no parentheses are needed.
/--
info: This proof term requires `backward.privateInPublic`; wrap it instead:
  [apply] private eq0
---
info: With the proof terms of this command wrapped in `private`, this `set_option` should be unnecessary; delete it:
  [apply] (delete)
-/
#guard_msgs in
set_option backward.privateInPublic true in
@[expose] def val1 : Foo := ⟨0, eq0⟩

-- An application: the whole application is wrapped, not just its head (which is itself a proof,
-- of an implication).
/--
info: This proof term requires `backward.privateInPublic`; wrap it instead:
  [apply] private eq0' 0 eq0
---
info: With the proof terms of this command wrapped in `private`, this `set_option` should be unnecessary; delete it:
  [apply] (delete)
-/
#guard_msgs in
set_option backward.privateInPublic true in
@[expose] def val2 : Foo := ⟨0, eq0' 0 eq0⟩

-- A function argument: parentheses are required, since the preceding token does not open a
-- position accepting a term of precedence 0.
/--
info: This proof term requires `backward.privateInPublic`; wrap it instead:
  [apply] (private eq0)
---
info: With the proof terms of this command wrapped in `private`, this `set_option` should be unnecessary; delete it:
  [apply] (delete)
-/
#guard_msgs in
set_option backward.privateInPublic true in
@[expose] def val3 : Foo := Foo.mk 0 eq0

-- A proof appearing in a *type*, which is always public.
/--
info: This proof term requires `backward.privateInPublic`; wrap it instead:
  [apply] (private eq0)
---
info: With the proof terms of this command wrapped in `private`, this `set_option` should be unnecessary; delete it:
  [apply] (delete)
-/
#guard_msgs in
set_option backward.privateInPublic true in
def typ1 (_ : FEq eq0) : Bool := true

-- A structure instance field, which is the shape almost all of the Mathlib uses take. The
-- suggestion is deliberately unparenthesized: `field := private ..` is structure instance syntax
-- with its own (compatible) meaning, and we are happy to take advantage of it.
/--
info: This proof term requires `backward.privateInPublic`; wrap it instead:
  [apply] private fooLeRefl
---
info: With the proof terms of this command wrapped in `private`, this `set_option` should be unnecessary; delete it:
  [apply] (delete)
-/
#guard_msgs in
set_option backward.privateInPublic true in
instance inst1 : MyPreorder Foo where
  le a b := a.n ≤ b.n
  le_refl := fooLeRefl

/-!
## Deleting the `set_option`s

Once every reference in a command can be wrapped, the `set_option`s which enable
`backward.privateInPublic` for it should no longer be needed, and each is suggested for deletion in
its own message. The suggested range runs from the `set_option` keyword through the whitespace
following the `in`, so that applying it removes the whole line.
-/

/--
info: This proof term requires `backward.privateInPublic`; wrap it instead:
  [apply] private eq0
---
info: With the proof terms of this command wrapped in `private`, this `set_option` should be unnecessary; delete it:
  [apply] (delete)
---
info: With the proof terms of this command wrapped in `private`, this `set_option` should be unnecessary; delete it:
  [apply] (delete)
-/
#guard_msgs in
set_option backward.privateInPublic.warn false in
set_option backward.privateInPublic true in
@[expose] def stacked : Foo := ⟨0, eq0⟩

-- Unrelated `set_option`s in the chain are left alone: there are three here, but only two
-- deletions are suggested.
/--
info: This proof term requires `backward.privateInPublic`; wrap it instead:
  [apply] private eq0
---
info: With the proof terms of this command wrapped in `private`, this `set_option` should be unnecessary; delete it:
  [apply] (delete)
---
info: With the proof terms of this command wrapped in `private`, this `set_option` should be unnecessary; delete it:
  [apply] (delete)
-/
#guard_msgs in
set_option linter.unusedVariables false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[expose] def stacked' : Foo := ⟨0, eq0⟩

/-!
## Negative tests
-/

-- `by` blocks with a `Prop` goal leave the exporting scope and are abstracted into auxiliary
-- theorems, so they need no `private` — and hence the `set_option` is not needed at all here.
/--
info: With the proof terms of this command wrapped in `private`, this `set_option` should be unnecessary; delete it:
  [apply] (delete)
-/
#guard_msgs in
set_option backward.privateInPublic true in
@[expose] def val4 : Foo := ⟨0, by exact eq0' 0 eq0⟩

-- Theorem values are not exported, and so are elaborated in a non-exporting environment.
#guard_msgs in
set_option backward.privateInPublic true in
theorem thm1 : (0 : Nat) = 0 := eq0' 0 eq0

-- Values which are not exposed are likewise elaborated in a non-exporting environment.
#guard_msgs in
set_option backward.privateInPublic true in
def val5 : Foo := ⟨0, eq0' 0 eq0⟩

-- Without the option there is nothing to report.
#guard_msgs in
@[expose] def val6 : Foo := ⟨0, private eq0' 0 eq0⟩

/-!
## The linter does not fire once `private` is present

The `private` elaborator warns that it is unnecessary while `backward.privateInPublic` is still
set, but the linter itself must stay quiet: these are exactly the declarations a sweep has already
fixed.
-/

/--
warning: `private` is unnecessary, since `backward.privateInPublic` is `true`.
-/
#guard_msgs in
set_option backward.privateInPublic true in
@[expose] def fixed1 : Foo := ⟨0, private eq0⟩

/--
warning: `private` is unnecessary, since `backward.privateInPublic` is `true`.
-/
#guard_msgs in
set_option backward.privateInPublic true in
@[expose] def fixed2 : Foo := ⟨0, private eq0' 0 eq0⟩

/--
warning: `private` is unnecessary, since `backward.privateInPublic` is `true`.
-/
#guard_msgs in
set_option backward.privateInPublic true in
@[expose] def fixed3 : Foo := Foo.mk 0 (private eq0)

/--
warning: `private` is unnecessary, since `backward.privateInPublic` is `true`.
-/
#guard_msgs in
set_option backward.privateInPublic true in
def fixed4 (_ : FEq (private eq0)) : Bool := true

-- The structure instance form expands to `private_decl%`, which does not consult the option, so
-- there is no warning here either.
#guard_msgs in
set_option backward.privateInPublic true in
instance fixed5 : MyPreorder Foo where
  le a b := a.n ≤ b.n
  le_refl := private fooLeRefl

-- And with the option gone, the fixed declarations elaborate silently.
#guard_msgs in
@[expose] def fixed6 : Foo := ⟨0, private eq0' 0 eq0⟩

#guard_msgs in
instance fixed7 : MyPreorder Foo where
  le a b := a.n ≤ b.n
  le_refl := private fooLeRefl
