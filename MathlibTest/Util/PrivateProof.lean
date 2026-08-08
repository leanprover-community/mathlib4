module

import Mathlib.Util.PrivateProof

public section

private def foo := 3
def fooPub := 3

private theorem fooThm : 1 = 1 := (rfl)

@[expose] def FEq (_ : 1 = 1) := Bool

-- Can't use private `fooThm` in public type of `f` normally
/--
error: Unknown identifier `fooThm`

Note: A private declaration `fooThm` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
def f (_ : FEq fooThm) : Bool := true

def f' (_ : FEq (private fooThm)) : Bool := true

@[expose] def F {α} (_ : α) := Bool

-- Works when we have solvable mvars:
def fα (_ : F (private fooThm)) : Bool := true

/--
error: `private` can only wrap proofs; the expected type of `foo` is not a `Prop`.
  Nat : Type
---
error: Unknown constant `_private.MathlibTest.Util.PrivateProof.0.foo`

Note: A private declaration `foo` (from the current module) exists but would need to be public to access here.
---
error: (kernel) declaration has metavariables 'fα''
-/
#guard_msgs in
def fα' (_ : F (private foo)) : Bool := true

/--
error: `private` can only wrap proofs; the expected type of `fooPub` is not a `Prop`.
  Nat : Type
-/
#guard_msgs in
def fαPub' (_ : F (private fooPub)) : Bool := true

-- Communicate that `private` doesn't work, but also continue elaborating, as shown by the
-- type mismatch error
/--
error: `private` can only wrap proofs; the expected type is not a `Prop`.
  Bool : Type
---
error: Unknown identifier `foo`

Note: A private declaration `foo` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
def fα'' (_ : F (α := Bool) (private foo)) : Bool := true

/--
error: `private` can only wrap proofs; the expected type is not a `Prop`.
  Bool : Type
---
error: Application type mismatch: The argument
  fooPub
has type
  Nat
but is expected to have type
  Bool
in the application
  F fooPub
-/
#guard_msgs in
def fαPub'' (_ : F (α := Bool) (private fooPub)) : Bool := true

set_option backward.privateInPublic true in
/--
@ +1:18...25
warning: `private` is unnecessary, since `backward.privateInPublic` is `true`.
-/
#guard_msgs (positions := true) in
def aPriv (_ : F (private fooPub)) : Bool := true

section implicitLambda

set_option linter.defProp false

-- implicit lambdas are inserted as usual
@[expose] def fImplicit : {_ : Nat} → 1 = 1 := private fooThm

-- and not accidentally re-inserted when we disable them
-- note: 'declaration has metavariables' occurs even with a normal `by exact @fooThm`
/--
error: Type mismatch
  fooThm
has type
  1 = 1
but is expected to have type
  ∀ {x : Nat}, 1 = 1
---
error: (kernel) declaration has metavariables 'fImplicit''
-/
#guard_msgs in
@[expose] def fImplicit' : {_ : Nat} → 1 = 1 := @(private fooThm)

end implicitLambda

end

/--
@ +1:18...25
warning: `private` is unnecessary, since private declarations are already usable.
-/
#guard_msgs (positions := true) in
def bPriv (_ : F (private foo)) : Bool := true
