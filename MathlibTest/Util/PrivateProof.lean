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
error: `private` can only wrap proofs, but the expected type of `foo` is not a `Prop`.
  Nat : Type

Use `private_decl%` to wrap a non-proof term in an auxiliary definition.
---
error: Unknown constant `_private.MathlibTest.Util.PrivateProof.0.foo`

Note: A private declaration `foo` (from the current module) exists but would need to be public to access here.
---
error: (kernel) declaration has metavariables 'fα''
-/
#guard_msgs in
def fα' (_ : F (private foo)) : Bool := true

/--
error: `private` can only wrap proofs, but the expected type of `fooPub` is not a `Prop`.
  Nat : Type

Use `private_decl%` to wrap a non-proof term in an auxiliary definition.
-/
#guard_msgs in
def fαPub' (_ : F (private fooPub)) : Bool := true

-- Communicate that `private` doesn't work, but also continue elaborating, as shown by the
-- type mismatch error
/--
error: `private` can only wrap proofs, but the expected type is not a `Prop`.
  Bool : Type

Use `private_decl%` to wrap a non-proof term in an auxiliary definition.
---
error: Unknown identifier `foo`

Note: A private declaration `foo` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
def fα'' (_ : F (α := Bool) (private foo)) : Bool := true

/--
error: `private` can only wrap proofs, but the expected type is not a `Prop`.
  Bool : Type

Use `private_decl%` to wrap a non-proof term in an auxiliary definition.
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

section implicitLambda

set_option linter.defProp false

-- implicit lambdas are inserted as usual
@[expose] def fImplicit : {_ : Nat} → 1 = 1 := private fooThm

-- and not accidentally re-inserted when we disable them
/--
error: Type mismatch
  fooThm
has type
  1 = 1
but is expected to have type
  ∀ {x : Nat}, 1 = 1
-/
#guard_msgs in
@[expose] def fImplicit' : {_ : Nat} → 1 = 1 := @(private fooThm)

-- and, we do not accidentally disable insertion of implicit arguments just because we disabled
-- implicit lambda.
private theorem implicitThm {n : Nat} : n = n := rfl

def gImplicit (_ : FEq (private implicitThm)) : Bool := true

end implicitLambda

-- unlike `by exact`, `private` ignores `backward.proofsInPublic`
set_option backward.proofsInPublic true in
def fProofsInPublic (_ : FEq (private fooThm)) : Bool := true

-- a local hypothesis needs no auxiliary theorem
/--
@ +1:30...37
warning: `private` is unnecessary, since the resulting expression is just a free variable:
  h : 1 = 1
-/
#guard_msgs (positions := true) in
def fLocal (h : 1 = 1) : FEq (private h) := true

-- Synthetic metavariables created while elaborating the term (here, a nested `by`) are synthesized
-- before we abstract, so that the proof ends up *inside* the auxiliary theorem. Otherwise the
-- pending metavariable is abstracted into a parameter and the auxiliary theorem would instead get
-- type `2 = 2 → 2 = 2`. (Note `2 = 2` is used so as not to hit the `mkAuxLemma` cache populated by
-- other aux lemmas in this file.)
private theorem barThm : 2 = 2 := rfl

@[expose] def FEq2 (_ : 2 = 2) := Bool

def fNested (_ : FEq2 (private (id (by exact barThm)))) : Bool := true

-- Ensure we have `fNested : ∀ (_ : FEq2 <constant>), _` and not e.g.
-- `fNested : ∀ (_ : FEq2 (<constant> args), _`.
-- (We use meta code in case e.g. `#check fNested._proof_1` is not stable.)
open Lean in
run_cmd do
  let .defnInfo { type .. } ← getConstInfo ``fNested | throwError "not a def"
  let_expr FEq2 auxThm := type.bindingDomain! | throwError "Wrong shape!{indentD type}"
  unless auxThm.isConst do throwError "Expected constant; got{indentD auxThm}"

set_option backward.privateInPublic true in
/--
@ +1:18...25
warning: `private` is unnecessary, since `backward.privateInPublic` is `true`.
-/
#guard_msgs (positions := true) in
def aPriv (_ : F (private fooPub)) : Bool := true

end

/--
@ +1:18...25
warning: `private` is unnecessary, since private declarations are already usable.
-/
#guard_msgs (positions := true) in
def bPriv (_ : F (private foo)) : Bool := true
