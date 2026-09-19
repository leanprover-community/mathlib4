module

import Mathlib.Util.PrivateProof
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Order.Lattice
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Lattice.Fold

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
  ℕ : Type

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
  ℕ : Type

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
  ℕ
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
  ∀ {x : ℕ}, 1 = 1
-/
#guard_msgs in
@[expose] def fImplicit' : {_ : Nat} → 1 = 1 := @(private fooThm)

-- and, we do not accidentally disable insertion of implicit arguments just because we disabled
-- implicit lambda.
private theorem implicitThm {n : Nat} : n = n := rfl

def gImplicit (_ : FEq (private implicitThm)) : Bool := true

end implicitLambda

section synthesisTiming

private theorem usePriv : Nat → 1 = 1 := fun _ => rfl

-- Make sure nested non-prop `by`s can use the private scope
-- This fails under `withSynthesize (postpone := .yes)`
def fNestedBy (_ : FEq (private usePriv (by exact foo))) : Bool := true

-- Example from `Mathlib.Combinatorics.SetFamily.AhlswedeZhang`
-- TODO: minimize
variable {α} [SemilatticeSup α] {s t : Finset α} {a : α}

private theorem sup_aux [DecidableLE α] : a ∈ lowerClosure s → {b ∈ s | a ≤ b}.Nonempty :=
  fun ⟨b, hb, hab⟩ ↦ ⟨b, Finset.mem_filter.2 ⟨hb, hab⟩⟩

-- Make sure synthetic mvars can be postponed
-- This fails under `withSynthesize (postpone := .no)`
@[expose] def truncatedSup [DecidableLE α] [OrderTop α] (s : Finset α) (a : α) : α :=
  if h : a ∈ lowerClosure s then {b ∈ s | a ≤ b}.sup' (private sup_aux h) id else ⊤

end synthesisTiming

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

set_option linter.privateProof.warnIfUnnecessary false in
def fLocalSilenced (h : 1 = 1) : FEq (private h) := true

set_option backward.privateInPublic true in
/--
@ +1:18...25
warning: `private` is unnecessary, since `backward.privateInPublic` is `true`.
-/
#guard_msgs (positions := true) in
def aPriv (_ : F (private fooThm)) : Bool := true

set_option backward.privateInPublic true in
/--
@ +1:28...35
warning: `private` is unnecessary, since `backward.privateInPublic` is `true`.
---
@ +1:36...42
error: `private` can only wrap proofs, but the expected type of `fooPub` is not a `Prop`.
  ℕ : Type

Use `private_decl%` to wrap a non-proof term in an auxiliary definition.
-/
#guard_msgs (positions := true) in
def aPrivBothErrors (_ : F (private fooPub)) : Bool := true

set_option backward.privateInPublic true in
set_option linter.privateProof.warnIfUnnecessary false in
def aPrivSilenced (_ : F (private fooThm)) : Bool := true

end

/--
@ +1:18...25
warning: `private` is unnecessary, since private declarations are already usable.
-/
#guard_msgs (positions := true) in
def bPriv (_ : F (private fooThm)) : Bool := true

set_option linter.privateProof.warnIfUnnecessary false in
def bPrivSilenced (_ : F (private fooThm)) : Bool := true
