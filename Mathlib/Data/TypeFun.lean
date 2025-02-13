/-
Copyright (c) 2024 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Mathlib.Data.TypeVec

/-!
# Uncurried Type Functions

Generally, type functions are written in a curried form, for example,
`Sum : Type u → Type v → Type (max u v)`.
In the developement of QPFs, though, we want to talk about `n`-ary type functions, for arbitrary
`n`, which is a bit painful to do with curried functions. Thus, we generally use uncurried functions
`TypeVec.{u} n → Type*` instead.

This files defines `TypeFun n` as an abbreviation for such uncurried type functions, and establishes
the canonical isomorphism between curried type functions `Type u → ... → Type u → Type v` and
uncurried type functions `TypeVec.{u} n → Type v`

## Main declarations:
* `TypeFun`: type of *uncurried* type functions (`TypeVec.{u} n → Type v`)
* `TypeFun.CurriedTypeFun n`: type of *curried* type functions (`Type u → ... → Type u → Type v`)
* `TypeFun.ofCurried`: conversion of a curried type function into uncurried
-/

universe u v

/-- The type of uncurried `n`-ary type functions, which take `n` arguments of type `Type u` and
return a `Type v` -/
@[nolint checkUnivs] -- The universes do occur separately in the body of the definition
abbrev TypeFun (n : Nat) : Type ((max u v) + 1) :=
  TypeVec.{u} n → Type v

namespace TypeFun
open TypeVec

/-- A curried type function of `n` arguments, i.e., `Type u → Type u → ... → Type v`.
This abbreviation should only be used to talk about such functions where `n` is arbitrary.
For concrete arities, always prefer the fully written form. -/
@[nolint checkUnivs] -- The universes do occur separately in the body of the definition
protected abbrev CurriedTypeFun : Nat → Type ((max u v) + 1)
  /- `CurriedTypeFun 0` can't be just `Type v`, because it's not the right universe.
  Regardless `0`-ary functions are a degenerate case we're not very interested in. -/
  | 0   => ULift.{(max u v) + 1} (Type v)
  | 1   => Type u → Type v
  | n+1 => Type u → TypeFun.CurriedTypeFun n

/-- Convert a curried type function `F : Type u → ... → Type u → Type v` into an uncurried type
function, such that `(ofCurried F) (Fin2.elim0 ::: α₁ ::: ... ::: αₙ) = F α₁ ... αₙ` -/
def ofCurried {n} (F : TypeFun.CurriedTypeFun n) : TypeFun n :=
  fun α => (go F) (fun i => α i.rev)
where
  /-- Convert a curried type function `F : Type u → ... → Type u → Type v` into an uncurried type
  function, *while also reversing the argument order*!
  That is, `(ofCurried.go F) (Fin2.elim0 ::: α₁ ::: ... ::: αₙ) = F αₙ ... α₁` -/
  go : {n : Nat} → TypeFun.CurriedTypeFun n → TypeFun n
  | 0,    F, _ => F.down
  | 1,    F, α => F (α .fz)
  | _+2,  F, α => go (F α.last) α.drop

/-- An example with `Sum`, to showcase the variable ordering is as expected. -/
example (α β : Type) : (ofCurried Sum) ((Fin2.elim0 ::: α) ::: β) = (α ⊕ β) := rfl

end TypeFun
