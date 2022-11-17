/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
import Mathlib.Util.WithWeakNamespace

/-! # `scoped[NS]` syntax

This is a replacement for the `localized` command in mathlib. It is similar to `scoped`,
but it scopes the syntax in the specified namespace instead of the current namespace.
-/

namespace Mathlib.Tactic
open Lean

/--
`scoped[NS]` is similar to the `scoped` modifier on attributes and notations,
but it scopes the syntax in the specified namespace instead of the current namespace.
```
scoped[Matrix] infixl:75 " ⬝ " => Matrix.mul
-- declares `⬝` as a notation for matrix multiplication
-- which is only accessible if you `open Matrix` or `open scoped Matrix`.

namespace Nat

scoped[Nat.Count] attribute [instance] CountSet.fintype
-- make the definition Nat.CountSet.fintype an instance,
-- but only if `Nat.Count` is open
```
-/
syntax (name := scopedNS) "scoped" "[" ident "] " command : command
macro_rules
  | `(scoped[$ns] notation $[$prec:precedence]? $[$n:namedName]? $[$prio:namedPrio]?
       $sym => $t) =>
    let ns := mkIdentFrom ns <| rootNamespace ++ ns.getId
    `(with_weak_namespace $ns
      scoped notation $[$prec:precedence]? $[$n:namedName]? $[$prio:namedPrio]? $sym => $t)
  | `(scoped[$ns] $mixfixKind:prefix $prec:precedence $[$n:namedName]? $[$prio:namedPrio]?
       $sym => $t) =>
    let ns := mkIdentFrom ns <| rootNamespace ++ ns.getId
    `(with_weak_namespace $ns
      scoped $mixfixKind $prec:precedence $[$n:namedName]? $[$prio:namedPrio]? $sym => $t)
  | `(scoped[$ns] attribute [$attr:attr] $ids*) =>
    let ns := mkIdentFrom ns <| rootNamespace ++ ns.getId
    `(with_weak_namespace $ns attribute [scoped $attr:attr] $ids*)
