/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Thomas Murrills
-/
import Lean
import Std.Tactic.OpenPrivate

/-!

# Additions to Lean.Meta.AppBuilder

We provide variants of `mkAppM` and `mkAppN` for customized behavior. Namely:

* `mkApp*Unifying`(`'`): Checks that argument types are defeq to the corresponding input types, and
does not set a new MCtx depth

* `mkAppMUnifyingWithNewMVars`(`'`): Unifies at the current MCtx depth as above, and does not fail
if newly-created implicit argument mvars are unassigned, instead returning them along with the
`Expr`. Useful if we want to delay the assignment of these metavariables.


-/


-/

