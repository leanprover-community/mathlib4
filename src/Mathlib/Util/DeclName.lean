/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean

/-!
Defines a macro that returns the name of the enclosing definition.

```
namespace Foo
def bar : Name := decl_name!

#eval Foo.bar -- `Foo.bar
```
-/

open Lean Elab Term

elab "decl_name%" : term => do
  let some declName ← getDeclName?
    | throwError "invalid `decl_name!` macro, it must be used in definitions"
  elabTerm (quote declName) none
