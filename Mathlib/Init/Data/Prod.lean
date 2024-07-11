/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Util.CompileInductive

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.

### alignments from lean 3 `init.data.prod`
-/

compile_inductive% Prod
