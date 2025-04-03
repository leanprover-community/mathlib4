/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Mathport.Rename

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.

# Align statements for declarations from Batteries
-/

#align option.mem_def Option.mem_def
#align option.is_none_iff_eq_none Option.isNone_iff_eq_none
#align option.some_inj Option.some_inj
#align option.decidable_eq_none Option.decidable_eq_none
#align option.guard Option.guard
#align option.to_list Option.toList
#align option.rel Option.Rel
#align option.pbind Option.pbind
#align option.pmap Option.pmap
#align option.join Option.join

#align option.filter Option.filter
