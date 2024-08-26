/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Batteries.Tactic.Alias
import Mathlib.Init
/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

# Quot

Some induction principles tagged with `elab_as_elim`, since the attribute is missing in core.
-/

universe u v
variable {α : Sort u} {r : α → α → Prop} {motive : Quot r → Sort v}

@[inherit_doc Quot.rec, elab_as_elim] -- Porting note: adding `elab_as_elim`
protected abbrev Quot.recOn'
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (Quot.sound p) = f b) :
    motive q :=
 q.rec f h

@[deprecated (since := "2024-08-26")] alias Quot.recOnSubsingleton' := Quot.recOnSubsingleton

@[deprecated (since := "2024-08-26")]
theorem Quotient.mk'_eq_mk [s : Setoid α] : Quotient.mk' = Quotient.mk s := rfl
