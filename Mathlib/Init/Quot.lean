/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
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

# Quot

Some induction principles tagged with `elab_as_elim`, since the attribute is missing in core.
-/

#align quotient.induction_on Quotient.inductionOn
#align quot.induction_on Quot.inductionOn

universe u v
variable {α : Sort u} {r : α → α → Prop} {motive : Quot r → Sort v}

@[inherit_doc Quot.rec, elab_as_elim] -- Porting note: adding `elab_as_elim`
protected abbrev Quot.recOn'
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (Quot.sound p) = f b) :
    motive q :=
 q.rec f h
#align quot.rec_on Quot.recOn'
-- expected token

/-- Version of `Quot.recOnSubsingleton` tagged with `elab_as_elim` -/
@[elab_as_elim] -- Porting note: this attribute is missing in core
protected abbrev Quot.recOnSubsingleton'
    [h : (a : α) → Subsingleton (motive (Quot.mk r a))]
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a)) :
    motive q := by
  induction q using Quot.rec
  apply f
  apply Subsingleton.elim
#align quot.rec_on_subsingleton Quot.recOnSubsingleton'

theorem Quotient.mk'_eq_mk [s : Setoid α] : Quotient.mk' = Quotient.mk s := rfl
