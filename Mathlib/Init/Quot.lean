/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Mathport.Rename

/-!
# Quot

Some induction principles tagged with `elab_as_elim`, since the attribute is missing in core.
-/

set_option autoImplicit true

#align quotient.induction_on Quotient.inductionOn
#align quot.induction_on Quot.inductionOn

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
