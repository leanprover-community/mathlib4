/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Basic
/-!
# The `nodup` predicate for multisets without duplicate elements.

TODO: This is currently extremely minimal,
containing only the definitions required to implement the `fin_cases` tactic.
Please update this module doc as changes are made,
eventually restoring the original mathlib3 module doc.
-/


namespace Multiset

open Function List

variable {α β γ : Type _} {r : α → α → Prop} {s t : Multiset α} {a : α}

/-- `nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1. -/
def Nodup (s : Multiset α) : Prop :=
  Quot.liftOn s List.Nodup fun _ _ p => propext p.nodup_iff
