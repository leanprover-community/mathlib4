/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Perm

namespace Multiset
open List

variable {α β γ : Type _} {r : α → α → Prop} {s t : Multiset α} {a : α}

/- Nodup -/

/-- `Nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1. -/
def Nodup (s : Multiset α) : Prop :=
Quot.liftOn s List.Nodup (λ _ _ p => propext p.nodup_iff)
