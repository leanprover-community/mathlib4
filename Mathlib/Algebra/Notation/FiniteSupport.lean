/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.FiniteSupport.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive

/-!
# Finiteness of support
-/

public section

assert_not_exists Monoid

namespace Function
variable {α β γ : Type*} [One γ]

@[to_additive (attr := simp)]
lemma mulSupport_along_fiber_finite_of_finite (f : α × β → γ) (a : α) (h : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun b ↦ f (a, b) :=
  (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)

end Function
