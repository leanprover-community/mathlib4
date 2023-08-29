/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Scott Morrison
-/

import Mathlib.Control.Basic
import Mathlib.Logic.Equiv.Defs

/-!

# Functors can be applied to `Equiv`s.

```
def Functor.mapEquiv (f : Type u → Type v) [functor f] [LawfulFunctor f] :
  α ≃ β → f α ≃ f β
```

-/

set_option autoImplicit true

open Equiv

namespace Functor

variable (f : Type u → Type v) [Functor f] [LawfulFunctor f]

/-- Apply a functor to an `Equiv`. -/
def map_equiv (h : α ≃ β) : f α ≃ f β where
  toFun    := map h
  invFun   := map h.symm
  left_inv x := by simp [map_map]
                   -- 🎉 no goals
  right_inv x := by simp [map_map]
                    -- 🎉 no goals

@[simp]
lemma map_equiv_apply (h : α ≃ β) (x : f α) :
  (map_equiv f h : f α ≃ f β) x = map h x := rfl

@[simp]
lemma map_equiv_symm_apply (h : α ≃ β) (y : f β) :
  (map_equiv f h : f α ≃ f β).symm y = map h.symm y := rfl

end Functor
