/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Scott Morrison
-/
import Mathlib.Data.Equiv.Basic

/-!

# Functors can be applied to `equiv`s.

```
def functor.map_equiv (f : Type u → Type v) [functor f] [is_lawful_functor f] :
  α ≃ β → f α ≃ f β
```

-/

open equiv

namespace Functor

variable (f : Type u → Type v) [Functor f] [LawfulFunctor f]

-- this is in control.basic in Lean 3
theorem map_map (m : α → β) (g : β → γ) (x : f α) :
  g <$> (m <$> x) = (g ∘ m) <$> x :=
(comp_map _ _ _).symm

/-- Apply a functor to an `equiv`. -/
def map_equiv (h : α ≃ β) : f α ≃ f β where
  to_fun    := map h
  inv_fun   := map h.symm
  left_inv x := by simp [map_map]
  right_inv x := by simp [map_map]

@[simp]
lemma map_equiv_apply (h : α ≃ β) (x : f α) :
  (map_equiv f h : f α ≃ f β) x = map h x := rfl

@[simp]
lemma map_equiv_symm_apply (h : α ≃ β) (y : f β) :
  (map_equiv f h : f α ≃ f β).symm y = map h.symm y := rfl

end Functor
