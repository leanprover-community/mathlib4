/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apahe 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.SpecificGroups.PushoutI
import Mathlib.GroupTheory.SpecificGroups.HNNExtension

variable {α G : Type*} [Group G] (r : FreeGroup α)

namespace OneRelator

def OneRelator (r : FreeGroup α) : Type _ :=
  FreeGroup α ⧸ Subgroup.normalClosure {r}

instance : Group (OneRelator r) := by
  delta OneRelator; infer_instance

variable {r}

def lift (f : α → G) (hf : FreeGroup.lift f r = 1) : OneRelator r →* G :=
  QuotientGroup.lift _ (FreeGroup.lift f)
    (show Subgroup.normalClosure {r} ≤ (FreeGroup.lift f).ker from
      Subgroup.normalClosure_le_normal (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hf))

def of (x : α) : OneRelator r := QuotientGroup.mk (FreeGroup.of x)

@[simp]
theorem lift_of (f : α → G) (hf : FreeGroup.lift f r = 1) (x : α) :
    lift f hf (of x) = f x := by
  rw [lift, of, QuotientGroup.lift_mk', FreeGroup.lift.of]

@[ext high]
theorem hom_ext {f g : OneRelator r →* G} (h : ∀ x, f (of x) = g (of x)) : f = g := by
  delta OneRelator
  ext
  exact h _

end OneRelator
