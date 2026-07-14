/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmad Ali Parr
-/
import Mathlib.GroupTheory.GroupAction.DomAct.Basic
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Invariant functions under `DomMulAct`

A function `f : α → β` is invariant under the `DomMulAct` action if and only if
it is constant on each orbit of the underlying `MulAction` of `M` on `α`.

## Main results

- `DomMulAct.isFixedPt_iff_constOn_orbit`: `f` is a fixed point of `c ∈ Mᵈᵐᵃ` iff
  `f` is constant on the orbit of `mk.symm c`.
- `DomMulAct.smul_eq_iff_constOn_orbits`: `f` is invariant under all of `Mᵈᵐᵃ` iff
  `f` is constant on every orbit of the `M`-action on `α`.
- `DomMulAct.eq_const_of_pretransitive`: if the `M`-action on `α` is pretransitive,
  every `Mᵈᵐᵃ`-invariant function `f : α → β` is constant.
-/

namespace DomMulAct

variable {M α β : Type*} [Monoid M] [MulAction M α]

open MulAction

/-- `f` is fixed by `c : Mᵈᵐᵃ` iff `f` is constant on the orbit of `mk.symm c` in `α`. -/
theorem isFixedPt_smul_iff_constOn_orbit (c : Mᵈᵐᵃ) (f : α → β) :
    c • f = f ↔ ∀ a : α, f ((mk.symm c) • a) = f a := by
  simp [funext_iff, smul_apply]

/-- `f : α → β` is invariant under all of `Mᵈᵐᵃ` iff it is constant on every `M`-orbit. -/
theorem smul_eq_iff_constOn_orbits (f : α → β) :
    (∀ c : Mᵈᵐᵃ, c • f = f) ↔ ∀ (m : M) (a : α), f (m • a) = f a := by
  simp [funext_iff, smul_apply]
  constructor
  · intro h m a
    have := h (mk m) a
    simpa using this
  · intro h c a
    exact h (mk.symm c) a

/-- On a pretransitive action, every `Mᵈᵐᵃ`-invariant function is constant. -/
theorem eq_const_of_pretransitive [IsPretransitive M α] [Nonempty α]
    {f : α → β} (hf : ∀ c : Mᵈᵐᵃ, c • f = f) : ∀ a b : α, f a = f b := by
  intro a b
  rw [smul_eq_iff_constOn_orbits] at hf
  obtain ⟨m, rfl⟩ := (IsPretransitive.exists_smul_eq a b)
  exact (hf m a).symm

end DomMulAct
