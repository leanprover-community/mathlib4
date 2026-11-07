/-
Copyright (c) 2026 Stewart Thomas-William Pawley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stewart Thomas-William Pawley
-/
module

public import Mathlib.Order.Nucleus

/-!
# Nuclei on a Boolean algebra are closed

On a Boolean algebra, every nucleus `n` is a *closed* nucleus: it is determined by its value at
`⊥`, via `n a = a ⊔ n ⊥`. Equivalently, `n` is the closure operator `a ↦ a ⊔ d` for the fixed
element `d = n ⊥`. This is the pointwise algebraic content of the classical fact that the
assembly (frame of nuclei) `N(L)` is Boolean iff `L` is (Beazer–Macnab; Simmons; see also
Johnstone, *Stone Spaces*, II.2).

`Mathlib.Order.Nucleus` already provides the frame/Heyting structure of `Nucleus X`, the
closure-operator view, and the pointwise `le_apply`/`idempotent`/`map_inf` API; this file adds the
Boolean specialization, which those results do not contain.

## Main statements

* `Nucleus.apply_eq_sup_apply_bot` : `n a = a ⊔ n ⊥` for `n : Nucleus X` and `[BooleanAlgebra X]`.
* `Nucleus.isClosed_of_booleanAlgebra` : the same fact packaged as "`n` equals the closure by
  `n ⊥`", i.e. `⇑n = fun a => a ⊔ n ⊥`.

## References

* R. Beazer and D. S. Macnab, *Modal extensions of Heyting algebras*.
* H. Simmons, *A framework for topology*, in Logic Colloquium '77.
* P. T. Johnstone, *Stone Spaces*, CUP (1982), II.2.
-/

@[expose] public section

namespace Nucleus

variable {X : Type*} [BooleanAlgebra X] (n : Nucleus X)

/-- On a Boolean algebra, a nucleus is **closed**: it is determined by its value at `⊥` via
`n a = a ⊔ n ⊥`. The forward inequality uses complementation and the meet-preservation of a
nucleus (`n a ⊓ aᶜ ≤ n aᶜ ⊓ n a = n (aᶜ ⊓ a) = n ⊥`); the reverse is inflationarity together with
monotonicity applied to `⊥ ≤ a`. -/
theorem apply_eq_sup_apply_bot (a : X) : n a = a ⊔ n ⊥ := by
  refine le_antisymm ?_ ?_
  · calc
      n a = n a ⊓ (a ⊔ aᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
      _ = n a ⊓ a ⊔ n a ⊓ aᶜ := by rw [inf_sup_left]
      _ ≤ a ⊔ n ⊥ := by
        refine sup_le_sup inf_le_right ?_
        calc
          n a ⊓ aᶜ ≤ n a ⊓ n aᶜ := inf_le_inf_left _ (n.le_apply)
          _ = n (a ⊓ aᶜ) := by rw [map_inf]
          _ = n ⊥ := by rw [inf_compl_eq_bot]
  · exact sup_le n.le_apply (n.monotone bot_le)

/-- On a Boolean algebra, a nucleus coincides with the closure operator `a ↦ a ⊔ n ⊥`. This is the
"every nucleus is closed" statement in point-free form. -/
theorem isClosed_of_booleanAlgebra : ⇑n = fun a => a ⊔ n ⊥ :=
  funext n.apply_eq_sup_apply_bot

/-- Two nuclei on a Boolean algebra are equal as soon as they agree at `⊥` — a Boolean nucleus is
determined by its single "required" element `n ⊥`. -/
theorem eq_of_apply_bot_eq {m n : Nucleus X} (h : m ⊥ = n ⊥) : m = n :=
  DFunLike.ext _ _ fun a => by
    rw [m.apply_eq_sup_apply_bot, n.apply_eq_sup_apply_bot, h]

end Nucleus
