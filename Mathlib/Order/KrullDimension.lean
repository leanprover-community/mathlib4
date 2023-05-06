/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangmin Li
-/

import Mathlib.Order.Monotone.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Order.WithBot
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Equiv.Fin

/-!
# Krull dimension of a preordered set

If `α` is a preordered set, then `krull_dim α` is defined to be `sup {n | a₀ < a₁ < ... < aₙ}`.
In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to
be positive infinity.

For `a : α`, its height is defined to be the krull dimension of the subset `(-∞, a]` while its
coheight is defined to be the krull dimension of `[a, +∞)`.
-/

variable (α : Type _) [Preorder α]

/--
For a preordered set `(α, <)`, a strict series of `α` of length `n` is a strictly monotonic function
`fin (n + 1) → α`, i.e. `a₀ < a₁ < ... < aₙ` with `aᵢ : α`.
-/
structure StrictSeries where
/-- the number of inequalities in the series -/
length : ℕ
/-- the underlying function of a strict series -/
toFun : Fin (maxIndex + 1) → α
/-- the underlying function should be strictly monotonic -/
StrictMono : StrictMono toFun

namespace StrictSeries

instance : CoeFun (StrictSeries α) (fun x ↦ Fin (x.maxIndex + 1) → α) :=
{ coe := StrictSeries.toFun }

instance : Preorder (StrictSeries α) :=
Preorder.lift StrictSeries.maxIndex

variable {α}

lemma le_def (x y : StrictSeries α) : x ≤ y ↔ x.maxIndex ≤ y.maxIndex :=
Iff.rfl

lemma lt_def (x y : StrictSeries α) : x < y ↔ x.maxIndex < y.maxIndex :=
Iff.rfl

/--
In a preordered set `α`, each term of `α` gives a strict series with the right most index to be 0.
-/
@[simps!] def singleton (a : α) : StrictSeries α :=
{ maxIndex := 0
  toFun := fun _ ↦ a
  StrictMono := fun _ _ h ↦ (ne_of_lt h $ @Subsingleton.elim _ subsingleton_fin_one _ _).elim }

instance [IsEmpty α] : IsEmpty (StrictSeries α) :=
{ false := fun x ↦ IsEmpty.false (x 0) }

instance [Inhabited α] : Inhabited (StrictSeries α) :=
{ default := singleton default }

instance [Nonempty α] : Nonempty (StrictSeries α) :=
Nonempty.map singleton inferInstance

lemma top_len_unique [OrderTop (StrictSeries α)] (p : StrictSeries α) (hp : IsTop p) :
  p.maxIndex = (⊤ : StrictSeries α).maxIndex :=
le_antisymm (@le_top (StrictSeries α) _ _ _) (hp ⊤)

lemma top_len_unique' (H1 H2 : OrderTop (StrictSeries α)) : H1.top.maxIndex = H2.top.maxIndex :=
le_antisymm (H2.le_top H1.top) (H1.le_top H2.top)

end StrictSeries

/--
Krull dimension of a preordered set `α` is the supremum of the right most index of all strict
series of `α`. If there is no strict series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull dimension
is defined to be negative infinity; if the length of `a₀ < a₁ < ... < aₙ` is unbounded, its Krull
dimension is defined to be positive infinity.
-/
noncomputable def krullDim : WithBot (WithTop ℕ) :=
⨆ (p : StrictSeries α), p.maxIndex

/--
Height of an element `a` of a preordered set `α` is the Krull dimension of the subset `(-∞, a]`
-/
noncomputable def height (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Iic a)

/--
Coheight of an element `a` of a pre-ordered set `α` is the Krull dimension of the subset `[a, +∞)`
-/
noncomputable def coheight (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Ici a)
