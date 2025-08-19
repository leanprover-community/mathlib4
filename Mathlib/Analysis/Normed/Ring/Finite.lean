/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Analysis.Normed.Ring.Basic


/-!
# Finite order elements in normed rings.

A finite order element in a normed ring has norm 1.

The values of additive characters on finite cancellative monoids have norm 1.

-/

variable {α β : Type*}

section NormedRing
variable [NormedRing α] [NormMulClass α] [NormOneClass α] {a : α}

protected lemma IsOfFinOrder.norm_eq_one (ha : IsOfFinOrder a) : ‖a‖ = 1 :=
  ((normHom : α →*₀ ℝ).toMonoidHom.isOfFinOrder ha).eq_one <| norm_nonneg _

example [Monoid β] (φ : β →* α) {x : β} {k : ℕ+} (h : x ^ (k : ℕ) = 1) :
    ‖φ x‖ = 1 := (φ.isOfFinOrder <| isOfFinOrder_iff_pow_eq_one.2 ⟨_, k.2, h⟩).norm_eq_one

@[simp] lemma AddChar.norm_apply {G : Type*} [AddLeftCancelMonoid G] [Finite G] (ψ : AddChar G α)
    (x : G) : ‖ψ x‖ = 1 := (ψ.toMonoidHom.isOfFinOrder <| isOfFinOrder_of_finite _).norm_eq_one

end NormedRing
