/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Support
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Support of a function

In this file we define `Function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `Function.mulSupport f = {x | f x ≠ 1}`.
-/


open Set

open BigOperators

namespace Function

variable {α β A B M N P R S G M₀ G₀ : Type*} {ι : Sort*}

section One

variable [One M] [One N] [One P]

@[to_additive]
theorem mulSupport_sup [SemilatticeSup M] (f g : α → M) :
    (mulSupport fun x => f x ⊔ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊔ ·) sup_idem f g
#align function.mul_support_sup Function.mulSupport_sup
#align function.support_sup Function.support_sup

@[to_additive]
theorem mulSupport_inf [SemilatticeInf M] (f g : α → M) :
    (mulSupport fun x => f x ⊓ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊓ ·) inf_idem f g
#align function.mul_support_inf Function.mulSupport_inf
#align function.support_inf Function.support_inf

@[to_additive]
theorem mulSupport_max [LinearOrder M] (f g : α → M) :
    (mulSupport fun x => max (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_sup f g
#align function.mul_support_max Function.mulSupport_max
#align function.support_max Function.support_max

@[to_additive]
theorem mulSupport_min [LinearOrder M] (f g : α → M) :
    (mulSupport fun x => min (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_inf f g
#align function.mul_support_min Function.mulSupport_min
#align function.support_min Function.support_min

@[to_additive]
theorem mulSupport_iSup [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (mulSupport fun x => ⨆ i, f i x) ⊆ ⋃ i, mulSupport (f i) := by
  rw [mulSupport_subset_iff']
  simp only [mem_iUnion, not_exists, nmem_mulSupport]
  intro x hx
  simp only [hx, ciSup_const]
#align function.mul_support_supr Function.mulSupport_iSup
#align function.support_supr Function.support_iSup

@[to_additive]
theorem mulSupport_iInf [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (mulSupport fun x => ⨅ i, f i x) ⊆ ⋃ i, mulSupport (f i) :=
  @mulSupport_iSup _ Mᵒᵈ ι ⟨(1 : M)⟩ _ _ f
#align function.mul_support_infi Function.mulSupport_iInf
#align function.support_infi Function.support_iInf
