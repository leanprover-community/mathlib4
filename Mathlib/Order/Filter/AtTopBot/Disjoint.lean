/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Set.Disjoint

/-!
# Disjointness of `Filter.atTop` and `Filter.atBot`
-/

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

@[to_dual disjoint_atTop_principal_Iio]
theorem disjoint_atBot_principal_Ioi [Preorder α] (x : α) : Disjoint atBot (𝓟 (Ioi x)) :=
  disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl) (Iic_mem_atBot x) (mem_principal_self _)

@[to_dual disjoint_atBot_principal_Ici]
theorem disjoint_atTop_principal_Iic [Preorder α] [NoTopOrder α] (x : α) :
    Disjoint atTop (𝓟 (Iic x)) :=
  disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl).symm (Ioi_mem_atTop x)
    (mem_principal_self _)

@[to_dual disjoint_pure_atBot]
theorem disjoint_pure_atTop [Preorder α] [NoTopOrder α] (x : α) : Disjoint (pure x) atTop :=
  Disjoint.symm <| (disjoint_atTop_principal_Iic x).mono_right <| le_principal_iff.2 <|
    mem_pure.2 self_mem_Iic

@[to_dual disjoint_atTop_atBot]
theorem disjoint_atBot_atTop [PartialOrder α] [Nontrivial α] :
    Disjoint (atBot : Filter α) atTop := by
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  by_cases hle : x ≤ y
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot x) (Ici_mem_atTop y)
    exact Iic_disjoint_Ici.2 (hle.lt_of_ne hne).not_ge
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot y) (Ici_mem_atTop x)
    exact Iic_disjoint_Ici.2 hle

end Filter


-- Dual/order lemmas discovered by the Manifold Destiny verifier-mediated learner.
-- Paper: https://github.com/sumofagents/manifold-destiny
section
theorem Filter.Tendsto.eventually_ne_atBot' : ∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β] [NoBotOrder β] {f : α → β} {l : Filter α}, Filter.Tendsto f l Filter.atBot → ∀ (c : α), ∀ᶠ (x : α) in l, x ≠ c := by
  open Filter Filter.Tendsto Set in
    intro α β inst _ f l hf c
    exact ((hf.eventually_ne_atBot (f c)).mono fun _ => ne_of_apply_ne f)

end
