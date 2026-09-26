/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Prod

/-!
# `Filter.atTop` and `Filter.atBot` filters on products
-/

public section

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

@[to_dual]
theorem prod_atTop_atTop_eq [Preorder α] [Preorder β] :
    (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β)) := by
  cases isEmpty_or_nonempty α
  · subsingleton
  cases isEmpty_or_nonempty β
  · subsingleton
  simpa [atTop, prod_iInf_left, prod_iInf_right, iInf_prod] using iInf_comm

lemma tendsto_finsetProd_atTop :
    Tendsto (fun (p : Finset ι × Finset ι') ↦ p.1 ×ˢ p.2) atTop atTop := by
  classical
  apply Monotone.tendsto_atTop_atTop
  · intro p q hpq
    simpa using Finset.product_subset_product hpq.1 hpq.2
  · intro b
    use (Finset.image Prod.fst b, Finset.image Prod.snd b)
    exact Finset.subset_product

@[deprecated (since := "2026-04-08")] alias tendsto_finset_prod_atTop := tendsto_finsetProd_atTop

@[to_dual]
theorem prod_map_atTop_eq {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂]
    (u₁ : β₁ → α₁) (u₂ : β₂ → α₂) : map u₁ atTop ×ˢ map u₂ atTop = map (Prod.map u₁ u₂) atTop := by
  rw [prod_map_map_eq, prod_atTop_atTop_eq, Prod.map_def]

@[to_dual]
theorem tendsto_atTop_diagonal [Preorder α] : Tendsto (fun a : α => (a, a)) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_id.prodMk tendsto_id

@[to_dual]
theorem Tendsto.prod_map_prod_atTop [Preorder γ] {F : Filter α} {G : Filter β} {f : α → γ}
    {g : β → γ} (hf : Tendsto f F atTop) (hg : Tendsto g G atTop) :
    Tendsto (Prod.map f g) (F ×ˢ G) atTop := by
  rw [← prod_atTop_atTop_eq]
  exact hf.prodMap hg

@[to_dual]
theorem Tendsto.prod_atTop [Preorder α] [Preorder γ] {f g : α → γ}
    (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    Tendsto (Prod.map f g) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact hf.prod_map_prod_atTop hg

@[to_dual]
theorem eventually_atTop_prod_self [Nonempty α] [Preorder α] [IsDirectedOrder α]
    {p : α × α → Prop} : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ k l, a ≤ k → a ≤ l → p (k, l) := by
  simp [← prod_atTop_atTop_eq, (@atTop_basis α _ _).prod_self.eventually_iff]

@[to_dual]
theorem eventually_atTop_prod_self' [Nonempty α] [Preorder α] [IsDirectedOrder α]
    {p : α × α → Prop} : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ k, a ≤ k → ∀ l, a ≤ l → p (k, l) := by
  simp only [eventually_atTop_prod_self, forall_cond_comm]

@[to_dual]
theorem eventually_atTop_curry [Preorder α] [Preorder β] {p : α × β → Prop}
    (hp : ∀ᶠ x : α × β in Filter.atTop, p x) : ∀ᶠ k in atTop, ∀ᶠ l in atTop, p (k, l) := by
  rw [← prod_atTop_atTop_eq] at hp
  exact hp.curry

end Filter
