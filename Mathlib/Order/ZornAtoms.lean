/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Zorn
import Mathlib.Order.Atoms

#align_import order.zorn_atoms from "leanprover-community/mathlib"@"9aba7801eeecebb61f58a5763c2b6dd1b47dc6ef"

/-!
# Zorn lemma for (co)atoms

In this file we use Zorn's lemma to prove that a partial order is atomic if every nonempty chain
`c`, `⊥ ∉ c`, has a lower bound not equal to `⊥`. We also prove the order dual version of this
statement.
-/


open Set

/-- **Zorn's lemma**: A partial order is coatomic if every nonempty chain `c`, `⊤ ∉ c`, has an upper
bound not equal to `⊤`. -/
theorem IsCoatomic.of_isChain_bounded {α : Type*} [PartialOrder α] [OrderTop α]
    (h :
      ∀ c : Set α,
        IsChain (· ≤ ·) c → c.Nonempty → ⊤ ∉ c → ∃ (x : _) (_ : x ≠ ⊤), x ∈ upperBounds c) :
    IsCoatomic α := by
  refine ⟨fun x => le_top.eq_or_lt.imp_right fun hx => ?_⟩
  -- ⊢ ∃ a, IsCoatom a ∧ x ≤ a
  have : ∃ y ∈ Ico x ⊤, x ≤ y ∧ ∀ z ∈ Ico x ⊤, y ≤ z → z = y := by
    refine zorn_nonempty_partialOrder₀ (Ico x ⊤) (fun c hxc hc y hy => ?_) x (left_mem_Ico.2 hx)
    rcases h c hc ⟨y, hy⟩ fun h => (hxc h).2.ne rfl with ⟨z, hz, hcz⟩
    exact ⟨z, ⟨le_trans (hxc hy).1 (hcz hy), hz.lt_top⟩, hcz⟩
  rcases this with ⟨y, ⟨hxy, hy⟩, -, hy'⟩
  -- ⊢ ∃ a, IsCoatom a ∧ x ≤ a
  refine ⟨y, ⟨hy.ne, fun z hyz => le_top.eq_or_lt.resolve_right fun hz => ?_⟩, hxy⟩
  -- ⊢ False
  exact hyz.ne' (hy' z ⟨hxy.trans hyz.le, hz⟩ hyz.le)
  -- 🎉 no goals
#align is_coatomic.of_is_chain_bounded IsCoatomic.of_isChain_bounded

/-- **Zorn's lemma**: A partial order is atomic if every nonempty chain `c`, `⊥ ∉ c`, has a lower
bound not equal to `⊥`. -/
theorem IsAtomic.of_isChain_bounded {α : Type*} [PartialOrder α] [OrderBot α]
    (h :
      ∀ c : Set α,
        IsChain (· ≤ ·) c → c.Nonempty → ⊥ ∉ c → ∃ (x : _) (_ : x ≠ ⊥), x ∈ lowerBounds c) :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.mp <| IsCoatomic.of_isChain_bounded fun c hc => h c hc.symm
#align is_atomic.of_is_chain_bounded IsAtomic.of_isChain_bounded
