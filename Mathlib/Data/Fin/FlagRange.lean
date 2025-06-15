/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Preorder.Chain

/-!
# Range of `f : Fin (n + 1) → α` as a `Flag`

Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.
Then the range of `f` is a maximal chain.

We formulate this result in terms of `IsMaxChain` and `Flag`.
-/

open Set

variable {α : Type*} [PartialOrder α] [BoundedOrder α] {n : ℕ} {f : Fin (n + 1) → α}

/-- Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.
Then the range of `f` is a maximal chain. -/
theorem IsMaxChain.range_fin_of_covBy (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
    (hcovBy : ∀ k : Fin n, f k.castSucc ⩿ f k.succ) :
    IsMaxChain (· ≤ ·) (range f) := by
  have hmono : Monotone f := Fin.monotone_iff_le_succ.2 fun k ↦ (hcovBy k).1
  refine ⟨hmono.isChain_range, fun t htc hbt ↦ hbt.antisymm fun x hx ↦ ?_⟩
  rw [mem_range]; by_contra! h
  suffices ∀ k, f k < x by simpa [hlast] using this (.last _)
  intro k
  induction k using Fin.induction with
  | zero => simpa [h0, bot_lt_iff_ne_bot] using (h 0).symm
  | succ k ihk =>
    rw [range_subset_iff] at hbt
    exact (htc.lt_of_le (hbt k.succ) hx (h _)).resolve_right ((hcovBy k).2 ihk)

/-- Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.
Then the range of `f` is a `Flag α`. -/
@[simps]
def Flag.rangeFin (f : Fin (n + 1) → α) (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
    (hcovBy : ∀ k : Fin n, f k.castSucc ⩿ f k.succ) : Flag α where
  carrier := range f
  Chain' := (IsMaxChain.range_fin_of_covBy h0 hlast hcovBy).1
  max_chain' := (IsMaxChain.range_fin_of_covBy h0 hlast hcovBy).2

@[simp] theorem Flag.mem_rangeFin {x h0 hlast hcovBy} :
    x ∈ rangeFin f h0 hlast hcovBy ↔ ∃ k, f k = x :=
  Iff.rfl
