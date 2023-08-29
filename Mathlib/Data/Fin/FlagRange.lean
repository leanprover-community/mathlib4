/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Cover
import Mathlib.Order.Chain
import Mathlib.Data.Fin.Basic

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

variable {α : Type _} [PartialOrder α] [BoundedOrder α] {n : ℕ} {f : Fin (n + 1) → α}

/-- Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.
Then the range of `f` is a maximal chain. -/
theorem IsMaxChain.range_fin_of_covby (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
    (hcovby : ∀ k : Fin n, f k.castSucc ⩿ f k.succ) :
    IsMaxChain (· ≤ ·) (range f) := by
  have hmono : Monotone f := Fin.monotone_iff_le_succ.2 fun k ↦ (hcovby k).1
  -- ⊢ IsMaxChain (fun x x_1 => x ≤ x_1) (range f)
  refine ⟨hmono.isChain_range, fun t htc hbt ↦ hbt.antisymm fun x hx ↦ ?_⟩
  -- ⊢ x ∈ range f
  rw [mem_range]; by_contra' h
  -- ⊢ ∃ y, f y = x
                  -- ⊢ False
  suffices ∀ k, f k < x by simpa [hlast] using this (.last _)
  -- ⊢ ∀ (k : Fin (n + 1)), f k < x
  intro k
  -- ⊢ f k < x
  induction k using Fin.induction with
  | zero => simpa [h0, bot_lt_iff_ne_bot] using (h 0).symm
  | succ k ihk =>
    rw [range_subset_iff] at hbt
    exact (htc.lt_of_le (hbt k.succ) hx (h _)).resolve_right ((hcovby k).2 ihk)

/-- Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.
Then the range of `f` is a `Flag α`. -/
@[simps]
def Flag.rangeFin (f : Fin (n + 1) → α) (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
    (hcovby : ∀ k : Fin n, f k.castSucc ⩿ f k.succ) : Flag α where
  carrier := range f
  Chain' := (IsMaxChain.range_fin_of_covby h0 hlast hcovby).1
  max_chain' := (IsMaxChain.range_fin_of_covby h0 hlast hcovby).2

@[simp] theorem Flag.mem_rangeFin {x h0 hlast hcovby} :
    x ∈ rangeFin f h0 hlast hcovby ↔ ∃ k, f k = x :=
  Iff.rfl
