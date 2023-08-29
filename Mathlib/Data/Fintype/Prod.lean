/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod

#align_import data.fintype.prod from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# fintype instance for the product of two fintypes.

-/


open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset Function

namespace Set

variable {s t : Set α}

theorem toFinset_prod (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype (s ×ˢ t)] :
    (s ×ˢ t).toFinset = s.toFinset ×ˢ t.toFinset := by
  ext
  -- ⊢ a✝ ∈ toFinset (s ×ˢ t) ↔ a✝ ∈ toFinset s ×ˢ toFinset t
  simp
  -- 🎉 no goals
#align set.to_finset_prod Set.toFinset_prod

theorem toFinset_off_diag {s : Set α} [DecidableEq α] [Fintype s] [Fintype s.offDiag] :
    s.offDiag.toFinset = s.toFinset.offDiag :=
  Finset.ext <| by simp
                   -- 🎉 no goals
#align set.to_finset_off_diag Set.toFinset_off_diag

end Set

instance instFintypeProd (α β : Type*) [Fintype α] [Fintype β] : Fintype (α × β) :=
  ⟨univ ×ˢ univ, fun ⟨a, b⟩ => by simp⟩
                                  -- 🎉 no goals

@[simp]
theorem Finset.univ_product_univ {α β : Type*} [Fintype α] [Fintype β] :
    (univ : Finset α) ×ˢ (univ : Finset β) = univ :=
  rfl
#align finset.univ_product_univ Finset.univ_product_univ

@[simp]
theorem Fintype.card_prod (α β : Type*) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β :=
  card_product _ _
#align fintype.card_prod Fintype.card_prod

section

open Classical

@[simp]
theorem infinite_prod : Infinite (α × β) ↔ Infinite α ∧ Nonempty β ∨ Nonempty α ∧ Infinite β := by
  refine'
    ⟨fun H => _, fun H =>
      H.elim (and_imp.2 <| @Prod.infinite_of_left α β) (and_imp.2 <| @Prod.infinite_of_right α β)⟩
  rw [and_comm]; contrapose! H; intro H'
  -- ⊢ Nonempty β ∧ Infinite α ∨ Nonempty α ∧ Infinite β
                 -- ⊢ ¬Infinite (α × β)
                                -- ⊢ False
  rcases Infinite.nonempty (α × β) with ⟨a, b⟩
  -- ⊢ False
  haveI := fintypeOfNotInfinite (H.1 ⟨b⟩); haveI := fintypeOfNotInfinite (H.2 ⟨a⟩)
  -- ⊢ False
                                           -- ⊢ False
  exact H'.false
  -- 🎉 no goals
#align infinite_prod infinite_prod

instance Pi.infinite_of_left {ι : Sort*} {π : ι → Sort _} [∀ i, Nontrivial <| π i] [Infinite ι] :
    Infinite (∀ i : ι, π i) := by
  choose m n hm using fun i => exists_pair_ne (π i)
  -- ⊢ Infinite ((i : ι) → π i)
  refine' Infinite.of_injective (fun i => update m i (n i)) fun x y h => of_not_not fun hne => _
  -- ⊢ False
  simp_rw [update_eq_iff, update_noteq hne] at h
  -- ⊢ False
  exact (hm x h.1.symm).elim
  -- 🎉 no goals
#align pi.infinite_of_left Pi.infinite_of_left

/-- If at least one `π i` is infinite and the rest nonempty, the pi type of all `π` is infinite. -/
theorem Pi.infinite_of_exists_right {ι : Type*} {π : ι → Type*} (i : ι) [Infinite <| π i]
    [∀ i, Nonempty <| π i] : Infinite (∀ i : ι, π i) :=
  let ⟨m⟩ := @Pi.Nonempty ι π _
  Infinite.of_injective _ (update_injective m i)
#align pi.infinite_of_exists_right Pi.infinite_of_exists_right

/-- See `Pi.infinite_of_exists_right` for the case that only one `π i` is infinite. -/
instance Pi.infinite_of_right {ι : Sort _} {π : ι → Sort _} [∀ i, Infinite <| π i] [Nonempty ι] :
    Infinite (∀ i : ι, π i) :=
  Pi.infinite_of_exists_right (Classical.arbitrary ι)
#align pi.infinite_of_right Pi.infinite_of_right

/-- Non-dependent version of `Pi.infinite_of_left`. -/
instance Function.infinite_of_left {ι π : Sort _} [Nontrivial π] [Infinite ι] : Infinite (ι → π) :=
  Pi.infinite_of_left
#align function.infinite_of_left Function.infinite_of_left

/-- Non-dependent version of `Pi.infinite_of_exists_right` and `Pi.infinite_of_right`. -/
instance Function.infinite_of_right {ι π : Sort _} [Infinite π] [Nonempty ι] : Infinite (ι → π) :=
  Pi.infinite_of_right
#align function.infinite_of_right Function.infinite_of_right

end
