/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin

/-!
# fintype instance for the product of two fintypes.

-/


open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Set

variable {s t : Set α}

theorem toFinset_prod (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype (s ×ˢ t)] :
    (s ×ˢ t).toFinset = s.toFinset ×ˢ t.toFinset := by
  ext
  simp

theorem toFinset_off_diag {s : Set α} [DecidableEq α] [Fintype s] [Fintype s.offDiag] :
    s.offDiag.toFinset = s.toFinset.offDiag :=
  Finset.ext <| by simp

end Set

instance instFintypeProd (α β : Type*) [Fintype α] [Fintype β] : Fintype (α × β) :=
  ⟨univ ×ˢ univ, fun ⟨a, b⟩ => by simp⟩

namespace Finset
variable [Fintype α] [Fintype β] {s : Finset α} {t : Finset β}

@[simp] lemma univ_product_univ : univ ×ˢ univ = (univ : Finset (α × β)) := rfl

@[simp] lemma product_eq_univ [Nonempty α] [Nonempty β] : s ×ˢ t = univ ↔ s = univ ∧ t = univ := by
  simp [eq_univ_iff_forall, forall_and]

end Finset

@[simp]
theorem Fintype.card_prod (α β : Type*) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β :=
  card_product _ _

section

@[simp]
theorem infinite_prod : Infinite (α × β) ↔ Infinite α ∧ Nonempty β ∨ Nonempty α ∧ Infinite β := by
  refine
    ⟨fun H => ?_, fun H =>
      H.elim (and_imp.2 <| @Prod.infinite_of_left α β) (and_imp.2 <| @Prod.infinite_of_right α β)⟩
  rw [and_comm]; contrapose! H; intro H'
  rcases Infinite.nonempty (α × β) with ⟨a, b⟩
  haveI := fintypeOfNotInfinite (H.1 ⟨b⟩); haveI := fintypeOfNotInfinite (H.2 ⟨a⟩)
  exact H'.false

instance Pi.infinite_of_left {ι : Sort*} {π : ι → Type*} [∀ i, Nontrivial <| π i] [Infinite ι] :
    Infinite (∀ i : ι, π i) := by
  classical
  choose m n hm using fun i => exists_pair_ne (π i)
  refine Infinite.of_injective (fun i => update m i (n i)) fun x y h => of_not_not fun hne => ?_
  simp_rw [update_eq_iff, update_of_ne hne] at h
  exact (hm x h.1.symm).elim

/-- If at least one `π i` is infinite and the rest nonempty, the pi type of all `π` is infinite. -/
theorem Pi.infinite_of_exists_right {ι : Sort*} {π : ι → Sort*} (i : ι) [Infinite <| π i]
    [∀ i, Nonempty <| π i] : Infinite (∀ i : ι, π i) := by
  classical
  let ⟨m⟩ := @Pi.instNonempty ι π _
  exact Infinite.of_injective _ (update_injective m i)

/-- See `Pi.infinite_of_exists_right` for the case that only one `π i` is infinite. -/
instance Pi.infinite_of_right {ι : Sort*} {π : ι → Type*} [∀ i, Infinite <| π i] [Nonempty ι] :
    Infinite (∀ i : ι, π i) :=
  Pi.infinite_of_exists_right (Classical.arbitrary ι)

/-- Non-dependent version of `Pi.infinite_of_left`. -/
instance Function.infinite_of_left {ι : Sort*} {π : Type*} [Nontrivial π] [Infinite ι] :
    Infinite (ι → π) :=
  Pi.infinite_of_left

/-- Non-dependent version of `Pi.infinite_of_exists_right` and `Pi.infinite_of_right`. -/
instance Function.infinite_of_right {ι : Sort*} {π : Type*} [Infinite π] [Nonempty ι] :
    Infinite (ι → π) :=
  Pi.infinite_of_right

end
