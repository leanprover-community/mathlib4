/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Aaron Anderson
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Antichain
import Mathlib.Order.OrderIsoNat

variable {α : Type*} {r : α → α → Prop} {s : Set α}

/-- A well quasi-order or WQO is a relation such that any infinite sequence contains an infinite
monotonic subsequence, or equivalently, two elements `f m` and `f n` with `m < n` and
`r (f m) (f n)`.

For a preorder, this is equivalent to having a well-founded order with no infinite antichains.

Despite the nomenclature, we don't require the relation to be preordered. Moreover, a well
quasi-order will not in general be a well-order. -/
def WellQuasiOrdered (r : α → α → Prop) : Prop :=
  ∀ f : ℕ → α, ∃ m n : ℕ, m < n ∧ r (f m) (f n)

theorem IsAntichain.finite_of_wellQuasiOrdered (hs : IsAntichain r s) (hr : WellQuasiOrdered r) :
    s.Finite := by
  refine Set.not_infinite.1 fun hi => ?_
  obtain ⟨m, n, hmn, h⟩ := hr fun n => hi.natEmbedding _ n
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    hs.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)

theorem Finite.wellQuasiOrdered (r : α → α → Prop) [Finite α] [IsRefl α r] :
    WellQuasiOrdered r := by
  intro f
  obtain ⟨m, n, h, hf⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem (f := f)
    fun _ ↦ Set.mem_univ _
  exact ⟨m, n, h, hf ▸ refl _⟩

theorem WellQuasiOrdered.exists_monotone_subseq [IsPreorder α r] (h : WellQuasiOrdered r)
    (f : ℕ → α) : ∃ g : ℕ ↪o ℕ, ∀ m n, m ≤ n → r (f (g m)) (f (g n)) := by
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f
  · refine ⟨g, fun m n hle => ?_⟩
    obtain hlt | rfl := hle.lt_or_eq
    exacts [h1 m n hlt, refl_of r _]
  · obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g)
    cases h2 m n hlt hle

theorem wellQuasiOrdered_iff_exists_monotone_subseq [IsPreorder α r] :
    WellQuasiOrdered r ↔ ∀ f : ℕ → α, ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) := by
  constructor <;> intro h f
  · exact h.exists_monotone_subseq f
  · obtain ⟨g, gmon⟩ := h f
    exact ⟨_, _, g.strictMono Nat.zero_lt_one, gmon _ _ (Nat.zero_le 1)⟩

/-- A typeclass for an ordered with a well quasi-ordered `≤` relation. -/
@[mk_iff wellQuasiOrderedLE_iff']
class WellQuasiOrderedLE (α : Type*) [LE α] where
  wqo : @WellQuasiOrdered α (· ≤ ·)

theorem wellQuasiOrdered_le [LE α] [h : WellQuasiOrderedLE α] : @WellQuasiOrdered α (· ≤ ·) :=
  h.wqo

section Preorder
variable [Preorder α]

instance (priority := 100) Finite.to_wellQuasiOrderedLE [Finite α] : WellQuasiOrderedLE α where
  wqo := Finite.wellQuasiOrdered _

instance (priority := 100) WellQuasiOrderedLE.to_wellFoundedLT [WellQuasiOrderedLE α] :
    WellFoundedLT α := by
  rw [WellFoundedLT, isWellFounded_iff, RelEmbedding.wellFounded_iff_no_descending_seq]
  refine ⟨fun f ↦ ?_⟩
  obtain ⟨a, b, h, hf⟩ := wellQuasiOrdered_le f
  exact (f.map_rel_iff.2 h).not_le hf

theorem WellQuasiOrderedLE.finite_of_isAntichain [WellQuasiOrderedLE α]
    (h : IsAntichain (· ≤ ·) s) : s.Finite :=
  h.finite_of_wellQuasiOrdered wellQuasiOrdered_le

/-- A preorder is well quasi-ordered iff it's well-founded and has no infinite antichains. -/
theorem wellQuasiOrderedLE_iff :
    WellQuasiOrderedLE α ↔ WellFoundedLT α ∧ ∀ s : Set α, IsAntichain (· ≤ ·) s → s.Finite := by
  refine ⟨fun h ↦ ⟨h.to_wellFoundedLT, fun s ↦ h.finite_of_isAntichain⟩, fun ⟨hwf, hc⟩ ↦ ?_⟩
  rw [wellQuasiOrderedLE_iff', WellQuasiOrdered]
  contrapose! hc
  obtain ⟨f, hf⟩ := hc
  have := Function.argmin




#exit
end Preorder
