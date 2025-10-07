/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Sort
import Mathlib.Logic.Equiv.List

/-!
# `Encodable` and `Denumerable` instances for `Multiset`
-/

variable {α : Type*}

open Encodable

section Finset

variable [Encodable α]

private def enle : α → α → Prop :=
  encode ⁻¹'o (· ≤ ·)

private theorem enle.isLinearOrder : IsLinearOrder α enle :=
  (RelEmbedding.preimage ⟨encode, encode_injective⟩ (· ≤ ·)).isLinearOrder

private def decidable_enle (a b : α) : Decidable (enle a b) := by
  unfold enle Order.Preimage
  infer_instance

attribute [local instance] enle.isLinearOrder decidable_enle

/-- Explicit encoding function for `Multiset α` -/
def encodeMultiset (s : Multiset α) : ℕ :=
  encode (s.sort enle)

/-- Explicit decoding function for `Multiset α` -/
def decodeMultiset (n : ℕ) : Option (Multiset α) :=
  ((↑) : List α → Multiset α) <$> decode (α := List α) n

/-- If `α` is encodable, then so is `Multiset α`. -/
instance _root_.Multiset.encodable : Encodable (Multiset α) :=
  ⟨encodeMultiset, decodeMultiset, fun s => by simp [encodeMultiset, decodeMultiset, encodek]⟩

end Finset

namespace Denumerable
variable [Denumerable α]

section Multiset

/-- Outputs the list of differences of the input list, that is
`lower [a₁, a₂, ...] n = [a₁ - n, a₂ - a₁, ...]` -/
def lower : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: l, n => (m - n) :: lower l m

/-- Outputs the list of partial sums of the input list, that is
`raise [a₁, a₂, ...] n = [n + a₁, n + a₁ + a₂, ...]` -/
def raise : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: l, n => (m + n) :: raise l (m + n)

theorem lower_raise : ∀ l n, lower (raise l n) n = l
  | [], _ => rfl
  | m :: l, n => by rw [raise, lower, Nat.add_sub_cancel_right, lower_raise l]

theorem raise_lower : ∀ {l n}, List.Sorted (· ≤ ·) (n :: l) → raise (lower l n) n = l
  | [], _, _ => rfl
  | m :: l, n, h => by
    have : n ≤ m := List.rel_of_sorted_cons h _ List.mem_cons_self
    simp [raise, lower, Nat.sub_add_cancel this, raise_lower h.of_cons]

theorem isChain_raise : ∀ l n, List.IsChain (· ≤ ·) (raise l n)
  | [], _ => .nil
  | [_], _ => .singleton _
  | _ :: _ :: _, _ => .cons_cons (Nat.le_add_left _ _) (isChain_raise (_ :: _) _)

theorem isChain_cons_raise (l n) : List.IsChain (· ≤ ·) (n :: raise l n) :=
  isChain_raise (n :: l) 0

@[deprecated (since := "2025-09-19")]
alias raise_chain := isChain_cons_raise

/-- `raise l n` is a non-decreasing sequence. -/
theorem raise_sorted (l n) : List.Sorted (· ≤ ·) (raise l n) := (isChain_raise _ _).pairwise

/-- If `α` is denumerable, then so is `Multiset α`. Warning: this is *not* the same encoding as used
in `Multiset.encodable`. -/
instance multiset : Denumerable (Multiset α) :=
  mk'
    ⟨fun s : Multiset α => encode <| lower ((s.map encode).sort (· ≤ ·)) 0,
     fun n =>
      Multiset.map (ofNat α) (raise (ofNat (List ℕ) n) 0),
     fun s => by
      have :=
        raise_lower (List.sorted_cons.2 ⟨fun n _ => Nat.zero_le n, (s.map encode).sort_sorted _⟩)
      simp [-Multiset.map_coe, this],
     fun n => by
      simp [-Multiset.map_coe, List.mergeSort_eq_self _ (raise_sorted _ _), lower_raise]⟩

end Multiset

end Denumerable
