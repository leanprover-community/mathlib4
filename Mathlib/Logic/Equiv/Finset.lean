/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Multiset

/-!
# `Encodable` and `Denumerable` instances for `Finset`
-/

variable {α}

open Encodable

/-- If `α` is encodable, then so is `Finset α`. -/
instance Finset.encodable [Encodable α] : Encodable (Finset α) :=
  haveI := decidableEqOfEncodable α
  ofEquiv { s : Multiset α // s.Nodup }
    { toFun := fun ⟨a, b⟩ => ⟨a, b⟩
      invFun := fun ⟨a, b⟩ => ⟨a, b⟩ }

namespace Encodable

/-- The elements of a `Fintype` as a sorted list. -/
def sortedUniv (α) [Fintype α] [Encodable α] : List α :=
  Finset.univ.sort (Encodable.encode' α ⁻¹'o (· ≤ ·))

@[simp]
theorem mem_sortedUniv {α} [Fintype α] [Encodable α] (x : α) : x ∈ sortedUniv α :=
  (Finset.mem_sort _).2 (Finset.mem_univ _)

@[simp]
theorem length_sortedUniv (α) [Fintype α] [Encodable α] : (sortedUniv α).length = Fintype.card α :=
  Finset.length_sort _

@[simp]
theorem sortedUniv_nodup (α) [Fintype α] [Encodable α] : (sortedUniv α).Nodup :=
  Finset.sort_nodup _ _

@[simp]
theorem sortedUniv_toFinset (α) [Fintype α] [Encodable α] [DecidableEq α] :
    (sortedUniv α).toFinset = Finset.univ :=
  Finset.sort_toFinset _ _

/-- An encodable `Fintype` is equivalent to the same size `Fin`. -/
def fintypeEquivFin {α} [Fintype α] [Encodable α] : α ≃ Fin (Fintype.card α) :=
  haveI : DecidableEq α := Encodable.decidableEqOfEncodable _
  ((sortedUniv_nodup α).getEquivOfForallMemList _ mem_sortedUniv).symm.trans <|
    Equiv.cast (congr_arg _ (length_sortedUniv α))

end Encodable


namespace Denumerable
variable [Denumerable α]

/-- Outputs the list of differences minus one of the input list, that is
`lower' [a₁, a₂, a₃, ...] n = [a₁ - n, a₂ - a₁ - 1, a₃ - a₂ - 1, ...]`. -/
def lower' : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: l, n => (m - n) :: lower' l (m + 1)

/-- Outputs the list of partial sums plus one of the input list, that is
`raise [a₁, a₂, a₃, ...] n = [n + a₁, n + a₁ + a₂ + 1, n + a₁ + a₂ + a₃ + 2, ...]`. Adding one each
time ensures the elements are distinct. -/
def raise' : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: l, n => (m + n) :: raise' l (m + n + 1)

theorem lower_raise' : ∀ l n, lower' (raise' l n) n = l
  | [], _ => rfl
  | m :: l, n => by simp [raise', lower', lower_raise']

theorem raise_lower' : ∀ {l n}, (∀ m ∈ l, n ≤ m) → List.SortedLT l → raise' (lower' l n) n = l
  | [], _, _, _ => rfl
  | m :: l, n, h₁, h₂ => by
    have : n ≤ m := h₁ _ List.mem_cons_self
    simp [raise', lower', Nat.sub_add_cancel this,
      raise_lower' (fun _ => List.rel_of_pairwise_cons h₂.pairwise : ∀ a ∈ l, m < a)
      h₂.pairwise.of_cons.sortedLT]

theorem isChain_raise' : ∀ (l) (n), List.IsChain (· < ·) (raise' l n)
  | [], _ => .nil
  | [_], _ => .singleton _
  | _ :: _ :: _, _ => .cons_cons (by omega) (isChain_raise' (_ :: _) _)

theorem isChain_cons_raise' (l m) : List.IsChain (· < ·) (m :: raise' l (m + 1)) :=
  isChain_raise' (m :: l) 0

theorem isChain_cons_raise'_of_lt (l) {m n} (h : m < n) :
    List.IsChain (· < ·) (m :: raise' l n) := by
  unfold raise'; cases l with grind [isChain_cons_raise']

@[deprecated (since := "2025-09-19")]
alias raise'_chain := isChain_cons_raise'_of_lt

/-- `raise' l n` is a strictly increasing sequence. -/
theorem raise'_sorted (l n) : List.SortedLT (raise' l n) := (isChain_raise' _ _).sortedLT

/-- Makes `raise' l n` into a finset. Elements are distinct thanks to `raise'_sorted`. -/
def raise'Finset (l : List ℕ) (n : ℕ) : Finset ℕ :=
  ⟨raise' l n, (raise'_sorted _ _).nodup⟩

/-- If `α` is denumerable, then so is `Finset α`. Warning: this is *not* the same encoding as used
in `Finset.encodable`. -/
instance finset : Denumerable (Finset α) :=
  mk'
    ⟨fun s : Finset α => encode <| lower' (s.map (eqv α).toEmbedding).sort 0, fun n =>
      Finset.map (eqv α).symm.toEmbedding (raise'Finset (ofNat (List ℕ) n) 0), fun s =>
      Finset.eq_of_veq <| by
        simp [-Multiset.map_coe, raise'Finset,
          raise_lower' (fun n _ => Nat.zero_le n) (Finset.sort_sorted_lt _)],
      fun n => by
      simp [-Multiset.map_coe, Finset.map, raise'Finset, Finset.sort,
        List.mergeSort_eq_self _ (raise'_sorted _ _).sortedLE.pairwise, lower_raise']⟩

end Denumerable
