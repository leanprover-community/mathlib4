/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Denumerable

/-!
# Equivalences involving `List`-like types

This file defines some additional constructive equivalences using `Encodable` and the pairing
function on `ℕ`.
-/

open Mathlib (Vector)
open Nat List

namespace Encodable

variable {α : Type*}

section List

variable [Encodable α]

/-- Explicit encoding function for `List α` -/
def encodeList : List α → ℕ
  | [] => 0
  | a :: l => succ (pair (encode a) (encodeList l))

/-- Explicit decoding function for `List α` -/
def decodeList : ℕ → Option (List α)
  | 0 => some []
  | succ v =>
    match unpair v, unpair_right_le v with
    | (v₁, v₂), h =>
      have : v₂ < succ v := lt_succ_of_le h
      (· :: ·) <$> decode (α := α) v₁ <*> decodeList v₂

/-- If `α` is encodable, then so is `List α`. This uses the `pair` and `unpair` functions from
`Data.Nat.Pairing`. -/
instance _root_.List.encodable : Encodable (List α) :=
  ⟨encodeList, decodeList, fun l => by
    induction' l with a l IH <;> simp [encodeList, decodeList, unpair_pair, encodek, *]⟩

instance _root_.List.countable {α : Type*} [Countable α] : Countable (List α) := by
  haveI := Encodable.ofCountable α
  infer_instance

@[simp]
theorem encode_list_nil : encode (@nil α) = 0 :=
  rfl

@[simp]
theorem encode_list_cons (a : α) (l : List α) :
    encode (a :: l) = succ (pair (encode a) (encode l)) :=
  rfl

@[simp]
theorem decode_list_zero : decode (α := List α) 0 = some [] :=
  show decodeList 0 = some [] by rw [decodeList]

@[simp, nolint unusedHavesSuffices] -- Porting note: false positive
theorem decode_list_succ (v : ℕ) :
    decode (α := List α) (succ v) =
      (· :: ·) <$> decode (α := α) v.unpair.1 <*> decode (α := List α) v.unpair.2 :=
  show decodeList (succ v) = _ by
    cases' e : unpair v with v₁ v₂
    simp [decodeList, e]; rfl

theorem length_le_encode : ∀ l : List α, length l ≤ encode l
  | [] => Nat.zero_le _
  | _ :: l => succ_le_succ <| (length_le_encode l).trans (right_le_pair _ _)

end List

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

/-- If `α` is countable, then so is `Multiset α`. -/
instance _root_.Multiset.countable {α : Type*} [Countable α] : Countable (Multiset α) :=
  Quotient.countable

end Finset

/-- A listable type with decidable equality is encodable. -/
def encodableOfList [DecidableEq α] (l : List α) (H : ∀ x, x ∈ l) : Encodable α :=
  ⟨fun a => indexOf a l, l.get?, fun _ => indexOf_get? (H _)⟩

/-- A finite type is encodable. Because the encoding is not unique, we wrap it in `Trunc` to
preserve computability. -/
def _root_.Fintype.truncEncodable (α : Type*) [DecidableEq α] [Fintype α] : Trunc (Encodable α) :=
  @Quot.recOnSubsingleton _ _ (fun s : Multiset α => (∀ x : α, x ∈ s) → Trunc (Encodable α)) _
    Finset.univ.1 (fun l H => Trunc.mk <| encodableOfList l H) Finset.mem_univ

/-- A noncomputable way to arbitrarily choose an ordering on a finite type.
It is not made into a global instance, since it involves an arbitrary choice.
This can be locally made into an instance with `attribute [local instance] Fintype.toEncodable`. -/
noncomputable def _root_.Fintype.toEncodable (α : Type*) [Fintype α] : Encodable α := by
  classical exact (Fintype.truncEncodable α).out

/-- If `α` is encodable, then so is `Vector α n`. -/
instance _root_.Vector.encodable [Encodable α] {n} : Encodable (Vector α n) :=
  Subtype.encodable

/-- If `α` is countable, then so is `Vector α n`. -/
instance _root_.Vector.countable [Countable α] {n} : Countable (Vector α n) :=
  Subtype.countable

/-- If `α` is encodable, then so is `Fin n → α`. -/
instance finArrow [Encodable α] {n} : Encodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm

instance finPi (n) (π : Fin n → Type*) [∀ i, Encodable (π i)] : Encodable (∀ i, π i) :=
  ofEquiv _ (Equiv.piEquivSubtypeSigma (Fin n) π)

/-- If `α` is encodable, then so is `Finset α`. -/
instance _root_.Finset.encodable [Encodable α] : Encodable (Finset α) :=
  haveI := decidableEqOfEncodable α
  ofEquiv { s : Multiset α // s.Nodup }
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

/-- If `α` is countable, then so is `Finset α`. -/
instance _root_.Finset.countable [Countable α] : Countable (Finset α) :=
  Finset.val_injective.countable

-- TODO: Unify with `fintypePi` and find a better name
/-- When `α` is finite and `β` is encodable, `α → β` is encodable too. Because the encoding is not
unique, we wrap it in `Trunc` to preserve computability. -/
def fintypeArrow (α : Type*) (β : Type*) [DecidableEq α] [Fintype α] [Encodable β] :
    Trunc (Encodable (α → β)) :=
  (Fintype.truncEquivFin α).map fun f =>
    Encodable.ofEquiv (Fin (Fintype.card α) → β) <| Equiv.arrowCongr f (Equiv.refl _)

/-- When `α` is finite and all `π a` are encodable, `Π a, π a` is encodable too. Because the
encoding is not unique, we wrap it in `Trunc` to preserve computability. -/
def fintypePi (α : Type*) (π : α → Type*) [DecidableEq α] [Fintype α] [∀ a, Encodable (π a)] :
    Trunc (Encodable (∀ a, π a)) :=
  (Fintype.truncEncodable α).bind fun a =>
    (@fintypeArrow α (Σa, π a) _ _ (@Sigma.encodable _ _ a _)).bind fun f =>
      Trunc.mk <|
        @Encodable.ofEquiv _ _ (@Subtype.encodable _ _ f _)
          (Equiv.piEquivSubtypeSigma α π)

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
  -- Porting note: used the `trans` tactic
  ((sortedUniv_nodup α).getEquivOfForallMemList _ mem_sortedUniv).symm.trans <|
    Equiv.cast (congr_arg _ (length_sortedUniv α))

/-- If `α` and `β` are encodable and `α` is a fintype, then `α → β` is encodable as well. -/
instance fintypeArrowOfEncodable {α β : Type*} [Encodable α] [Fintype α] [Encodable β] :
    Encodable (α → β) :=
  ofEquiv (Fin (Fintype.card α) → β) <| Equiv.arrowCongr fintypeEquivFin (Equiv.refl _)

end Encodable

namespace Denumerable

variable {α : Type*} {β : Type*} [Denumerable α] [Denumerable β]

open Encodable

section List

@[nolint unusedHavesSuffices] -- Porting note: false positive
theorem denumerable_list_aux : ∀ n : ℕ, ∃ a ∈ @decodeList α _ n, encodeList a = n
  | 0 => by rw [decodeList]; exact ⟨_, rfl, rfl⟩
  | succ v => by
    cases' e : unpair v with v₁ v₂
    have h := unpair_right_le v
    rw [e] at h
    rcases have : v₂ < succ v := lt_succ_of_le h
      denumerable_list_aux v₂ with
      ⟨a, h₁, h₂⟩
    rw [Option.mem_def] at h₁
    use ofNat α v₁ :: a
    simp [decodeList, e, h₂, h₁, encodeList, pair_unpair' e]

/-- If `α` is denumerable, then so is `List α`. -/
instance denumerableList : Denumerable (List α) :=
  ⟨denumerable_list_aux⟩

@[simp]
theorem list_ofNat_zero : ofNat (List α) 0 = [] := by rw [← @encode_list_nil α, ofNat_encode]

@[simp, nolint unusedHavesSuffices] -- Porting note: false positive
theorem list_ofNat_succ (v : ℕ) :
    ofNat (List α) (succ v) = ofNat α v.unpair.1 :: ofNat (List α) v.unpair.2 :=
  ofNat_of_decode <|
    show decodeList (succ v) = _ by
      cases' e : unpair v with v₁ v₂
      simp [decodeList, e]
      rw [show decodeList v₂ = decode (α := List α) v₂ from rfl, decode_eq_ofNat, Option.seq_some]

end List

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
  | [], n => rfl
  | m :: l, n => by rw [raise, lower, Nat.add_sub_cancel_right, lower_raise l]

theorem raise_lower : ∀ {l n}, List.Sorted (· ≤ ·) (n :: l) → raise (lower l n) n = l
  | [], n, _ => rfl
  | m :: l, n, h => by
    have : n ≤ m := List.rel_of_sorted_cons h _ (l.mem_cons_self _)
    simp [raise, lower, Nat.sub_add_cancel this, raise_lower h.of_cons]

theorem raise_chain : ∀ l n, List.Chain (· ≤ ·) n (raise l n)
  | [], _ => List.Chain.nil
  | _ :: _, _ => List.Chain.cons (Nat.le_add_left _ _) (raise_chain _ _)

/-- `raise l n` is a non-decreasing sequence. -/
theorem raise_sorted : ∀ l n, List.Sorted (· ≤ ·) (raise l n)
  | [], _ => List.sorted_nil
  | _ :: _, _ => List.chain_iff_pairwise.1 (raise_chain _ _)

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
      simp [-Multiset.map_coe, List.mergeSort'_eq_self _ (raise_sorted _ _), lower_raise]⟩

end Multiset

section Finset

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
  | [], n => rfl
  | m :: l, n => by simp [raise', lower', add_tsub_cancel_right, lower_raise']

theorem raise_lower' : ∀ {l n}, (∀ m ∈ l, n ≤ m) → List.Sorted (· < ·) l → raise' (lower' l n) n = l
  | [], n, _, _ => rfl
  | m :: l, n, h₁, h₂ => by
    have : n ≤ m := h₁ _ (l.mem_cons_self _)
    simp [raise', lower', Nat.sub_add_cancel this,
      raise_lower' (List.rel_of_sorted_cons h₂ : ∀ a ∈ l, m < a) h₂.of_cons]

theorem raise'_chain : ∀ (l) {m n}, m < n → List.Chain (· < ·) m (raise' l n)
  | [], _, _, _ => List.Chain.nil
  | _ :: _, _, _, h =>
    List.Chain.cons (lt_of_lt_of_le h (Nat.le_add_left _ _)) (raise'_chain _ (lt_succ_self _))

/-- `raise' l n` is a strictly increasing sequence. -/
theorem raise'_sorted : ∀ l n, List.Sorted (· < ·) (raise' l n)
  | [], _ => List.sorted_nil
  | _ :: _, _ => List.chain_iff_pairwise.1 (raise'_chain _ (lt_succ_self _))

/-- Makes `raise' l n` into a finset. Elements are distinct thanks to `raise'_sorted`. -/
def raise'Finset (l : List ℕ) (n : ℕ) : Finset ℕ :=
  ⟨raise' l n, (raise'_sorted _ _).imp (@ne_of_lt _ _)⟩

/-- If `α` is denumerable, then so is `Finset α`. Warning: this is *not* the same encoding as used
in `Finset.encodable`. -/
instance finset : Denumerable (Finset α) :=
  mk'
    ⟨fun s : Finset α => encode <| lower' ((s.map (eqv α).toEmbedding).sort (· ≤ ·)) 0, fun n =>
      Finset.map (eqv α).symm.toEmbedding (raise'Finset (ofNat (List ℕ) n) 0), fun s =>
      Finset.eq_of_veq <| by
        simp [-Multiset.map_coe, raise'Finset,
          raise_lower' (fun n _ => Nat.zero_le n) (Finset.sort_sorted_lt _)],
      fun n => by
      simp [-Multiset.map_coe, Finset.map, raise'Finset, Finset.sort,
        List.mergeSort'_eq_self (· ≤ ·) ((raise'_sorted _ _).imp (@le_of_lt _ _)), lower_raise']⟩

end Finset

end Denumerable

namespace Equiv

/-- The type lists on unit is canonically equivalent to the natural numbers. -/
def listUnitEquiv : List Unit ≃ ℕ where
  toFun := List.length
  invFun n := List.replicate n ()
  left_inv u := List.length_injective (by simp)
  right_inv n := List.length_replicate n ()

/-- `List ℕ` is equivalent to `ℕ`. -/
def listNatEquivNat : List ℕ ≃ ℕ :=
  Denumerable.eqv _

/-- If `α` is equivalent to `ℕ`, then `List α` is equivalent to `α`. -/
def listEquivSelfOfEquivNat {α : Type*} (e : α ≃ ℕ) : List α ≃ α :=
  calc
    List α ≃ List ℕ := listEquivOfEquiv e
    _ ≃ ℕ := listNatEquivNat
    _ ≃ α := e.symm

end Equiv
