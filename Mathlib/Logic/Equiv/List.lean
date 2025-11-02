/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Logic.Denumerable

/-!
# Equivalences involving `List`-like types

This file defines some additional constructive equivalences using `Encodable` and the pairing
function on `ℕ`.
-/

assert_not_exists Monoid Multiset.sort

open List
open Nat

namespace Equiv

/-- An equivalence between `α` and `β` generates an equivalence between `List α` and `List β`. -/
def listEquivOfEquiv {α β} (e : α ≃ β) : List α ≃ List β where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv l := by rw [List.map_map, e.symm_comp_self, List.map_id]
  right_inv l := by rw [List.map_map, e.self_comp_symm, List.map_id]

end Equiv

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

@[simp]
theorem decodeList_encodeList_eq_self (l : List α) : decodeList (encodeList l) = some l := by
  induction l <;> simp [encodeList, decodeList, unpair_pair, encodek, *]

/-- If `α` is encodable, then so is `List α`. This uses the `pair` and `unpair` functions from
`Data.Nat.Pairing`. -/
instance _root_.List.encodable : Encodable (List α) :=
  ⟨encodeList, decodeList, decodeList_encodeList_eq_self⟩

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

@[simp]
theorem decode_list_succ (v : ℕ) :
    decode (α := List α) (succ v) =
      (· :: ·) <$> decode (α := α) v.unpair.1 <*> decode (α := List α) v.unpair.2 :=
  show decodeList (succ v) = _ by
    rcases e : unpair v with ⟨v₁, v₂⟩
    simp [decodeList, e]; rfl

theorem length_le_encode : ∀ l : List α, length l ≤ encode l
  | [] => Nat.zero_le _
  | _ :: l => succ_le_succ <| (length_le_encode l).trans (right_le_pair _ _)

end List

/-! These two lemmas are not about lists, but are convenient to keep here and don't
require `Finset.sort`. -/

/-- If `α` is countable, then so is `Multiset α`. -/
instance _root_.Multiset.countable [Countable α] : Countable (Multiset α) :=
  Quotient.countable

/-- If `α` is countable, then so is `Finset α`. -/
instance _root_.Finset.countable [Countable α] : Countable (Finset α) :=
  Finset.val_injective.countable

/-- A listable type with decidable equality is encodable. -/
def encodableOfList [DecidableEq α] (l : List α) (H : ∀ x, x ∈ l) : Encodable α :=
  ⟨fun a => idxOf a l, (l[·]?), fun _ => getElem?_idxOf (H _)⟩

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

end Encodable

namespace Denumerable

variable {α : Type*} {β : Type*} [Denumerable α] [Denumerable β]

open Encodable

section List

theorem denumerable_list_aux : ∀ n : ℕ, ∃ a ∈ @decodeList α _ n, encodeList a = n
  | 0 => by rw [decodeList]; exact ⟨_, rfl, rfl⟩
  | succ v => by
    rcases e : unpair v with ⟨v₁, v₂⟩
    have h := unpair_right_le v
    rw [e] at h
    rcases have : v₂ < succ v := lt_succ_of_le h
      denumerable_list_aux v₂ with
      ⟨a, h₁, h₂⟩
    rw [Option.mem_def] at h₁
    use ofNat α v₁ :: a
    simp [decodeList, e, h₂, h₁, encodeList, pair_eq_of_unpair_eq e]

/-- If `α` is denumerable, then so is `List α`. -/
instance denumerableList : Denumerable (List α) :=
  ⟨denumerable_list_aux⟩

@[simp]
theorem list_ofNat_zero : ofNat (List α) 0 = [] := by rw [← @encode_list_nil α, ofNat_encode]

@[simp]
theorem list_ofNat_succ (v : ℕ) :
    ofNat (List α) (succ v) = ofNat α v.unpair.1 :: ofNat (List α) v.unpair.2 :=
  ofNat_of_decode <|
    show decodeList (succ v) = _ by
      rcases e : unpair v with ⟨v₁, v₂⟩
      simp [decodeList, e]
      rw [show decodeList v₂ = decode (α := List α) v₂ from rfl, decode_eq_ofNat, Option.seq_some]

end List

end Denumerable

namespace Equiv

/-- A list on a unique type is equivalent to ℕ by sending each list to its length. -/
@[simps!]
def listUniqueEquiv (α : Type*) [Unique α] : List α ≃ ℕ where
  toFun := List.length
  invFun n := List.replicate n default
  left_inv u := List.length_injective (by simp)
  right_inv n := List.length_replicate

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
