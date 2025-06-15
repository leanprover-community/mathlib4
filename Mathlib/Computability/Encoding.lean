/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Num.Lemmas
import Mathlib.Data.Option.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Encodings

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `finEncodingNatBool`  : a binary encoding of ℕ in a simple alphabet.
- `finEncodingNatΓ'`    : a binary encoding of ℕ in the alphabet used for TM's.
- `unaryFinEncodingNat` : a unary encoding of ℕ
- `finEncodingBoolBool` : an encoding of bool.
-/


universe u v

open Cardinal

namespace Computability

/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure Encoding (α : Type u) where
  /-- The alphabet of the encoding -/
  Γ : Type v
  /-- The encoding function -/
  encode : α → List Γ
  /-- The decoding function -/
  decode : List Γ → Option α
  /-- Decoding and encoding are inverses of each other. -/
  decode_encode : ∀ x, decode (encode x) = some x

theorem Encoding.encode_injective {α : Type u} (e : Encoding α) : Function.Injective e.encode := by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode, ← e.decode_encode, h]

/-- An encoding plus a guarantee of finiteness of the alphabet. -/
structure FinEncoding (α : Type u) extends Encoding.{u, 0} α where
  /-- The alphabet of the encoding is finite -/
  ΓFin : Fintype Γ

instance Γ.fintype {α : Type u} (e : FinEncoding α) : Fintype e.toEncoding.Γ :=
  e.ΓFin

/-- A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma. -/
inductive Γ'
  | blank
  | bit (b : Bool)
  | bra
  | ket
  | comma
  deriving DecidableEq, Fintype

instance inhabitedΓ' : Inhabited Γ' :=
  ⟨Γ'.blank⟩

/-- The natural inclusion of bool in Γ'. -/
def inclusionBoolΓ' : Bool → Γ' :=
  Γ'.bit

/-- An arbitrary section of the natural inclusion of bool in Γ'. -/
def sectionΓ'Bool : Γ' → Bool
  | Γ'.bit b => b
  | _ => Inhabited.default

@[simp]
theorem sectionΓ'Bool_inclusionBoolΓ' {b} : sectionΓ'Bool (inclusionBoolΓ' b) = b := by
  cases b <;> rfl

@[deprecated sectionΓ'Bool_inclusionBoolΓ' (since := "2025-01-21")]
theorem leftInverse_section_inclusion : Function.LeftInverse sectionΓ'Bool inclusionBoolΓ' :=
  fun x => Bool.casesOn x rfl rfl

theorem inclusionBoolΓ'_injective : Function.Injective inclusionBoolΓ' :=
  Function.HasLeftInverse.injective ⟨_, (fun _ => sectionΓ'Bool_inclusionBoolΓ')⟩

/-- An encoding function of the positive binary numbers in bool. -/
def encodePosNum : PosNum → List Bool
  | PosNum.one    => [true]
  | PosNum.bit0 n => false :: encodePosNum n
  | PosNum.bit1 n => true :: encodePosNum n

/-- An encoding function of the binary numbers in bool. -/
def encodeNum : Num → List Bool
  | Num.zero => []
  | Num.pos n => encodePosNum n

/-- An encoding function of ℕ in bool. -/
def encodeNat (n : ℕ) : List Bool :=
  encodeNum n

/-- A decoding function from `List Bool` to the positive binary numbers. -/
def decodePosNum : List Bool → PosNum
  | false :: l => PosNum.bit0 (decodePosNum l)
  | true  :: l => ite (l = []) PosNum.one (PosNum.bit1 (decodePosNum l))
  | _          => PosNum.one

/-- A decoding function from `List Bool` to the binary numbers. -/
def decodeNum : List Bool → Num := fun l => ite (l = []) Num.zero <| decodePosNum l

/-- A decoding function from `List Bool` to ℕ. -/
def decodeNat : List Bool → Nat := fun l => decodeNum l

theorem encodePosNum_nonempty (n : PosNum) : encodePosNum n ≠ [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun _m => List.cons_ne_nil _ _) fun _m =>
    List.cons_ne_nil _ _

@[simp] theorem decode_encodePosNum : ∀ n, decodePosNum (encodePosNum n) = n := fun n ↦ by
  induction n with unfold encodePosNum decodePosNum
  | one => rfl
  | bit1 m hm =>
    rw [hm]
    exact if_neg (encodePosNum_nonempty m)
  | bit0 m hm => exact congr_arg PosNum.bit0 hm

@[simp] theorem decode_encodeNum : ∀ n, decodeNum (encodeNum n) = n := by
  intro n
  obtain - | n := n <;> unfold encodeNum decodeNum
  · rfl
  rw [decode_encodePosNum n]
  rw [PosNum.cast_to_num]
  exact if_neg (encodePosNum_nonempty n)

@[simp] theorem decode_encodeNat : ∀ n, decodeNat (encodeNat n) = n := by
  intro n
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg ((↑) : Num → ℕ) (decode_encodeNum n)

/-- A binary encoding of ℕ in bool. -/
def encodingNatBool : Encoding ℕ where
  Γ := Bool
  encode := encodeNat
  decode n := some (decodeNat n)
  decode_encode n := congr_arg _ (decode_encodeNat n)

/-- A binary fin_encoding of ℕ in bool. -/
def finEncodingNatBool : FinEncoding ℕ :=
  ⟨encodingNatBool, Bool.fintype⟩

/-- A binary encoding of ℕ in Γ'. -/
def encodingNatΓ' : Encoding ℕ where
  Γ := Γ'
  encode x := List.map inclusionBoolΓ' (encodeNat x)
  decode x := some (decodeNat (List.map sectionΓ'Bool x))
  decode_encode x := congr_arg _ <| by simp [Function.comp_def]

/-- A binary FinEncoding of ℕ in Γ'. -/
def finEncodingNatΓ' : FinEncoding ℕ :=
  ⟨encodingNatΓ', inferInstanceAs (Fintype Γ')⟩

/-- A unary encoding function of ℕ in bool. -/
def unaryEncodeNat : Nat → List Bool
  | 0 => []
  | n + 1 => true :: unaryEncodeNat n

/-- A unary decoding function from `List Bool` to ℕ. -/
def unaryDecodeNat : List Bool → Nat :=
  List.length

@[simp] theorem unary_decode_encode_nat : ∀ n, unaryDecodeNat (unaryEncodeNat n) = n := fun n =>
  Nat.rec rfl (fun (_m : ℕ) hm => (congr_arg Nat.succ hm.symm).symm) n

/-- A unary fin_encoding of ℕ. -/
def unaryFinEncodingNat : FinEncoding ℕ where
  Γ := Bool
  encode := unaryEncodeNat
  decode n := some (unaryDecodeNat n)
  decode_encode n := congr_arg _ (unary_decode_encode_nat n)
  ΓFin := Bool.fintype

/-- An encoding function of bool in bool. -/
def encodeBool : Bool → List Bool := pure

/-- A decoding function from `List Bool` to bool. -/
def decodeBool : List Bool → Bool
  | b :: _ => b
  | _ => Inhabited.default

@[simp] theorem decode_encodeBool (b : Bool) : decodeBool (encodeBool b) = b := rfl

/-- A fin_encoding of bool in bool. -/
def finEncodingBoolBool : FinEncoding Bool where
  Γ := Bool
  encode := encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)
  ΓFin := Bool.fintype

instance inhabitedFinEncoding : Inhabited (FinEncoding Bool) :=
  ⟨finEncodingBoolBool⟩

instance inhabitedEncoding : Inhabited (Encoding Bool) :=
  ⟨finEncodingBoolBool.toEncoding⟩

theorem Encoding.card_le_card_list {α : Type u} (e : Encoding.{u, v} α) :
    Cardinal.lift.{v} #α ≤ Cardinal.lift.{u} #(List e.Γ) :=
  Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩

theorem Encoding.card_le_aleph0 {α : Type u} (e : Encoding.{u, v} α) [Countable e.Γ] :
    #α ≤ ℵ₀ :=
  haveI : Countable α := e.encode_injective.countable
  Cardinal.mk_le_aleph0

theorem FinEncoding.card_le_aleph0 {α : Type u} (e : FinEncoding α) : #α ≤ ℵ₀ :=
  e.toEncoding.card_le_aleph0

end Computability
