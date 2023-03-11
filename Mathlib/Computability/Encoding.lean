/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent

! This file was ported from Lean 3 source module computability.encoding
! leanprover-community/mathlib commit b6395b3a5acd655b16385fa0cdbf1961d6c34b3e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Num.Lemmas
import Mathbin.SetTheory.Cardinal.Ordinal
import Mathbin.Tactic.DeriveFintype

/-!
# Encodings

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `fin_encoding_nat_bool`   : a binary encoding of ℕ in a simple alphabet.
- `fin_encoding_nat_Γ'`    : a binary encoding of ℕ in the alphabet used for TM's.
- `unary_fin_encoding_nat` : a unary encoding of ℕ
- `fin_encoding_bool_bool`  : an encoding of bool.
-/


universe u v

open Cardinal

namespace Computability

/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure Encoding (α : Type u) where
  Γ : Type v
  encode : α → List Γ
  decode : List Γ → Option α
  decode_encode : ∀ x, decode (encode x) = some x
#align computability.encoding Computability.Encoding

theorem Encoding.encode_injective {α : Type u} (e : Encoding α) : Function.Injective e.encode :=
  by
  refine' fun _ _ h => Option.some_injective _ _
  rw [← e.decode_encode, ← e.decode_encode, h]
#align computability.encoding.encode_injective Computability.Encoding.encode_injective

/-- An encoding plus a guarantee of finiteness of the alphabet. -/
structure FinEncoding (α : Type u) extends Encoding.{u, 0} α where
  ΓFin : Fintype Γ
#align computability.fin_encoding Computability.FinEncoding

instance {α : Type u} (e : FinEncoding α) : Fintype e.toEncoding.Γ :=
  e.ΓFin

/-- A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma. -/
inductive Γ'
  | blank
  | bit (b : Bool)
  | bra
  | ket
  | comma
  deriving DecidableEq, Fintype
#align computability.Γ' Computability.Γ'

instance inhabitedΓ' : Inhabited Γ' :=
  ⟨Γ'.blank⟩
#align computability.inhabited_Γ' Computability.inhabitedΓ'

/-- The natural inclusion of bool in Γ'. -/
def inclusionBoolΓ' : Bool → Γ' :=
  Γ'.bit
#align computability.inclusion_bool_Γ' Computability.inclusionBoolΓ'

/-- An arbitrary section of the natural inclusion of bool in Γ'. -/
def sectionΓ'Bool : Γ' → Bool
  | Γ'.bit b => b
  | _ => Inhabited.default Bool
#align computability.section_Γ'_bool Computability.sectionΓ'Bool

theorem leftInverse_section_inclusion : Function.LeftInverse sectionΓ'Bool inclusionBoolΓ' :=
  fun x => Bool.casesOn x rfl rfl
#align computability.left_inverse_section_inclusion Computability.leftInverse_section_inclusion

theorem inclusionBoolΓ'_injective : Function.Injective inclusionBoolΓ' :=
  Function.HasLeftInverse.injective (Exists.intro sectionΓ'Bool leftInverse_section_inclusion)
#align computability.inclusion_bool_Γ'_injective Computability.inclusionBoolΓ'_injective

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- An encoding function of the positive binary numbers in bool. -/
def encodePosNum : PosNum → List Bool
  | PosNum.one => [true]
  | PosNum.bit0 n => false::encode_pos_num n
  | PosNum.bit1 n => true::encode_pos_num n
#align computability.encode_pos_num Computability.encodePosNum

/-- An encoding function of the binary numbers in bool. -/
def encodeNum : Num → List Bool
  | Num.zero => []
  | Num.pos n => encodePosNum n
#align computability.encode_num Computability.encodeNum

/-- An encoding function of ℕ in bool. -/
def encodeNat (n : ℕ) : List Bool :=
  encodeNum n
#align computability.encode_nat Computability.encodeNat

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A decoding function from `list bool` to the positive binary numbers. -/
def decodePosNum : List Bool → PosNum
  | ff::l => PosNum.bit0 (decode_pos_num l)
  | tt::l => ite (l = []) PosNum.one (PosNum.bit1 (decode_pos_num l))
  | _ => PosNum.one
#align computability.decode_pos_num Computability.decodePosNum

/-- A decoding function from `list bool` to the binary numbers. -/
def decodeNum : List Bool → Num := fun l => ite (l = []) Num.zero <| decodePosNum l
#align computability.decode_num Computability.decodeNum

/-- A decoding function from `list bool` to ℕ. -/
def decodeNat : List Bool → Nat := fun l => decodeNum l
#align computability.decode_nat Computability.decodeNat

theorem encodePosNum_nonempty (n : PosNum) : encodePosNum n ≠ [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun m => List.cons_ne_nil _ _) fun m =>
    List.cons_ne_nil _ _
#align computability.encode_pos_num_nonempty Computability.encodePosNum_nonempty

theorem decode_encodePosNum : ∀ n, decodePosNum (encodePosNum n) = n :=
  by
  intro n
  induction' n with m hm m hm <;> unfold encode_pos_num decode_pos_num
  · rfl
  · rw [hm]
    exact if_neg (encode_pos_num_nonempty m)
  · exact congr_arg PosNum.bit0 hm
#align computability.decode_encode_pos_num Computability.decode_encodePosNum

theorem decode_encodeNum : ∀ n, decodeNum (encodeNum n) = n :=
  by
  intro n
  cases n <;> unfold encode_num decode_num
  · rfl
  rw [decode_encode_pos_num n]
  rw [PosNum.cast_to_num]
  exact if_neg (encode_pos_num_nonempty n)
#align computability.decode_encode_num Computability.decode_encodeNum

theorem decode_encodeNat : ∀ n, decodeNat (encodeNat n) = n :=
  by
  intro n
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg coe (decode_encode_num ↑n)
#align computability.decode_encode_nat Computability.decode_encodeNat

/-- A binary encoding of ℕ in bool. -/
def encodingNatBool : Encoding ℕ where
  Γ := Bool
  encode := encodeNat
  decode n := some (decodeNat n)
  decode_encode n := congr_arg _ (decode_encodeNat n)
#align computability.encoding_nat_bool Computability.encodingNatBool

/-- A binary fin_encoding of ℕ in bool. -/
def finEncodingNatBool : FinEncoding ℕ :=
  ⟨encodingNatBool, Bool.fintype⟩
#align computability.fin_encoding_nat_bool Computability.finEncodingNatBool

/-- A binary encoding of ℕ in Γ'. -/
def encodingNatΓ' : Encoding ℕ where
  Γ := Γ'
  encode x := List.map inclusionBoolΓ' (encodeNat x)
  decode x := some (decodeNat (List.map sectionΓ'Bool x))
  decode_encode x :=
    congr_arg _ <| by
      rw [List.map_map, List.map_id' left_inverse_section_inclusion, decode_encode_nat]
#align computability.encoding_nat_Γ' Computability.encodingNatΓ'

/-- A binary fin_encoding of ℕ in Γ'. -/
def finEncodingNatΓ' : FinEncoding ℕ :=
  ⟨encodingNatΓ', Γ'.fintype⟩
#align computability.fin_encoding_nat_Γ' Computability.finEncodingNatΓ'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A unary encoding function of ℕ in bool. -/
def unaryEncodeNat : Nat → List Bool
  | 0 => []
  | n + 1 => true::unary_encode_nat n
#align computability.unary_encode_nat Computability.unaryEncodeNat

/-- A unary decoding function from `list bool` to ℕ. -/
def unaryDecodeNat : List Bool → Nat :=
  List.length
#align computability.unary_decode_nat Computability.unaryDecodeNat

theorem unary_decode_encode_nat : ∀ n, unaryDecodeNat (unaryEncodeNat n) = n := fun n =>
  Nat.rec rfl (fun (m : ℕ) hm => (congr_arg Nat.succ hm.symm).symm) n
#align computability.unary_decode_encode_nat Computability.unary_decode_encode_nat

/-- A unary fin_encoding of ℕ. -/
def unaryFinEncodingNat : FinEncoding ℕ where
  Γ := Bool
  encode := unaryEncodeNat
  decode n := some (unaryDecodeNat n)
  decode_encode n := congr_arg _ (unary_decode_encode_nat n)
  ΓFin := Bool.fintype
#align computability.unary_fin_encoding_nat Computability.unaryFinEncodingNat

/-- An encoding function of bool in bool. -/
def encodeBool : Bool → List Bool :=
  List.ret
#align computability.encode_bool Computability.encodeBool

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A decoding function from `list bool` to bool. -/
def decodeBool : List Bool → Bool
  | b::_ => b
  | _ => Inhabited.default Bool
#align computability.decode_bool Computability.decodeBool

theorem decode_encodeBool : ∀ b, decodeBool (encodeBool b) = b := fun b => Bool.casesOn b rfl rfl
#align computability.decode_encode_bool Computability.decode_encodeBool

/-- A fin_encoding of bool in bool. -/
def finEncodingBoolBool : FinEncoding Bool
    where
  Γ := Bool
  encode := encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)
  ΓFin := Bool.fintype
#align computability.fin_encoding_bool_bool Computability.finEncodingBoolBool

instance inhabitedFinEncoding : Inhabited (FinEncoding Bool) :=
  ⟨finEncodingBoolBool⟩
#align computability.inhabited_fin_encoding Computability.inhabitedFinEncoding

instance inhabitedEncoding : Inhabited (Encoding Bool) :=
  ⟨finEncodingBoolBool.toEncoding⟩
#align computability.inhabited_encoding Computability.inhabitedEncoding

theorem Encoding.card_le_card_list {α : Type u} (e : Encoding.{u, v} α) :
    Cardinal.lift.{v} (#α) ≤ Cardinal.lift.{u} (#List e.Γ) :=
  Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩
#align computability.encoding.card_le_card_list Computability.Encoding.card_le_card_list

theorem Encoding.card_le_aleph0 {α : Type u} (e : Encoding.{u, v} α) [Encodable e.Γ] : (#α) ≤ ℵ₀ :=
  by
  refine' Cardinal.lift_le.1 (e.card_le_card_list.trans _)
  simp only [Cardinal.lift_aleph0, Cardinal.lift_le_aleph0]
  cases' isEmpty_or_nonempty e.Γ with h h
  · simp only [Cardinal.mk_le_aleph0]
  · rw [Cardinal.mk_list_eq_aleph0]
#align computability.encoding.card_le_aleph_0 Computability.Encoding.card_le_aleph0

theorem FinEncoding.card_le_aleph0 {α : Type u} (e : FinEncoding α) : (#α) ≤ ℵ₀ :=
  haveI : Encodable e.Γ := Fintype.toEncodable _
  e.to_encoding.card_le_aleph_0
#align computability.fin_encoding.card_le_aleph_0 Computability.FinEncoding.card_le_aleph0

end Computability

