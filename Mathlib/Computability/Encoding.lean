/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Num.Lemmas
import Mathlib.Data.Option.Basic
import Mathlib.SetTheory.Cardinal.Basic

#align_import computability.encoding from "leanprover-community/mathlib"@"b6395b3a5acd655b16385fa0cdbf1961d6c34b3e"

/-!
# Encodings

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `finEncodingNatBool`   : a binary encoding of ℕ in a simple alphabet.
- `finEncodingNatΓ'`    : a binary encoding of ℕ in the alphabet used for TM's.
- `unaryFinEncodingNat` : a unary encoding of ℕ
- `finEncodingBoolBool`  : an encoding of bool.
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

theorem Encoding.encode_injective {α : Type u} (e : Encoding α) : Function.Injective e.encode := by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode, ← e.decode_encode, h]
#align computability.encoding.encode_injective Computability.Encoding.encode_injective

/-- An encoding plus a guarantee of finiteness of the alphabet. -/
structure FinEncoding (α : Type u) extends Encoding.{u, 0} α where
  ΓFin : Fintype Γ
#align computability.fin_encoding Computability.FinEncoding

instance Γ.fintype {α : Type u} (e : FinEncoding α) : Fintype e.toEncoding.Γ :=
  e.ΓFin
#align computability.Γ.fintype Computability.Γ.fintype

/-- A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma. -/
inductive Γ'
  | blank
  | bit (b : Bool)
  | bra
  | ket
  | comma
  deriving DecidableEq
#align computability.Γ' Computability.Γ'

-- Porting note: A handler for `Fintype` had not been implemented yet.
instance Γ'.fintype : Fintype Γ' :=
  ⟨⟨{.blank, .bit true, .bit false, .bra, .ket, .comma}, by decide⟩,
    by intro; cases_type* Γ' Bool <;> decide⟩
#align computability.Γ'.fintype Computability.Γ'.fintype

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
  | _ => Inhabited.default
#align computability.section_Γ'_bool Computability.sectionΓ'Bool

theorem leftInverse_section_inclusion : Function.LeftInverse sectionΓ'Bool inclusionBoolΓ' :=
  fun x => Bool.casesOn x rfl rfl
#align computability.left_inverse_section_inclusion Computability.leftInverse_section_inclusion

theorem inclusionBoolΓ'_injective : Function.Injective inclusionBoolΓ' :=
  Function.HasLeftInverse.injective (Exists.intro sectionΓ'Bool leftInverse_section_inclusion)
#align computability.inclusion_bool_Γ'_injective Computability.inclusionBoolΓ'_injective

/-- An encoding function of the positive binary numbers in bool. -/
def encodePosNum : PosNum → List Bool
  | PosNum.one    => [true]
  | PosNum.bit0 n => false :: encodePosNum n
  | PosNum.bit1 n => true :: encodePosNum n
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

/-- A decoding function from `List Bool` to the positive binary numbers. -/
def decodePosNum : List Bool → PosNum
  | false :: l => PosNum.bit0 (decodePosNum l)
  | true  :: l => ite (l = []) PosNum.one (PosNum.bit1 (decodePosNum l))
  | _          => PosNum.one
#align computability.decode_pos_num Computability.decodePosNum

/-- A decoding function from `List Bool` to the binary numbers. -/
def decodeNum : List Bool → Num := fun l => ite (l = []) Num.zero <| decodePosNum l
#align computability.decode_num Computability.decodeNum

/-- A decoding function from `List Bool` to ℕ. -/
def decodeNat : List Bool → Nat := fun l => decodeNum l
#align computability.decode_nat Computability.decodeNat

theorem encodePosNum_nonempty (n : PosNum) : encodePosNum n ≠ [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun _m => List.cons_ne_nil _ _) fun _m =>
    List.cons_ne_nil _ _
#align computability.encode_pos_num_nonempty Computability.encodePosNum_nonempty

theorem decode_encodePosNum : ∀ n, decodePosNum (encodePosNum n) = n := by
  intro n
  induction' n with m hm m hm <;> unfold encodePosNum decodePosNum
  · rfl
  · rw [hm]
    exact if_neg (encodePosNum_nonempty m)
  · exact congr_arg PosNum.bit0 hm
#align computability.decode_encode_pos_num Computability.decode_encodePosNum

theorem decode_encodeNum : ∀ n, decodeNum (encodeNum n) = n := by
  intro n
  cases' n with n <;> unfold encodeNum decodeNum
  · rfl
  rw [decode_encodePosNum n]
  rw [PosNum.cast_to_num]
  exact if_neg (encodePosNum_nonempty n)
#align computability.decode_encode_num Computability.decode_encodeNum

theorem decode_encodeNat : ∀ n, decodeNat (encodeNat n) = n := by
  intro n
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg ((↑) : Num → ℕ) (decode_encodeNum n)
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
      -- Porting note: `rw` can't unify `g ∘ f` with `fun x => g (f x)`, used `LeftInverse.id`
      -- instead.
      rw [List.map_map, leftInverse_section_inclusion.id, List.map_id, decode_encodeNat]
#align computability.encoding_nat_Γ' Computability.encodingNatΓ'

/-- A binary fin_encoding of ℕ in Γ'. -/
def finEncodingNatΓ' : FinEncoding ℕ :=
  ⟨encodingNatΓ', Γ'.fintype⟩
#align computability.fin_encoding_nat_Γ' Computability.finEncodingNatΓ'

/-- A unary encoding function of ℕ in bool. -/
def unaryEncodeNat : Nat → List Bool
  | 0 => []
  | n + 1 => true :: unaryEncodeNat n
#align computability.unary_encode_nat Computability.unaryEncodeNat

/-- A unary decoding function from `List Bool` to ℕ. -/
def unaryDecodeNat : List Bool → Nat :=
  List.length
#align computability.unary_decode_nat Computability.unaryDecodeNat

theorem unary_decode_encode_nat : ∀ n, unaryDecodeNat (unaryEncodeNat n) = n := fun n =>
  Nat.rec rfl (fun (_m : ℕ) hm => (congr_arg Nat.succ hm.symm).symm) n
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
def encodeBool : Bool → List Bool := pure
#align computability.encode_bool Computability.encodeBool

/-- A decoding function from `List Bool` to bool. -/
def decodeBool : List Bool → Bool
  | b :: _ => b
  | _ => Inhabited.default
#align computability.decode_bool Computability.decodeBool

theorem decode_encodeBool (b : Bool) : decodeBool (encodeBool b) = b := rfl
#align computability.decode_encode_bool Computability.decode_encodeBool

/-- A fin_encoding of bool in bool. -/
def finEncodingBoolBool : FinEncoding Bool where
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
    Cardinal.lift.{v} #α ≤ Cardinal.lift.{u} #(List e.Γ) :=
  Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩
#align computability.encoding.card_le_card_list Computability.Encoding.card_le_card_list

theorem Encoding.card_le_aleph0 {α : Type u} (e : Encoding.{u, v} α) [Countable e.Γ] :
    #α ≤ ℵ₀ :=
  haveI : Countable α := e.encode_injective.countable
  Cardinal.mk_le_aleph0
#align computability.encoding.card_le_aleph_0 Computability.Encoding.card_le_aleph0

theorem FinEncoding.card_le_aleph0 {α : Type u} (e : FinEncoding α) : #α ≤ ℵ₀ :=
  e.toEncoding.card_le_aleph0
#align computability.fin_encoding.card_le_aleph_0 Computability.FinEncoding.card_le_aleph0

end Computability
