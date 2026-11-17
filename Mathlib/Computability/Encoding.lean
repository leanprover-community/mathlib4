/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
module

public import Mathlib.Data.Num.Lemmas
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Encodings

This file contains the definition of an encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `encodingNatBool`  : a binary encoding of `ℕ` in a simple alphabet.
- `encodingNatΓ'`    : a binary encoding of `ℕ` in the alphabet used for TM's.
- `unaryEncodingNat` : a unary encoding of `ℕ`
- `encodingBoolBool` : an encoding of `Bool`.
- `encodingList`     : an encoding of `List α` in the alphabet `α`.
- `encodingProd`     : an encoding of `α × β` from encodings of `α` and `β`.
-/

@[expose] public section

universe u v

open Cardinal

namespace Computability

/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure Encoding (α : Type u) (Γ : Type v) where
  /-- The encoding function -/
  encode : α → List Γ
  /-- The decoding function -/
  decode : List Γ → Option α
  /-- Decoding and encoding are inverses of each other. -/
  decode_encode : ∀ x, decode (encode x) = some x

attribute [simp] Encoding.decode_encode

theorem Encoding.encode_injective {α Γ} (e : Encoding α Γ) : Function.Injective e.encode := by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode, ← e.decode_encode, h]

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

/-- The natural inclusion of `Bool` in `Γ'`. -/
def inclusionBoolΓ' : Bool → Γ' :=
  Γ'.bit

/-- An arbitrary section of the natural inclusion of `Bool` in `Γ'`. -/
def sectionΓ'Bool : Γ' → Bool
  | Γ'.bit b => b
  | _ => Inhabited.default

@[simp]
theorem sectionΓ'Bool_inclusionBoolΓ' {b} : sectionΓ'Bool (inclusionBoolΓ' b) = b := by
  cases b <;> rfl

theorem inclusionBoolΓ'_injective : Function.Injective inclusionBoolΓ' :=
  Function.HasLeftInverse.injective ⟨_, (fun _ => sectionΓ'Bool_inclusionBoolΓ')⟩

/-- An encoding function of the positive binary numbers in `Bool`. -/
def encodePosNum : PosNum → List Bool
  | PosNum.one => [true]
  | PosNum.bit0 n => false :: encodePosNum n
  | PosNum.bit1 n => true :: encodePosNum n

/-- An encoding function of the binary numbers in `Bool`. -/
def encodeNum : Num → List Bool
  | Num.zero => []
  | Num.pos n => encodePosNum n

/-- An encoding function of `ℕ` in `Bool`. -/
def encodeNat (n : ℕ) : List Bool :=
  encodeNum n

/-- A decoding function from `List Bool` to the positive binary numbers. -/
def decodePosNum : List Bool → PosNum
  | false :: l => PosNum.bit0 (decodePosNum l)
  | true  :: l => ite (l = []) PosNum.one (PosNum.bit1 (decodePosNum l))
  | _ => PosNum.one

/-- A decoding function from `List Bool` to the binary numbers. -/
def decodeNum : List Bool → Num := fun l => ite (l = []) Num.zero <| decodePosNum l

/-- A decoding function from `List Bool` to `ℕ`. -/
def decodeNat : List Bool → Nat := fun l => decodeNum l

theorem encodePosNum_nonempty (n : PosNum) : encodePosNum n ≠ [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun _m => List.cons_ne_nil _ _) fun _m =>
    List.cons_ne_nil _ _

@[simp] theorem decode_encodePosNum (n) : decodePosNum (encodePosNum n) = n := by
  induction n with unfold encodePosNum decodePosNum
  | one => rfl
  | bit1 m hm =>
    rw [hm]
    exact ite_eq_right (encodePosNum_nonempty m)
  | bit0 m hm => congrm PosNum.bit0 $hm

@[simp] theorem decode_encodeNum (n) : decodeNum (encodeNum n) = n := by
  obtain - | n := n <;> unfold encodeNum decodeNum
  · rfl
  rw [decode_encodePosNum n]
  rw [PosNum.cast_to_num]
  exact ite_eq_right (encodePosNum_nonempty n)

@[simp] theorem decode_encodeNat (n) : decodeNat (encodeNat n) = n := by
  conv_rhs => rw [← Num.to_of_nat n]
  congrm $(decode_encodeNum n)

/-- A binary `Encoding` of `ℕ` in `Bool`. -/
def encodingNatBool : Encoding ℕ Bool where
  encode := encodeNat
  decode n := some (decodeNat n)
  decode_encode n := congr_arg _ (decode_encodeNat n)

/-- A binary `Encoding` of `ℕ` in `Γ'`. -/
def encodingNatΓ' : Encoding ℕ Γ' where
  encode x := List.map inclusionBoolΓ' (encodeNat x)
  decode x := some (decodeNat (List.map sectionΓ'Bool x))
  decode_encode x := congr_arg _ <| by simp [Function.comp_def]

/-- A unary encoding function of `ℕ` in `Bool`. -/
def unaryEncodeNat : Nat → List Bool
  | 0 => []
  | n + 1 => true :: unaryEncodeNat n

/-- A unary decoding function from `List Bool` to `ℕ`. -/
def unaryDecodeNat : List Bool → Nat :=
  List.length

@[simp] theorem unary_decode_encode_nat : ∀ n, unaryDecodeNat (unaryEncodeNat n) = n := fun n =>
  Nat.rec rfl (fun (_m : ℕ) hm => congr($(hm.symm).succ).symm) n

/-- A unary `Encoding` of `ℕ` in `Bool`. -/
def unaryEncodingNat : Encoding ℕ Bool where
  encode := unaryEncodeNat
  decode n := some (unaryDecodeNat n)
  decode_encode n := congr_arg _ (unary_decode_encode_nat n)

/-- An encoding function of `Bool` in `Bool`. -/
def encodeBool : Bool → List Bool := pure

/-- A decoding function from `List Bool` to `Bool`. -/
def decodeBool : List Bool → Bool
  | b :: _ => b
  | _ => Inhabited.default

@[simp] theorem decode_encodeBool (b : Bool) : decodeBool (encodeBool b) = b := rfl

/-- An `Encoding` of `Bool` in `Bool`. -/
def encodingBoolBool : Encoding Bool Bool where
  encode := encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)

instance inhabitedEncoding : Inhabited (Encoding Bool Bool) :=
  ⟨encodingBoolBool⟩

theorem Encoding.card_le_card_list {α : Type u} {Γ : Type v} (e : Encoding α Γ) :
    Cardinal.lift.{v} #α ≤ Cardinal.lift.{u} #(List Γ) :=
  Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩

theorem Encoding.card_le_aleph0 {α Γ} (e : Encoding α Γ) [Countable Γ] :
    #α ≤ ℵ₀ :=
  haveI : Countable α := e.encode_injective.countable
  Cardinal.mk_le_aleph0

/-- An `Encoding` of a `List α` in alphabet `α`, encoded directly. -/
def encodingList (α : Type) : Encoding (List α) α where
  encode := id
  decode := Option.some
  decode_encode _ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Given an `Encoding` of `α` and `β`,
constructs an `Encoding` of `α × β` by concatenating the encodings,
mapping the symbols from the first encoding with `Sum.inl`
and those from the second with `Sum.inr`.
-/
def encodingProd {α β Γ₁ Γ₂ : Type*} (ea : Encoding α Γ₁) (eb : Encoding β Γ₂) :
    Encoding (α × β) (Γ₁ ⊕ Γ₂) where
  encode x := (ea.encode x.1).map .inl ++ (eb.encode x.2).map .inr
  decode x := Option.map₂ Prod.mk (ea.decode (x.filterMap Sum.getLeft?))
      (eb.decode (x.filterMap Sum.getRight?))
  decode_encode x := by simp

/-! ### Deprecated aliases for `FinEncoding` and unbundled `Γ` -/

end Computability
