/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Num.Lemmas
public import Mathlib.Data.Option.Basic
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# EncodingTos

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
This version parametrizes over the alphabet
-/

@[expose] public section


universe u v

open Cardinal

namespace Computability

/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure EncodingTo (α : Type u) (Γ : Type v) where
  /-- The encoding function -/
  encode : α → List Γ
  /-- The decoding function -/
  decode : List Γ → Option α
  /-- Decoding and encoding are inverses of each other. -/
  decode_encode : ∀ x, decode (encode x) = some x

theorem EncodingTo.encode_injective {α : Type u} {Γ : Type v} (e : EncodingTo α Γ) : Function.Injective e.encode := by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode, ← e.decode_encode, h]

/-- An encoding plus a guarantee of finiteness of the alphabet. -/
structure FinEncodingTo (α : Type u) (Γ : Type 0) extends EncodingTo.{u, 0} α Γ where
  /-- The alphabet of the encoding is finite -/
  ΓFin : Fintype Γ

instance Γ.fintype {α : Type u} {Γ : Type 0} (e : FinEncodingTo α Γ) : Fintype Γ :=
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

theorem inclusionBoolΓ'_injective : Function.Injective inclusionBoolΓ' :=
  Function.HasLeftInverse.injective ⟨_, (fun _ => sectionΓ'Bool_inclusionBoolΓ')⟩

/-- An encoding function of the positive binary numbers in bool. -/
def encodePosNum : PosNum → List Bool
  | PosNum.one => [true]
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
  | _ => PosNum.one

/-- A decoding function from `List Bool` to the binary numbers. -/
def decodeNum : List Bool → Num := fun l => ite (l = []) Num.zero <| decodePosNum l

/-- A decoding function from `List Bool` to ℕ. -/
def decodeNat : List Bool → Nat := fun l => decodeNum l

theorem encodePosNum_nonempty (n : PosNum) : encodePosNum n ≠ [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun _m => List.cons_ne_nil _ _) fun _m =>
    List.cons_ne_nil _ _

@[simp] theorem decode_encodePosNum (n) : decodePosNum (encodePosNum n) = n := by
  induction n with unfold encodePosNum decodePosNum
  | one => rfl
  | bit1 m hm =>
    rw [hm]
    exact if_neg (encodePosNum_nonempty m)
  | bit0 m hm => exact congr_arg PosNum.bit0 hm

@[simp] theorem decode_encodeNum (n) : decodeNum (encodeNum n) = n := by
  obtain - | n := n <;> unfold encodeNum decodeNum
  · rfl
  rw [decode_encodePosNum n]
  rw [PosNum.cast_to_num]
  exact if_neg (encodePosNum_nonempty n)

@[simp] theorem decode_encodeNat (n) : decodeNat (encodeNat n) = n := by
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg ((↑) : Num → ℕ) (decode_encodeNum n)

/-- A binary encoding of ℕ in bool. -/
def encodingNatBool : EncodingTo ℕ Bool where
  encode := encodeNat
  decode n := some (decodeNat n)
  decode_encode n := congr_arg _ (decode_encodeNat n)

/-- A binary fin_encoding of ℕ in bool. -/
def finEncodingToNatBool : FinEncodingTo ℕ Bool :=
  ⟨encodingNatBool, Bool.fintype⟩

/-- A binary encoding of ℕ in Γ'. -/
def encodingNatΓ' : EncodingTo ℕ Γ' where
  encode x := List.map inclusionBoolΓ' (encodeNat x)
  decode x := some (decodeNat (List.map sectionΓ'Bool x))
  decode_encode x := congr_arg _ <| by simp [Function.comp_def]

/-- A binary FinEncodingTo of ℕ in Γ'. -/
def finEncodingToNatΓ' : FinEncodingTo ℕ Γ' :=
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
def unaryFinEncodingToNat : FinEncodingTo ℕ Bool where
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
def finEncodingToBoolBool : FinEncodingTo Bool Bool where
  encode := encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)
  ΓFin := Bool.fintype

instance inhabitedFinEncodingTo : Inhabited (FinEncodingTo Bool Bool) :=
  ⟨finEncodingToBoolBool⟩

instance inhabitedEncodingTo : Inhabited (EncodingTo Bool Bool) :=
  ⟨finEncodingToBoolBool.toEncodingTo⟩

end Computability
