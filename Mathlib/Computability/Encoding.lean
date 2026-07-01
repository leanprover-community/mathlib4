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
# Encodings

This file contains the definition of an encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `encodingNatBool`  : a binary encoding of `ℕ` in a simple alphabet.
- `encodingNatΓ'`    : a binary encoding of `ℕ` in the alphabet used for TM's.
- `unaryEncodingNat` : a unary encoding of `ℕ`
- `unaryPrefixEncodingNat` : a self-delimiting unary encoding of `ℕ`
- `encodingBoolBool` : an encoding of `Bool`.
- `encodingList`     : an encoding of `List α` in the alphabet `α`.
- `encodingProd`     : an encoding of `α × β` from encodings of `α` and `β`.
- `encodingProdBool` : a self-delimiting encoding of `α × β` in the alphabet `Bool`.
- `encodingListBool` : a self-delimiting encoding of `List α` in the alphabet `Bool`.
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
  Nat.rec rfl (fun (_m : ℕ) hm => (congr_arg Nat.succ hm.symm).symm) n

/-- A unary `Encoding` of `ℕ` in `Bool`. -/
def unaryEncodingNat : Encoding ℕ Bool where
  encode := unaryEncodeNat
  decode n := some (unaryDecodeNat n)
  decode_encode n := congr_arg _ (unary_decode_encode_nat n)

/-! ### Unary Prefix Coding -/

namespace UnaryPrefix

/--
A self-delimiting unary prefix encoding of `ℕ` in `Bool`.
Encodes `n` as `n` `true`s followed by a `false`.
-/
def encode (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

@[simp]
lemma length_encode (n : ℕ) : (encode n).length = n + 1 := by
  simp [encode]

@[simp]
lemma length_takeWhile_encode (n : ℕ) (p : List Bool) :
    ((encode n ++ p).takeWhile id).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

/--
Encodes a pair of boolean lists by prefixing the length of the first component.
The second component is the remaining suffix.
-/
def pair (x y : List Bool) : List Bool :=
  encode x.length ++ x ++ y

/-- Splits a boolean list using the first component length encoded by `encode`. -/
def unpair (x : List Bool) : List Bool × List Bool :=
  let n := (x.takeWhile id).length
  let l := x.drop (n + 1)
  (l.take n, l.drop n)

@[simp]
theorem unpair_pair (x y : List Bool) : unpair (pair x y) = (x, y) := by
  simp [unpair, pair]

end UnaryPrefix

/-- A self-delimiting unary `Encoding` of `ℕ` in `Bool`. -/
def unaryPrefixEncodingNat : Encoding ℕ Bool where
  encode := UnaryPrefix.encode
  decode l := some ((l.takeWhile id).length)
  decode_encode n := by
    simpa using UnaryPrefix.length_takeWhile_encode n []

/--
A self-delimiting encoding of a product type in the alphabet `Bool`, built from
encodings of the two factors in `Bool`.
-/
def encodingProdBool {α β : Type*} (ea : Encoding α Bool) (eb : Encoding β Bool) :
    Encoding (α × β) Bool where
  encode x := UnaryPrefix.pair (ea.encode x.1) (eb.encode x.2)
  decode x :=
    let p := UnaryPrefix.unpair x
    Option.map₂ Prod.mk (ea.decode p.1) (eb.decode p.2)
  decode_encode x := by
    simp [UnaryPrefix.unpair, UnaryPrefix.pair]

namespace EncodingListBool

/-- Auxiliary encoder for `encodingListBool`, without the outer list-length prefix. -/
def encodeAux {α : Type*} (e : Encoding α Bool) : List α → List Bool
  | [] => []
  | x :: xs => UnaryPrefix.pair (e.encode x) (encodeAux e xs)

/-- Auxiliary decoder for `encodingListBool`, reading the given number of entries. -/
def decodeAux {α : Type*} (e : Encoding α Bool) : ℕ → List Bool → Option (List α)
  | 0, _ => some []
  | n + 1, xs =>
    let p := UnaryPrefix.unpair xs
    Option.map₂ List.cons (e.decode p.1) (decodeAux e n p.2)

@[simp]
theorem decodeAux_encodeAux {α : Type*} (e : Encoding α Bool) :
    ∀ xs : List α, decodeAux e xs.length (encodeAux e xs) = some xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [encodeAux, decodeAux, UnaryPrefix.unpair, UnaryPrefix.pair, ih]

end EncodingListBool

/-- A self-delimiting encoding of lists in the alphabet `Bool`. -/
def encodingListBool {α : Type*} (e : Encoding α Bool) : Encoding (List α) Bool where
  encode xs := UnaryPrefix.encode xs.length ++ EncodingListBool.encodeAux e xs
  decode xs :=
    let n := (xs.takeWhile id).length
    EncodingListBool.decodeAux e n (xs.drop (n + 1))
  decode_encode xs := by
    simp [EncodingListBool.decodeAux_encodeAux]

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

/-- Deprecated: Use `Encoding α Γ` along with `[Fintype Γ]` instead. -/
@[reducible, nolint unusedArguments,
  deprecated "Use `Encoding α Γ` along with `[Fintype Γ]` instead" (since := "2026-05-07")]
def FinEncoding (α : Type u) {Γ : Type v} [Fintype Γ] := Encoding α Γ

/-- Deprecated: `Γ` is now an explicit parameter of `Encoding`. -/
@[reducible, nolint unusedArguments,
  deprecated "Γ is now an explicit parameter of `Encoding`" (since := "2026-05-07")]
def Encoding.Γ {α : Type u} {Γ : Type v} (_ : Encoding α Γ) : Type v := Γ

/-- Deprecated: Use `inferInstanceAs (Fintype Γ)` instead. -/
@[reducible, nolint unusedArguments,
  deprecated "Use `inferInstanceAs (Fintype Γ)` instead" (since := "2026-05-07")]
def FinEncoding.ΓFin {α : Type u} {Γ : Type v} [h : Fintype Γ]
    (_ : Encoding α Γ) : Fintype Γ := h

/-- Deprecated: Use the encoding directly. -/
@[reducible, nolint unusedArguments,
  deprecated "Use the encoding directly" (since := "2026-05-07")]
def FinEncoding.toEncoding {α : Type u} {Γ : Type v} [Fintype Γ]
    (e : Encoding α Γ) : Encoding α Γ := e

/-- Deprecated alias for `encodingNatBool`. -/
@[deprecated encodingNatBool (since := "2026-05-07")]
abbrev finEncodingNatBool := encodingNatBool

/-- Deprecated alias for `encodingNatΓ'`. -/
@[deprecated encodingNatΓ' (since := "2026-05-07")]
abbrev finEncodingNatΓ' := encodingNatΓ'

/-- Deprecated alias for `unaryEncodingNat`. -/
@[deprecated unaryEncodingNat (since := "2026-05-07")]
abbrev unaryFinEncodingNat := unaryEncodingNat

/-- Deprecated alias for `encodingBoolBool`. -/
@[deprecated encodingBoolBool (since := "2026-05-07")]
abbrev finEncodingBoolBool := encodingBoolBool

/-- Deprecated alias for `encodingList`. -/
@[reducible, nolint unusedArguments,
  deprecated encodingList (since := "2026-05-07")]
def finEncodingList (α : Type) [Fintype α] := encodingList α

/-- Deprecated alias for `encodingProd`. -/
@[reducible, nolint unusedArguments,
  deprecated encodingProd (since := "2026-05-07")]
def finEncodingPair {α β Γ₁ Γ₂ : Type*} [Fintype Γ₁] [Fintype Γ₂]
    (ea : Encoding α Γ₁) (eb : Encoding β Γ₂) :=
  encodingProd ea eb

/-- Deprecated alias for `Encoding.card_le_aleph0`. -/
@[deprecated Encoding.card_le_aleph0 (since := "2026-05-07")]
theorem FinEncoding.card_le_aleph0 {α Γ} [Countable Γ] (e : Encoding α Γ) : #α ≤ ℵ₀ :=
  e.card_le_aleph0

end Computability
