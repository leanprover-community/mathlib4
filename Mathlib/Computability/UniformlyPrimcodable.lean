/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito
-/

import Mathlib.Computability.Primrec

/-! # Lemmas about computability of dependent types -/

/-- A `UniformlyPrimcodable` type is an indexed `Primcodable` types, where each encoding is
 uniformly primitive recursive. -/
class UniformlyPrimcodable {α : Type*} (β : α → Type*)
    [Primcodable α] [(a : α) → Primcodable (β a)] : Prop where
  uniformly_prim : Primrec₂ fun a n ↦ Encodable.encode (Encodable.decode (α := β a) n)

namespace Encodable

variable {α : Type*} {P : α → Prop} [Encodable α] [DecidablePred P]

lemma encode_decode_subtype (e : ℕ) :
    encode (decode (α := {x // P x}) e) =
    encode ((decode (α := α) e).bind fun a ↦ if P a then some a else none) := by
  rcases h : decode (α := α) e with (_ | s) <;>
    simp [*, decode, decodeSubtype, encode, encodeSubtype]
  by_cases hs : P s <;> simp [hs]

/-- Result of mapping encode to the decoded value.-/
def encodeDecode (α : Type*) [Encodable α] (e : ℕ) : Option ℕ := (decode e : Option α).map encode

lemma encodeDecode_of_none {e : ℕ} (h : decode (α := α) e = none) :
    encodeDecode α e = none := by simp [encodeDecode, h]

lemma encodeDecode_of_some {e : ℕ} {a : α} (h : decode e = some a) :
    encodeDecode α e = some (encode a) := by simp [encodeDecode, h]

lemma decode_encodeDecode (e i : ℕ) : encodeDecode α e = some i → ∃ a : α, decode i = some a := by
  unfold encodeDecode
  cases (decode e : Option α) <;> simp
  rintro rfl; simp

end Encodable

namespace UniformlyPrimcodable

open Encodable Primcodable Primrec
variable {α : Type*} {β γ : α → Type*}
  [Primcodable α] [(a : α) → Primcodable (β a)] [(a : α) → Primcodable (γ a)]

lemma _root_.Primrec₂.encodeDecode [UniformlyPrimcodable β] :
    Primrec₂ fun a ↦ encodeDecode (β a) :=
  (to₂ <| nat_casesOn (UniformlyPrimcodable.uniformly_prim.comp fst snd)
    (const none) (option_some.comp₂ Primrec₂.right)).of_eq fun a n ↦ by
    unfold encodeDecode
    rcases decode n <;> simp

/-- `β` is `UniformlyPrimcodable` if the `encodeDecode` of `β` is primitive recursive.-/
def ofEncodeDecode (h : Primrec₂ fun a ↦ encodeDecode (β a)) :
    UniformlyPrimcodable β where
  uniformly_prim := (Primrec.encode.comp₂ h).of_eq fun a n ↦ by
    unfold encodeDecode
    rcases decode n <;> simp

protected instance const (α β : Type*) [Primcodable α] [Primcodable β] :
    UniformlyPrimcodable fun (_ : α) ↦ β where
  uniformly_prim := (nat_iff.mpr Primcodable.prim).comp snd

/-- A subtype is `UniformlyPrimcodable` if its characteristic function is primitive recursive.-/
def subtype {β : Type*} [Primcodable β] {R : α → β → Prop}
    [(a : α) → (b : β) → Decidable (R a b)] (hR : PrimrecRel R) :
    haveI : (a : α) → Primcodable { x // R a x } := fun a ↦
      Primcodable.subtype (hR.comp (Primrec.const a) Primrec.id)
    UniformlyPrimcodable fun a ↦ { x // R a x } :=
  have : Primrec₂ fun a e ↦
      encode ((decode e : Option β).bind fun b ↦ if R a b then some b else none) :=
    (Primrec.encode.comp <|
      option_bind (Primrec.decode.comp snd)
        (Primrec.ite (hR.comp (fst.comp fst) snd) (Primrec.option_some.comp snd) (const none)))
  @UniformlyPrimcodable.mk _ _ _ (fun a ↦ Primcodable.subtype (hR.comp (const a) Primrec.id))
    (this.of_eq fun a e ↦ by
      simp [decode, Primcodable.toEncodable, Primcodable.subtype, decodeSubtype]
      rcases (decode e) with (_ | b) <;> simp
      by_cases hr : R a b <;> simp [hr, Encodable.Subtype.encode_eq])

instance prod (β : α → Type*) (γ : α → Type*)
    [(a : α) → Primcodable (β a)] [(a : α) → Primcodable (γ a)]
    [UniformlyPrimcodable β] [UniformlyPrimcodable γ] :
    UniformlyPrimcodable fun a ↦ β a × γ a where
  uniformly_prim :=
    have : Primrec₂ (fun a e ↦
      encode ((encodeDecode (β a) e.unpair.1).bind fun b ↦
        (encodeDecode (γ a) e.unpair.2).map fun c ↦ b.pair c) : α → ℕ → ℕ) :=
      to₂ <| Primrec.encode.comp
        (Primrec.option_bind
          (to₂ <| Primrec₂.encodeDecode.comp fst (fst.comp <| Primrec.unpair.comp snd))
          (to₂ <| Primrec.option_map
            (Primrec₂.encodeDecode.comp
              (fst.comp fst)
              (snd.comp <| Primrec.unpair.comp <| snd.comp fst))
            (Primrec₂.natPair.comp₂ (snd.comp₂ Primrec₂.left) Primrec₂.right)))
    this.of_eq fun a e ↦ by
      simp only [decode_prod_val]
      rcases hb : (decode e.unpair.1 : Option (β a)) with (_ | b) <;>
        simp [*, encodeDecode_of_none, encodeDecode_of_some]
      rcases hc : (decode e.unpair.2 : Option (γ a)) with (_ | c) <;>
        simp [*, encodeDecode_of_none, encodeDecode_of_some hb]
      simp [encodeDecode_of_some hc]

instance vector (β : Type*) [Primcodable β] : UniformlyPrimcodable (Vector β) where
  uniformly_prim := by
    have e : ∀ n e,
        encode ((decode (α := List β) e).bind fun a ↦ if a.length = n then some a else none) =
        encode (decode (α := Vector β n) e) := by intro n e; rw [Encodable.encode_decode_subtype]
    have : Primrec₂ fun n e ↦
        encode ((decode (α := List β) e).bind fun a ↦ if a.length = n then some a else none) :=
      Primrec.encode.comp
        (Primrec.option_bind
          (Primrec.decode.comp snd)
          (Primrec.ite
            (Primrec.eq.comp (Primrec.list_length.comp snd) (fst.comp fst))
            (Primrec.option_some.comp snd)
            (const none)))
    exact this.of_eq e

instance fin : UniformlyPrimcodable Fin where
  uniformly_prim := by
    have : ∀ e n, encode (decode (α := Fin n) e) = if e < n then e + 1 else 0 := by
      intro e n
      by_cases h : e < n <;>
        simp [h, Encodable.decode_ofEquiv, decode, decodeSubtype,
          Encodable.encode_ofEquiv, encode, encodeSubtype]
    exact (Primrec.ite (Primrec.nat_lt.comp snd fst) (Primrec.succ.comp snd)
      (Primrec.const 0)).of_eq (by simp [this])

attribute [-instance] Encodable.finPi in
instance finArrow (β : Type*) [Primcodable β] : UniformlyPrimcodable (Fin · → β) where
  uniformly_prim := by
    have : ∀ n e, encode (decode (α := Vector β n) e) = encode (decode (α := Fin n → β) e) := by
      intro n e; simp [Encodable.decode_ofEquiv]
      rcases decode (α := Vector β n) e with (_ | v) <;> simp
      { have : ∀ b : Fin n → β, encode b = encode ((Equiv.vectorEquivFin β n).symm b) :=
          fun b ↦ encode_ofEquiv (Equiv.vectorEquivFin β n).symm b
        simpa using (this (Equiv.vectorEquivFin β n v)).symm }
    exact uniformly_prim.of_eq this

end UniformlyPrimcodable

namespace Primcodable

open Encodable UniformlyPrimcodable Primrec
variable {α : Type*} {β : α → Type*}
  [Primcodable α] [(a : α) → Primcodable (β a)] [UniformlyPrimcodable β]

instance sigma : Primcodable (Sigma β) where
  prim := by
    have p₁ : Primrec (fun e ↦ decode e.unpair.1 : ℕ → Option α) :=
      Primrec.decode.comp <| fst.comp Primrec.unpair
    have p₂ : Primrec₂ (fun e a ↦
        (encodeDecode (β a) e.unpair.2).map (Nat.pair (encode a)) : ℕ → α → Option ℕ) :=
      (Primrec.option_map
        (Primrec₂.encodeDecode.comp snd (snd.comp $ Primrec.unpair.comp $ fst))
        (Primrec₂.natPair.comp₂ (Primrec.encode.comp $ snd.comp $ fst) Primrec₂.right))
    exact Primrec.nat_iff.mp <| (Primrec.encode.comp $ p₁.option_bind p₂).of_eq (by
      intro e; simp
      rcases (decode e.unpair.1 : Option α) with (_ | a) <;> simp
      rcases hb : (decode e.unpair.2 : Option (β a)) with (_ | b) <;> simp [*, encodeDecode_of_none]
      simp [encodeDecode_of_some hb])

@[simp] lemma sigma_toEncodable_eq :
    (sigma : Primcodable (Sigma β)).toEncodable = Sigma.encodable := rfl

end Primcodable
