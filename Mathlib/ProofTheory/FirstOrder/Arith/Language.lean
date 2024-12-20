/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.ModelTheory.Basic
import Mathlib.Computability.Primrec

/-!
# Language of first-order logic of arithmetic

This file defines the language of first-order logic of arithmetic.

- `FirstOrder.Language.oRing`, `ℒₒᵣ` is the language of ordered ring.
-/

namespace FirstOrder.Language

open Primrec

namespace ORing

/-- Arity of functions -/
inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | add : Func 2
  | mul : Func 2

/-- Arity of relations -/
inductive Rel : ℕ → Type
  | eq : Rel 2
  | lt : Rel 2

end ORing

/-- Definition of `oRing` language -/
@[reducible]
def oRing : Language := ⟨ORing.Func, ORing.Rel⟩

/-- Notation for `oRing` -/
notation "ℒₒᵣ" => oRing

namespace ORing

instance (k) : DecidableEq (oRing.Functions k) := fun a b ↦ by
  rcases a <;> rcases b <;> simp <;> exact inferInstance

instance (k) : DecidableEq (oRing.Relations k) := fun a b ↦ by
  rcases a <;> rcases b <;> simp <;> exact inferInstance

instance (k) : Encodable (oRing.Functions k) where
  encode := fun x =>
    match x with
    | Func.zero => 0
    | Func.one  => 1
    | Func.add  => 0
    | Func.mul  => 1
  decode := fun e =>
    match k, e with
    | 0, 0 => some Func.zero
    | 0, 1 => some Func.one
    | 2, 0 => some Func.add
    | 2, 1 => some Func.mul
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance Func1IsEmpty : IsEmpty (oRing.Functions 1) := ⟨by rintro ⟨⟩⟩

instance FuncGe3IsEmpty : ∀ (k : ℕ ), k ≥ 3 → IsEmpty (oRing.Functions k)
  | 0       => by simp
  | 1       => by simp [show ¬3 ≤ 1 from of_decide_eq_false rfl]
  | 2       => by simp [show ¬3 ≤ 2 from of_decide_eq_false rfl]
  | (n + 3) => fun _ => ⟨by rintro ⟨⟩⟩

private lemma Func_encodeDecode_primrec : Primrec₂ (fun k e =>
  if k = 0 ∧ e = 0 then some 0
  else if k = 0 ∧ e = 1 then some 1
  else if k = 2 ∧ e = 0 then some 0
  else if k = 2 ∧ e = 1 then some 1
  else none) :=
  to₂ <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _))
        (Primrec.eq.comp snd (const _))) (const _)
      <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _))
        (Primrec.eq.comp snd (const _))) (const _)
      <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _))
        (Primrec.eq.comp snd (const _))) (const _)
      <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _))
        (Primrec.eq.comp snd (const _))) (const _)
      <| const _

instance (k) : Primcodable (oRing.Functions k) where
  prim := nat_iff.mp <| (Primrec.encode.comp (Func_encodeDecode_primrec.comp (Primrec.const k)
      Primrec.id)).of_eq (fun e => by
    simp[Encodable.decode]
    rcases k with (_ | k)
    · rcases e with (_ | e) <;> simp
      · rfl
      · rcases e with (_ | e) <;> simp
        · rfl
    · rcases k with (_ | k) <;> simp
      · rcases k with (_ | k) <;> simp
        · rcases e with (_ | e) <;> simp
          · rfl
          · rcases e with (_ | e) <;> simp
            · rfl)

/-
instance : UniformlyPrimcodable oRing.Functions := UniformlyPrimcodable.ofEncodeDecode
  (Func_encodeDecode_primrec.of_eq $ fun k e => by
    simp[Encodable.encodeDecode, Encodable.decode]
    rcases k with (_ | k)
    · rcases e with (_ | e) <;> simp
      ·rfl
      · rcases e with (_ | e) <;> simp
        · rfl
    · rcases k with (_ | k) <;> simp
      · rcases k with (_ | k) <;> simp
        · rcases e with (_ | e) <;> simp
          · rfl
          · rcases e with (_ | e) <;> simp
            · rfl)
-/

instance (k) : Encodable (oRing.Relations k) where
  encode := fun x =>
    match x with
    | Rel.eq => 0
    | Rel.lt => 1
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | 2, 1 => some Rel.lt
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

private lemma Rel_encodeDecode_primrec : Primrec₂ (fun k e =>
  if k = 2 ∧ e = 0 then some 0
  else if k = 2 ∧ e = 1 then some 1
  else none) :=
  to₂ <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _))
        (Primrec.eq.comp snd (const _))) (const _)
      <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _))
        (Primrec.eq.comp snd (const _))) (const _)
      <| const _

instance (k) : Primcodable (oRing.Relations k) where
  prim := nat_iff.mp <| (Primrec.encode.comp (Rel_encodeDecode_primrec.comp (Primrec.const k)
      Primrec.id)).of_eq (fun e => by
    simp[Encodable.decode]
    rcases k with (_ | k) <;> simp
    rcases k with (_ | k) <;> simp
    rcases k with (_ | k) <;> simp
    rcases e with (_ | e) <;> simp
    · rfl
    · rcases e with (_ | e) <;> simp
      · rfl)
/-
instance : UniformlyPrimcodable oRing.Relations := UniformlyPrimcodable.ofEncodeDecode
  (Rel_encodeDecode_primrec.of_eq $ fun k e => by
    simp[Encodable.encodeDecode, Encodable.decode]
    rcases k with (_ | k) <;> simp
    rcases k with (_ | k) <;> simp
    rcases k with (_ | k) <;> simp
    rcases e with (_ | e) <;> simp
    · rfl
    · rcases e with (_ | e) <;> simp
      · rfl)
-/
end ORing

end Language

end FirstOrder
