/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Logic
import Mathlib.Mathport.Rename

/-! # Quotient types

These are ported from the Lean 3 standard library file `init/data/quot.lean`.
-/

set_option autoImplicit true

section
variable {α : Type u}
variable (r : α → α → Prop)

/-- `EqvGen r` is the equivalence relation generated by `r`. -/
inductive EqvGen : α → α → Prop
  | rel : ∀ x y, r x y → EqvGen x y
  | refl : ∀ x, EqvGen x x
  | symm : ∀ x y, EqvGen x y → EqvGen y x
  | trans : ∀ x y z, EqvGen x y → EqvGen y z → EqvGen x z
#align eqv_gen EqvGen

theorem EqvGen.is_equivalence : Equivalence (@EqvGen α r) :=
  Equivalence.mk EqvGen.refl (EqvGen.symm _ _) (EqvGen.trans _ _ _)

/-- `EqvGen.Setoid r` is the setoid generated by a relation `r`.

The motivation for this definition is that `Quot r` behaves like `Quotient (EqvGen.Setoid r)`,
see for example `Quot.exact` and `Quot.EqvGen_sound`.
-/
def EqvGen.Setoid : Setoid α :=
  Setoid.mk _ (EqvGen.is_equivalence r)
#align eqv_gen.setoid EqvGen.Setoid

theorem Quot.exact {a b : α} (H : Quot.mk r a = Quot.mk r b) : EqvGen r a b :=
  @Quotient.exact _ (EqvGen.Setoid r) a b (congr_arg
    (Quot.lift (Quotient.mk (EqvGen.Setoid r)) (fun x y h ↦ Quot.sound (EqvGen.rel x y h))) H)
#align quot.exact Quot.exact

theorem Quot.EqvGen_sound {r : α → α → Prop} {a b : α} (H : EqvGen r a b) :
    Quot.mk r a = Quot.mk r b :=
  EqvGen.rec
    (fun _ _ h ↦ Quot.sound h)
    (fun _ ↦ rfl)
    (fun _ _ _ IH ↦ Eq.symm IH)
    (fun _ _ _ _ _ IH₁ IH₂ ↦ Eq.trans IH₁ IH₂)
    H
#align quot.eqv_gen_sound Quot.EqvGen_sound

end

open Decidable
instance Quotient.decidableEq {α : Sort u} {s : Setoid α} [d : ∀ a b : α, Decidable (a ≈ b)] :
    DecidableEq (Quotient s) :=
  fun q₁ q₂ : Quotient s ↦
    Quotient.recOnSubsingleton₂ q₁ q₂
      (fun a₁ a₂ ↦
        match (d a₁ a₂) with
        | (isTrue h₁)  => isTrue (Quotient.sound h₁)
        | (isFalse h₂) => isFalse (fun h ↦ absurd (Quotient.exact h) h₂))
