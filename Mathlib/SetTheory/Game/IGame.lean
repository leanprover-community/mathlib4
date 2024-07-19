/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.SetTheory.Game.PGame
import Mathlib.Tactic.Abel

/-!
# Combinatorial games with identity as equality.

In this file we define "identical" games (`IGame` below) to be the quotient of `PGames` by the
extensional equivalence. Their equality in Lean is usually called identity, and we use `≈` to
express the equality of games.
Combinatorial games quotient by equality, whose identity is meaningless, are constructed in
`SetTheory.Game.Basic`.
-/

universe u

namespace SetTheory

abbrev IGame := Quotient PGame.identicalSetoid

namespace IGame

attribute [local instance] PGame.identicalSetoid

open PGame

abbrev mk : PGame → IGame := Quotient.mk _

instance : Coe PGame IGame where
  coe := mk

@[simp]
lemma mk_eq_mk {x y : PGame} : mk x = mk y ↔ x ≡ y :=
  Quotient.eq

@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma inductionOn {motive : IGame → Prop}
    (a : IGame) (mk : ∀ a, motive (mk a)) : motive a :=
  Quotient.inductionOn a mk

@[elab_as_elim]
lemma inductionOn₂ {motive : IGame → IGame → Prop}
    (a b : IGame) (mk : ∀ a b, motive (mk a) (mk b)) : motive a b :=
  Quotient.inductionOn₂ a b mk

@[elab_as_elim]
lemma inductionOn₃ {motive : IGame → IGame → IGame → Prop}
    (a b c : IGame) (mk : ∀ a b c, motive (mk a) (mk b) (mk c)) : motive a b c :=
  Quotient.inductionOn₃ a b c mk

instance : LeftRightOption IGame where
  memₗ := Quotient.lift₂ (· ∈ₗ ·)
    (fun _ _ _ _ hx hy ↦ propext ((memₗ.congr_left hx).trans (memₗ.congr_right hy)))
  memᵣ := Quotient.lift₂ (· ∈ᵣ ·)
    (fun _ _ _ _ hx hy ↦ propext ((memᵣ.congr_left hx).trans (memᵣ.congr_right hy)))

lemma ext {x y : IGame} (hl : ∀ z, z ∈ₗ x ↔ z ∈ₗ y) (hr : ∀ z, z ∈ᵣ x ↔ z ∈ᵣ y) : x = y := by
  induction x; induction y
  exact Quotient.sound <| PGame.Identical.ext (hl ·) (hr ·)

instance : Preorder IGame where
  le := Quotient.lift₂ (· ≤ ·) (fun x₁ y₁ x₂ y₂ (hx : x₁ ≡ x₂) (hy : y₁ ≡ y₂) ↦
    propext ((le_congr_left hx.equiv).trans (le_congr_right hy.equiv)))
  lt := Quotient.lift₂ (· < ·) (fun x₁ y₁ x₂ y₂ (hx : x₁ ≡ x₂) (hy : y₁ ≡ y₂) ↦
    propext ((lt_congr_left hx.equiv).trans (lt_congr_right hy.equiv)))
  le_refl x := inductionOn x le_refl
  le_trans x y z := inductionOn₃ x y z <| @le_trans PGame _
  lt_iff_le_not_le x y := inductionOn₂ x y <| @lt_iff_le_not_le PGame _

instance : Zero IGame where
  zero := mk 0

instance : One IGame where
  one := mk 1

instance : Add IGame where
  add := Quotient.map₂ (· + ·) (fun _ _ hx _ _ hy ↦ hx.add hy)

instance : Neg IGame where
  neg := Quotient.map PGame.neg (fun _ _ ↦ Identical.neg)

instance : AddCommMonoidWithOne IGame where
  add_assoc x y z := inductionOn₃ x y z <| fun x y z ↦ Quotient.sound (x.add_assoc y z)
  zero_add x := inductionOn x <| fun x ↦ Quotient.sound x.zero_add
  add_zero x := inductionOn x <| fun x ↦ Quotient.sound x.add_zero
  add_comm x y := inductionOn₂ x y <| fun x y ↦ Quotient.sound (x.add_comm y)
  nsmul := nsmulRec

@[simp] lemma mk_add_mk {x y : PGame} : mk x + mk y = mk (x + y) := rfl

@[simp] lemma neg_mk {x : PGame} : -mk x = mk (-x) := rfl

instance : SubtractionCommMonoid IGame where
  neg_neg x := x.inductionOn <| by simp [neg_mk]
  neg_add_rev x y := inductionOn₂ x y <| fun x y ↦ Quotient.sound (x.neg_add_rev y)
  neg_eq_of_add x y := inductionOn₂ x y <| fun x y h ↦ Quotient.sound <|
    let ⟨h₁, h₂⟩ := (add_eq_zero_iff x y).mp (Quotient.exact h)
    (h₁.neg.trans_eq neg_zero).trans h₂.symm
  add_comm := add_comm
  zsmul := zsmulRec

@[simp] lemma mk_sub_mk {x y : PGame} : mk x - mk y = mk (x - y) := rfl

instance covariantClass_add_le : CovariantClass IGame IGame (· + ·) (· ≤ ·) where
  elim x y₁ y₂ := inductionOn₃ x y₁ y₂ <| fun _ _ _ hy ↦
    add_le_add_left (α := PGame) hy _

instance covariantClass_add_lt : CovariantClass IGame IGame (· + ·) (· < ·) where
  elim x y₁ y₂ := inductionOn₃ x y₁ y₂ <| fun _ _ _ hy ↦
    add_lt_add_left (α := PGame) hy _

instance : MulZeroOneClass IGame where
  mul := Quotient.map₂ (· * ·) (fun _ _ hx _ _ hy ↦ hx.mul hy)
  one_mul x := inductionOn x <| fun x ↦ Quotient.sound x.one_mul
  mul_one x := inductionOn x <| fun x ↦ Quotient.sound x.mul_one
  zero_mul x := inductionOn x <| fun x ↦ Quotient.sound x.zero_mul
  mul_zero x := inductionOn x <| fun x ↦ Quotient.sound x.mul_zero

instance : CommMagma IGame where
  mul_comm x y := inductionOn₂ x y <| fun x y ↦ Quotient.sound (x.mul_comm y)

@[simp] lemma mk_mul_mk {x y : PGame} : mk x * mk y = mk (x * y) := rfl

instance : HasDistribNeg IGame where
  neg_mul x y := inductionOn₂ x y <| fun x y ↦ Quotient.sound (x.neg_mul y)
  mul_neg x y := inductionOn₂ x y <| by simp [PGame.mul_neg]

end IGame

end SetTheory
