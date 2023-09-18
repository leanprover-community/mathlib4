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

open scoped PGame
open Function PGame

attribute [instance] PGame.identicalSetoid in
section

abbrev mk : PGame → IGame := Quotient.mk _

instance : Coe PGame IGame where
  coe := mk

instance : LeftRightOption IGame where
  memₗ := Quotient.lift₂ PGame.memₗ
    (fun _ _ _ _ hx hy ↦ propext ((memₗ.congr_left hx).trans (memₗ.congr_right hy)))
  memᵣ := Quotient.lift₂ PGame.memᵣ
    (fun _ _ _ _ hx hy ↦ propext ((memᵣ.congr_left hx).trans (memᵣ.congr_right hy)))

lemma ext {x y : IGame} (hl : ∀ z, z ∈ₗ x ↔ z ∈ₗ y) (hr : ∀ z, z ∈ᵣ x ↔ z ∈ᵣ y) : x = y := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  exact Quotient.sound <| PGame.Identical.ext (hl ·) (hr ·)

instance : Preorder IGame where
  le := Quotient.lift₂ (· ≤ ·) (fun x₁ y₁ x₂ y₂ (hx : x₁ ≡ x₂) (hy : y₁ ≡ y₂) ↦
    propext ((le_congr_left hx.equiv).trans (le_congr_right hy.equiv)))
  lt := Quotient.lift₂ (· < ·) (fun x₁ y₁ x₂ y₂ (hx : x₁ ≡ x₂) (hy : y₁ ≡ y₂) ↦
    propext ((lt_congr_left hx.equiv).trans (lt_congr_right hy.equiv)))
  le_refl x := Quotient.inductionOn x le_refl
  le_trans x y z := Quotient.inductionOn₃ x y z <| @le_trans PGame _
  lt_iff_le_not_le x y := Quotient.inductionOn₂ x y <| @lt_iff_le_not_le PGame _

instance : AddCommMonoidWithOne IGame where
  zero := mk 0
  one := mk 1
  add := Quotient.map₂ (· + ·) (fun _ _ hx _ _ hy ↦ hx.add hy)
  add_assoc x y z := Quotient.inductionOn₃ x y z <| fun x y z ↦ Quotient.sound (x.add_assoc y z)
  zero_add x := Quotient.inductionOn x <| fun x ↦ Quotient.sound x.zero_add
  add_zero x := Quotient.inductionOn x <| fun x ↦ Quotient.sound x.add_zero
  add_comm x y := Quotient.inductionOn₂ x y <| fun x y ↦ Quotient.sound (x.add_comm y)

instance : Neg IGame where
  neg := Quotient.map PGame.neg (fun _ _ ↦ Identical.neg)

@[simp] lemma mk_add_mk {x y : PGame} : mk x + mk y = mk (x + y) := rfl

@[simp] lemma neg_mk {x : PGame} : -mk x = mk (-x) := rfl

instance : SubtractionCommMonoid IGame where
  neg_neg x := by apply x.ind; simp [neg_mk]
  neg_add_rev x y := Quotient.inductionOn₂ x y <| fun x y ↦ Quotient.sound (x.neg_add_rev y)
  neg_eq_of_add x y := Quotient.inductionOn₂ x y <| fun x y h ↦ Quotient.sound <|
    let ⟨h₁, h₂⟩ := (add_eq_zero_iff x y).mp (Quotient.exact h)
    (h₁.neg.trans_eq neg_zero).trans h₂.symm
  add_comm := add_comm

@[simp] lemma mk_sub_mk {x y : PGame} : mk x - mk y = mk (x - y) := rfl

instance covariantClass_add_le : CovariantClass IGame IGame (· + ·) (· ≤ ·) where
  elim x y₁ y₂ := Quotient.inductionOn₃ x y₁ y₂ <| fun _ _ _ hy ↦
    add_le_add_left (α := PGame) hy _

instance covariantClass_add_lt : CovariantClass IGame IGame (· + ·) (· < ·) where
  elim x y₁ y₂ := Quotient.inductionOn₃ x y₁ y₂ <| fun _ _ _ hy ↦
    add_lt_add_left (α := PGame) hy _

instance : MulZeroOneClass IGame where
  mul := Quotient.map₂ (· * ·) (fun _ _ hx _ _ hy ↦ hx.mul hy)
  one_mul x := Quotient.inductionOn x <| fun x ↦ Quotient.sound x.one_mul
  mul_one x := Quotient.inductionOn x <| fun x ↦ Quotient.sound x.mul_one
  zero_mul x := Quotient.inductionOn x <| fun x ↦ Quotient.sound x.zero_mul
  mul_zero x := Quotient.inductionOn x <| fun x ↦ Quotient.sound x.mul_zero

instance : IsCommutative IGame (· * ·) where
  comm x y := Quotient.inductionOn₂ x y <| fun x y ↦ Quotient.sound (x.mul_comm y)

@[simp] lemma mk_mul_mk {x y : PGame} : mk x * mk y = mk (x * y) := rfl

lemma Quotient.exists {α} {s : Setoid α} {p : Quotient s → Prop} :
    (∃ q, p q) ↔ (∃ a : α, p ⟦a⟧) :=
  ⟨fun ⟨q, hq⟩ ↦ q.exists_rep.imp fun a (ha : ⟦a⟧ = q) ↦ ha ▸ hq, fun ⟨a, ha⟩ ↦ ⟨⟦a⟧, ha⟩⟩

lemma memₗ_add_iff {x y₁ y₂ : IGame} :
    x ∈ₗ y₁ + y₂ ↔ (∃ z ∈ₗ y₁, x = z + y₂) ∨ (∃ z ∈ₗ y₂, x = y₁ + z) := by
  induction x using Quotient.ind
  induction y₁ using Quotient.ind
  induction y₂ using Quotient.ind
  simp_rw [Quotient.exists, mk_add_mk, Quotient.eq]
  exact PGame.memₗ_add_iff'

lemma memᵣ_add_iff {x y₁ y₂ : IGame} :
    x ∈ᵣ y₁ + y₂ ↔ (∃ z ∈ᵣ y₁, x = z + y₂) ∨ (∃ z ∈ᵣ y₂, x = y₁ + z) := by
  induction x using Quotient.ind
  induction y₁ using Quotient.ind
  induction y₂ using Quotient.ind
  simp_rw [Quotient.exists, mk_add_mk, Quotient.eq]
  exact PGame.memᵣ_add_iff'

lemma memₗ_neg_iff {x y : IGame} :
    x ∈ₗ -y ↔ (∃ z ∈ᵣ y, x = -z) := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  simp_rw [Quotient.exists, neg_mk, Quotient.eq]
  exact PGame.memₗ_neg_iff'

lemma memᵣ_neg_iff {x y : IGame} :
    x ∈ᵣ -y ↔ (∃ z ∈ₗ y, x = -z) := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  simp_rw [Quotient.exists, neg_mk, Quotient.eq]
  exact PGame.memᵣ_neg_iff'

lemma memₗ_mul_iff {x y₁ y₂ : IGame} :
    x ∈ₗ y₁ * y₂ ↔
      (∃ z₁ ∈ₗ y₁, (∃ z₂ ∈ₗ y₂, (x = z₁ * y₂ + y₁ * z₂ - z₁ * z₂))) ∨
      (∃ z₁ ∈ᵣ y₁, (∃ z₂ ∈ᵣ y₂, (x = z₁ * y₂ + y₁ * z₂ - z₁ * z₂))) := by
  induction x using Quotient.ind
  induction y₁ using Quotient.ind
  induction y₂ using Quotient.ind
  simp_rw [Quotient.exists, mk_mul_mk, mk_add_mk, mk_sub_mk, Quotient.eq]
  exact PGame.memₗ_mul_iff'

lemma memᵣ_mul_iff {x y₁ y₂ : IGame} :
    x ∈ᵣ y₁ * y₂ ↔
      (∃ z₁ ∈ₗ y₁, (∃ z₂ ∈ᵣ y₂, (x = z₁ * y₂ + y₁ * z₂ - z₁ * z₂))) ∨
      (∃ z₁ ∈ᵣ y₁, (∃ z₂ ∈ₗ y₂, (x = z₁ * y₂ + y₁ * z₂ - z₁ * z₂))) := by
  induction x using Quotient.ind
  induction y₁ using Quotient.ind
  induction y₂ using Quotient.ind
  simp_rw [Quotient.exists, mk_mul_mk, mk_add_mk, mk_sub_mk, Quotient.eq]
  exact PGame.memᵣ_mul_iff'

open Setoid in
def _root_.Setoid.correspondence' {α : Type*} (r : Setoid α) : { s // r ≤ s } ≃o Setoid (Quotient r) where
  toFun s := ⟨Quotient.lift₂ s.1.1 fun _ _ _ _ h₁ h₂ ↦ Eq.propIntro
      (fun h ↦ s.1.trans' (s.1.trans' (s.1.symm' (s.2 h₁)) h) (s.2 h₂))
      (fun h ↦ s.1.trans' (s.1.trans' (s.2 h₁) h) (s.1.symm' (s.2 h₂))),
    ⟨Quotient.ind s.1.2.1, @fun x y ↦ Quotient.inductionOn₂ x y fun _ _ ↦ s.1.2.2,
      @fun x y z ↦ Quotient.inductionOn₃ x y z fun _ _ _ ↦ s.1.2.3⟩⟩
  invFun s := ⟨comap Quotient.mk' s, fun x y h => by rw [comap_rel, Quotient.eq_rel.2 h]⟩
  left_inv s := rfl
  right_inv s := Setoid.ext fun x y ↦ Quotient.inductionOn₂ x y fun _ _ ↦ Iff.rfl
  map_rel_iff' :=
    ⟨fun h x y hs ↦ @h ⟦x⟧ ⟦y⟧ hs, fun h x y ↦ Quotient.inductionOn₂ x y fun _ _ hs ↦ h hs⟩

instance setoid : Setoid IGame :=
  Setoid.correspondence' _ ⟨PGame.setoid, fun _ _ h ↦ h.equiv⟩

abbrev Equiv : IGame → IGame → Prop := setoid.Rel

theorem Equiv.ext {x y : IGame}
    (hl : (∀ a ∈ₗ x, ∃ b ∈ₗ y, a ≈ b) ∧ (∀ b ∈ₗ y, ∃ a ∈ₗ x, a ≈ b))
    (hr : (∀ a ∈ᵣ x, ∃ b ∈ᵣ y, a ≈ b) ∧ (∀ b ∈ᵣ y, ∃ a ∈ᵣ x, a ≈ b)) :
    x ≈ y := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  refine' PGame.Equiv.ext' ⟨fun a ha ↦ _, fun a ha ↦ _⟩ ⟨fun a ha ↦ _, fun a ha ↦ _⟩
  · obtain ⟨b, hb, h⟩ := hl.1 a ha
    induction b using Quotient.ind
    exact ⟨_, hb, h⟩
  · obtain ⟨b, hb, h⟩ := hl.2 a ha
    induction b using Quotient.ind
    exact ⟨_, hb, h⟩
  · obtain ⟨b, hb, h⟩ := hr.1 a ha
    induction b using Quotient.ind
    exact ⟨_, hb, h⟩
  · obtain ⟨b, hb, h⟩ := hr.2 a ha
    induction b using Quotient.ind
    exact ⟨_, hb, h⟩

theorem Equiv.ext' {x y : IGame}
    (hl : Relator.BiTotal fun (a : {a // a ∈ₗ x}) (b : {b // b ∈ₗ y}) ↦ a.1 ≈ b.1)
    (hr : Relator.BiTotal fun (a : {a // a ∈ᵣ x}) (b : {b // b ∈ᵣ y}) ↦ a.1 ≈ b.1) :
    x ≈ y := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  refine' PGame.Equiv.ext'' ⟨fun a ↦ _, fun a ↦ _⟩ ⟨fun a ↦ _, fun a ↦ _⟩
  · obtain ⟨⟨b, hb⟩, h⟩ := hl.1 ⟨a.1, a.2⟩
    induction b using Quotient.ind
    exact ⟨⟨_, hb⟩, h⟩
  · obtain ⟨⟨b, hb⟩, h⟩ := hl.2 ⟨a.1, a.2⟩
    induction b using Quotient.ind
    exact ⟨⟨_, hb⟩, h⟩
  · obtain ⟨⟨b, hb⟩, h⟩ := hr.1 ⟨a.1, a.2⟩
    induction b using Quotient.ind
    exact ⟨⟨_, hb⟩, h⟩
  · obtain ⟨⟨b, hb⟩, h⟩ := hr.2 ⟨a.1, a.2⟩
    induction b using Quotient.ind
    exact ⟨⟨_, hb⟩, h⟩

@[simp]
theorem mul_add_equiv (x y z : IGame) : x * (y + z) ≈ x * y + x * z := by
  apply Equiv.ext
  · simp_rw [memₗ_add_iff, memₗ_mul_iff, LeftMovesMul.exists, mul_moveLeft_inl, mul_moveLeft_inr,
      LeftMovesAdd.exists, add_moveLeft_inl, add_moveLeft_inr,
      RightMovesAdd.exists, add_moveRight_inl, add_moveRight_inr, exists_or]; dsimp
    rw [or_or_or_comm]; congr! 6 <;> apply Identical.congr_right
    · apply Identitical.sub

end

end IGame

end SetTheory
