/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Setoid.Basic

/-!
# Quotient by the product of two setoids

In this file we define the natural equivalence between
`Quotient r × Quotient s` and `Quotient (r.prod s)`, see `Equiv.quotientProdQuotient`.
We also define the `Quot` version of this equivalence, see `Equiv.quotProdQuot`.
-/

namespace Equiv

variable {α β : Type*}

section QuotProd

/-- The natural equivalence between the product of two quotients
and the quotient of the product by the relation `t (x₁, x₂) (y₁, y₂) = r x₁ y₁ ∧ s x₂ y₂`.

We assume both relations to be reflexive, because, e.g.,
for `r _ _ = False` and `s _ _ = True` on `Bool`, LHS has 2 elements while RHS has 4 elements. -/
def quotProdQuot (r : α → α → Prop) [IsRefl α r] (s : β → β → Prop) [IsRefl β s] :
    Quot r × Quot s ≃ Quot (fun x y : α × β ↦ r x.1 y.1 ∧ s x.2 y.2) where
  toFun := fun x ↦ Quot.liftOn₂ x.1 x.2 (fun a b ↦ Quot.mk _ (a, b))
    (fun a b₁ b₂ hb ↦ Quot.sound ⟨refl_of .., hb⟩)
    (fun a₁ a₂ b ha ↦ Quot.sound ⟨ha, refl_of ..⟩)
  invFun := Quot.lift (Prod.map (Quot.mk r) (Quot.mk s)) fun x y ⟨h₁, h₂⟩ ↦
    Prod.ext (Quot.sound h₁) (Quot.sound h₂)
  left_inv := by rintro ⟨⟨a⟩, ⟨b⟩⟩; rfl
  right_inv := by rintro ⟨a⟩; rfl

variable {r : α → α → Prop} [IsRefl α r] {s : β → β → Prop} [IsRefl β s]

@[simp]
lemma quotProdQuot_apply_mk (a : α) (b : β) :
    quotProdQuot r s (Quot.mk r a, Quot.mk s b) = Quot.mk _ (a, b) :=
  rfl

@[simp]
lemma quotProdQuot_symm_apply_mk (x : α × β) :
    (quotProdQuot r s).symm (Quot.mk _ x) = (Quot.mk r x.1, Quot.mk s x.2) :=
  rfl

end QuotProd

section QuotientProd

/-- The natural equivalence between the product of two quotients
and the quotient of the product by the product setoid. -/
def quotientProdQuotient (r : Setoid α) (s : Setoid β) :
    Quotient r × Quotient s ≃ Quotient (r.prod s) :=
  haveI : IsRefl α r.Rel := ⟨r.refl⟩
  haveI : IsRefl β s.Rel := ⟨s.refl⟩
  quotProdQuot r.Rel s.Rel

variable {r : Setoid α} {s : Setoid β}

@[simp]
lemma quotientProdQuotient_apply_mk (a : α) (b : β) :
    quotientProdQuotient r s (⟦a⟧, ⟦b⟧) = ⟦(a, b)⟧ :=
  rfl

@[simp]
lemma quotientProdQuotient_symm_apply_mk (x : α × β) :
    (quotientProdQuotient r s).symm ⟦x⟧ = (⟦x.1⟧, ⟦x.2⟧) :=
  rfl

end QuotientProd

end Equiv
