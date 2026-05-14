/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive

/-!
# Product and sums indexed by finite sets in sigma types.

-/

public section

variable {ι κ α β γ : Type*}

open Fin Function

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoid

variable [CommMonoid β]

/-- The product over a sigma type equals the product of the fiberwise products.
For rewriting in the reverse direction, use `Finset.prod_sigma'`.

See also `Fintype.prod_sigma` for the product over the whole type. -/
@[to_additive /-- The sum over a sigma type equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_sigma'`.

See also `Fintype.sum_sigma` for the sum over the whole type. -/]
theorem prod_sigma {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : Sigma σ → β) :
    ∏ x ∈ s.sigma t, f x = ∏ a ∈ s, ∏ s ∈ t a, f ⟨a, s⟩ := by
  simp_rw [← disjiUnion_map_sigma_mk, prod_disjiUnion, prod_map, Function.Embedding.sigmaMk_apply]

/-- The product over a sigma type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Finset.prod_sigma`. -/
@[to_additive /-- The sum over a sigma type equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_sigma` -/]
theorem prod_sigma' {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : ∀ a, σ a → β) :
    (∏ a ∈ s, ∏ s ∈ t a, f a s) = ∏ x ∈ s.sigma t, f x.1 x.2 :=
  Eq.symm <| prod_sigma s t fun x => f x.1 x.2

@[to_additive]
theorem prod_finset_product (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ × α → β} :
    ∏ p ∈ r, f p = ∏ c ∈ s, ∏ a ∈ t c, f (c, a) := by
  refine Eq.trans ?_ (prod_sigma s t fun p => f (p.1, p.2))
  apply prod_equiv (Equiv.sigmaEquivProd _ _).symm <;> simp [h]

@[to_additive]
theorem prod_finset_product' (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ → α → β} :
    ∏ p ∈ r, f p.1 p.2 = ∏ c ∈ s, ∏ a ∈ t c, f c a :=
  prod_finset_product r s t h

@[to_additive]
theorem prod_finset_product_right (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α × γ → β} :
    ∏ p ∈ r, f p = ∏ c ∈ s, ∏ a ∈ t c, f (a, c) := by
  refine Eq.trans ?_ (prod_sigma s t fun p => f (p.2, p.1))
  apply prod_equiv ((Equiv.prodComm _ _).trans (Equiv.sigmaEquivProd _ _).symm) <;> simp [h]

@[to_additive]
theorem prod_finset_product_right' (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α → γ → β} :
    ∏ p ∈ r, f p.1 p.2 = ∏ c ∈ s, ∏ a ∈ t c, f a c :=
  prod_finset_product_right r s t h

/-- The product over a product set equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Finset.prod_product'`. -/
@[to_additive /-- The sum over a product set equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_product'` -/]
theorem prod_product (s : Finset γ) (t : Finset α) (f : γ × α → β) :
    ∏ x ∈ s ×ˢ t, f x = ∏ x ∈ s, ∏ y ∈ t, f (x, y) :=
  prod_finset_product (s ×ˢ t) s (fun _a => t) fun _p => mem_product

/-- The product over a product set equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Finset.prod_product`. -/
@[to_additive /-- The sum over a product set equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_product` -/]
theorem prod_product' (s : Finset γ) (t : Finset α) (f : γ → α → β) :
    ∏ x ∈ s ×ˢ t, f x.1 x.2 = ∏ x ∈ s, ∏ y ∈ t, f x y :=
  prod_product ..

@[to_additive]
theorem prod_product_right (s : Finset γ) (t : Finset α) (f : γ × α → β) :
    ∏ x ∈ s ×ˢ t, f x = ∏ y ∈ t, ∏ x ∈ s, f (x, y) :=
  prod_finset_product_right (s ×ˢ t) t (fun _a => s) fun _p => mem_product.trans and_comm

/-- An uncurried version of `Finset.prod_product_right`. -/
@[to_additive /-- An uncurried version of `Finset.sum_product_right` -/]
theorem prod_product_right' (s : Finset γ) (t : Finset α) (f : γ → α → β) :
    ∏ x ∈ s ×ˢ t, f x.1 x.2 = ∏ y ∈ t, ∏ x ∈ s, f x y :=
  prod_product_right ..

/-- Generalization of `Finset.prod_comm` to the case when the inner `Finset`s depend on the outer
variable. -/
@[to_additive /-- Generalization of `Finset.sum_comm` to the case when the inner `Finset`s depend on
the outer variable. -/]
theorem prod_comm' {s : Finset γ} {t : γ → Finset α} {t' : Finset α} {s' : α → Finset γ}
    (h : ∀ x y, x ∈ s ∧ y ∈ t x ↔ x ∈ s' y ∧ y ∈ t') {f : γ → α → β} :
    (∏ x ∈ s, ∏ y ∈ t x, f x y) = ∏ y ∈ t', ∏ x ∈ s' y, f x y := by
  classical
    have : ∀ z : γ × α, (z ∈ s.biUnion fun x => (t x).map <| Function.Embedding.sectR x _) ↔
      z.1 ∈ s ∧ z.2 ∈ t z.1 := by
      rintro ⟨x, y⟩
      simp only [mem_biUnion, mem_map, Function.Embedding.sectR_apply, Prod.mk.injEq,
        exists_eq_right, ← and_assoc]
    exact
      (prod_finset_product' _ _ _ this).symm.trans
        ((prod_finset_product_right' _ _ _) fun ⟨x, y⟩ => (this _).trans ((h x y).trans and_comm))

@[to_additive]
theorem prod_comm {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x ∈ s, ∏ y ∈ t, f x y) = ∏ y ∈ t, ∏ x ∈ s, f x y :=
  prod_comm' fun _ _ => Iff.rfl

/-- Cyclically permute 3 nested instances of `Finset.prod`. -/
@[to_additive]
theorem prod_comm_cycle {s : Finset γ} {t : Finset α} {u : Finset κ} {f : γ → α → κ → β} :
    (∏ x ∈ s, ∏ y ∈ t, ∏ z ∈ u, f x y z) = ∏ z ∈ u, ∏ x ∈ s, ∏ y ∈ t, f x y z := by
  simp_rw [prod_comm (s := t), prod_comm (s := s)]

end CommMonoid

@[simp]
theorem card_sigma {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) :
    #(s.sigma t) = ∑ a ∈ s, #(t a) :=
  Multiset.card_sigma _ _

end Finset
