/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-!
# Lists in product and sigma types

This file proves basic properties of `List.product` and `List.sigma`, which are list constructions
living in `Prod` and `Sigma` types respectively. Their definitions can be found in
[`Data.List.Defs`](./defs). Beware, this is not about `List.prod`, the multiplicative product.
-/


variable {α β : Type*}

namespace List

/-! ### product -/


@[simp]
theorem nil_product (l : List β) : (@nil α) ×ˢ l = [] :=
  rfl

@[simp]
theorem product_cons (a : α) (l₁ : List α) (l₂ : List β) :
    (a :: l₁) ×ˢ l₂ = map (fun b => (a, b)) l₂ ++ (l₁ ×ˢ l₂) :=
  rfl

@[simp]
theorem product_nil : ∀ l : List α, l ×ˢ (@nil β) = []
  | [] => rfl
  | _ :: l => by simp [product_cons, product_nil l]

@[simp]
theorem mem_product {l₁ : List α} {l₂ : List β} {a : α} {b : β} :
    (a, b) ∈ l₁ ×ˢ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ := by
  simp_all [SProd.sprod, product, mem_flatMap, mem_map, Prod.ext_iff, and_left_comm,
    exists_and_left, exists_eq_left, exists_eq_right]

theorem length_product (l₁ : List α) (l₂ : List β) :
    length (l₁ ×ˢ l₂) = length l₁ * length l₂ := by
  induction l₁ with
  | nil => exact (Nat.zero_mul _).symm
  | cons x l₁ IH =>
    simp only [length, product_cons, length_append, IH, Nat.add_mul, Nat.one_mul, length_map,
      Nat.add_comm]

/-! ### sigma -/


variable {σ : α → Type*}

@[simp]
theorem nil_sigma (l : ∀ a, List (σ a)) : (@nil α).sigma l = [] :=
  rfl

@[simp]
theorem sigma_cons (a : α) (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    (a :: l₁).sigma l₂ = map (Sigma.mk a) (l₂ a) ++ l₁.sigma l₂ :=
  rfl

@[simp]
theorem sigma_nil : ∀ l : List α, (l.sigma fun a => @nil (σ a)) = []
  | [] => rfl
  | _ :: l => by simp [sigma_cons, sigma_nil l]

@[simp]
theorem mem_sigma {l₁ : List α} {l₂ : ∀ a, List (σ a)} {a : α} {b : σ a} :
    Sigma.mk a b ∈ l₁.sigma l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ a := by
  simp [List.sigma, mem_flatMap, mem_map, exists_and_left, and_left_comm,
    exists_eq_left, exists_eq_right]

/-! ### Miscellaneous lemmas -/

@[simp 1100]
theorem mem_map_swap (x : α) (y : β) (xs : List (α × β)) :
    (y, x) ∈ map Prod.swap xs ↔ (x, y) ∈ xs := by
  simp

end List
