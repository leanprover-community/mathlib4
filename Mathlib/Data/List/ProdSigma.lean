/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Sigma.Basic

#align_import data.list.prod_sigma from "leanprover-community/mathlib"@"dd71334db81d0bd444af1ee339a29298bef40734"

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
#align list.nil_product List.nil_product

@[simp]
theorem product_cons (a : α) (l₁ : List α) (l₂ : List β) :
    (a :: l₁) ×ˢ l₂ = map (fun b => (a, b)) l₂ ++ (l₁ ×ˢ l₂) :=
  rfl
#align list.product_cons List.product_cons

@[simp]
theorem product_nil : ∀ l : List α, l ×ˢ (@nil β) = []
  | [] => rfl
  | _ :: l => by simp [product_cons, product_nil l]
#align list.product_nil List.product_nil

@[simp]
theorem mem_product {l₁ : List α} {l₂ : List β} {a : α} {b : β} :
    (a, b) ∈ l₁ ×ˢ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ := by
  simp_all [SProd.sprod, product, mem_bind, mem_map, Prod.ext_iff, exists_prop, and_left_comm,
    exists_and_left, exists_eq_left, exists_eq_right]
#align list.mem_product List.mem_product

theorem length_product (l₁ : List α) (l₂ : List β) :
    length (l₁ ×ˢ l₂) = length l₁ * length l₂ := by
  induction' l₁ with x l₁ IH
  · exact (Nat.zero_mul _).symm
  · simp only [length, product_cons, length_append, IH, Nat.add_mul, Nat.one_mul, length_map,
      Nat.add_comm]
#align list.length_product List.length_product

/-! ### sigma -/


variable {σ : α → Type*}

@[simp]
theorem nil_sigma (l : ∀ a, List (σ a)) : (@nil α).sigma l = [] :=
  rfl
#align list.nil_sigma List.nil_sigma

@[simp]
theorem sigma_cons (a : α) (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    (a :: l₁).sigma l₂ = map (Sigma.mk a) (l₂ a) ++ l₁.sigma l₂ :=
  rfl
#align list.sigma_cons List.sigma_cons

@[simp]
theorem sigma_nil : ∀ l : List α, (l.sigma fun a => @nil (σ a)) = []
  | [] => rfl
  | _ :: l => by simp [sigma_cons, sigma_nil l]
#align list.sigma_nil List.sigma_nil

@[simp]
theorem mem_sigma {l₁ : List α} {l₂ : ∀ a, List (σ a)} {a : α} {b : σ a} :
    Sigma.mk a b ∈ l₁.sigma l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ a := by
  simp [List.sigma, mem_bind, mem_map, exists_prop, exists_and_left, and_left_comm,
    exists_eq_left, heq_iff_eq, exists_eq_right]
#align list.mem_sigma List.mem_sigma

/-- See `List.length_sigma` for the corresponding statement using `List.sum`. -/
theorem length_sigma' (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    length (l₁.sigma l₂) = Nat.sum (l₁.map fun a ↦ length (l₂ a)) := by
  induction' l₁ with x l₁ IH
  · rfl
  · simp only [map, sigma_cons, length_append, length_map, IH, Nat.sum_cons]

end List
