/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module data.list.prod_sigma
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.BigOperators.Basic

/-!
# Lists in product and sigma types

This file proves basic properties of `List.product` and `List.sigma`, which are list constructions
living in `prod` and `sigma` types respectively. Their definitions can be found in
[`Data.List.Defs`](./defs). Beware, this is not about `List.prod`, the multiplicative product.
-/


variable {α β : Type _}

namespace List

/-! ### product -/


@[simp]
theorem nil_product (l : List β) : product (@nil α) l = [] :=
  rfl
#align list.nil_product List.nil_product

@[simp]
theorem product_cons (a : α) (l₁ : List α) (l₂ : List β) :
    product (a :: l₁) l₂ = map (fun b => (a, b)) l₂ ++ product l₁ l₂ :=
  rfl
#align list.product_cons List.product_cons

@[simp]
theorem product_nil : ∀ l : List α, product l (@nil β) = []
  | [] => rfl
  | _ :: l => by simp [product_cons, product_nil]
#align list.product_nil List.product_nil

@[simp]
theorem mem_product {l₁ : List α} {l₂ : List β} {a : α} {b : β} :
    (a, b) ∈ product l₁ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ := by
  simp_all [product, mem_bind, mem_map, Prod.ext_iff, exists_prop, and_left_comm, exists_and_left,
    exists_eq_left, exists_eq_right]
#align list.mem_product List.mem_product

theorem length_product (l₁ : List α) (l₂ : List β) :
    length (product l₁ l₂) = length l₁ * length l₂ := by
  induction' l₁ with x l₁ IH <;> [exact (zero_mul _).symm,
    simp only [length, product_cons, length_append, IH, right_distrib, one_mul, length_map,
      add_comm]]
#align list.length_product List.length_product

/-! ### sigma -/


variable {σ : α → Type _}

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
  | _ :: l => by simp [sigma_cons, sigma_nil]
#align list.sigma_nil List.sigma_nil

@[simp]
theorem mem_sigma {l₁ : List α} {l₂ : ∀ a, List (σ a)} {a : α} {b : σ a} :
    Sigma.mk a b ∈ l₁.sigma l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ a := by
  simp_all [List.sigma, mem_bind, mem_map, exists_prop, exists_and_left, and_left_comm,
    exists_eq_left, heq_iff_eq, exists_eq_right]
#align list.mem_sigma List.mem_sigma

theorem length_sigma (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    length (l₁.sigma l₂) = (l₁.map fun a => length (l₂ a)).sum := by
  induction' l₁ with x l₁ IH <;> [rfl,
    simp only [map, sigma_cons, length_append, length_map, IH, sum_cons]]
#align list.length_sigma List.length_sigma

end List
