/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Logic.Function.Basic
/-!
# Equivalence between types

* `equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

## Tags

equivalence, congruence, bijective map
-/

open Function

universes u v w
variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure equiv (α : Sort u) (β : Sort v) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

infix:25 " ≃ " => equiv

namespace equiv

/-- `perm α` is the type of bijections from `α` to itself. -/
@[reducible] def perm (α : Sort u) := equiv α α

instance : CoeFun (α ≃ β) (λ _ => α → β):=
⟨to_fun⟩

@[simp] theorem coe_fn_mk (f : α → β) (g l r) : (equiv.mk f g l r : α → β) = f :=
rfl

def refl (α) : α ≃ α := ⟨id, id, λ _ => rfl, λ _ => rfl⟩

def symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun, e.right_inv, e.left_inv⟩

def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ (e₁ : α → β), e₁.symm ∘ (e₂.symm : γ → β),
  e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simp] theorem apply_symm_apply  (e : α ≃ β) (x : β) : e (e.symm x) = x :=
e.right_inv x

@[simp] theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x :=
e.left_inv x

@[simp] theorem symm_comp_self (e : α ≃ β) : e.symm ∘ (e : α → β) = id := funext e.symm_apply_apply

@[simp] theorem self_comp_symm (e : α ≃ β) : e ∘ (e.symm : β → α) = id := funext e.apply_symm_apply

end equiv
