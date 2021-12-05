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

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α : Sort u) (β : Sort v) where
  toFun    : α → β
  invFun   : β → α
  leftInv  : left_inverse invFun toFun
  rightInv : right_inverse invFun toFun

infix:25 " ≃ " => Equiv

namespace Equiv

/-- `perm α` is the type of bijections from `α` to itself. -/
@[reducible] def perm (α : Sort u) := Equiv α α

instance : CoeFun (α ≃ β) (λ _ => α → β):=
⟨toFun⟩

-- Does not need to be simp, since the coercion is the projection,
-- which simp has built-in support for.
theorem coe_fn_mk (f : α → β) (g l r) : (Equiv.mk f g l r : α → β) = f :=
rfl

def refl (α) : α ≃ α := ⟨id, id, λ _ => rfl, λ _ => rfl⟩

instance : Inhabited (α ≃ α) := ⟨Equiv.refl α⟩

def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.rightInv, e.leftInv⟩


def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ (e₁ : α → β), e₁.symm ∘ (e₂.symm : γ → β),
  e₂.leftInv.comp e₁.leftInv, e₂.rightInv.comp e₁.rightInv⟩

theorem to_fun_as_coe (e : α ≃ β) : e.toFun = e := rfl

@[simp] theorem inv_fun_as_coe (e : α ≃ β) : e.invFun = e.symm := rfl

@[simp] theorem apply_symm_apply  (e : α ≃ β) (x : β) : e (e.symm x) = x :=
e.rightInv x

@[simp] theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x :=
e.leftInv x

@[simp] theorem symm_comp_self (e : α ≃ β) : e.symm ∘ (e : α → β) = id := funext e.symm_apply_apply

@[simp] theorem self_comp_symm (e : α ≃ β) : e ∘ (e.symm : β → α) = id := funext e.apply_symm_apply

end Equiv
