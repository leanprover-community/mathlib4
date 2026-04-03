/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Init

/-!

This file defines `Prod.prodMk f g`, the operation that prodMks two functions `f : γ → α` and
`g : γ → β` into a function `γ → α × β`.

It also defines the special case when `f = g = id`, `Prod.diag`. This is the canonical injection
of a type into its prouduct with itself onto its diagonal.


This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

-/

@[expose] public section

namespace Prod

universe u₁ u₂ u₃ u₄ u₅

variable {α : Type u₁} {β : Type u₂} {γ : Sort u₃} {δ : Type u₄} {ε : Type u₅}

/-- This is the pairing operation on functions, dual to `Sum.elim`. -/
@[expose] protected def prodMk (f : γ → α) (g : γ → β) : γ → α × β := fun a ↦ (f a, g a)

section

variable (f : γ → α) (g : γ → β)

@[grind =] theorem prodMk_apply (c : γ) : Prod.prodMk f g c = (f c, g c) := rfl

@[simp] theorem fst_prodMk {c} : (Prod.prodMk f g c).fst = f c := rfl
@[simp] theorem snd_prodMk {c} : (Prod.prodMk f g c).snd = g c := rfl

@[simp] theorem fst_comp_prodMk : fst ∘ Prod.prodMk f g = f := rfl
@[simp] theorem snd_comp_prodMk : snd ∘ Prod.prodMk f g = g := rfl
@[simp] theorem prodMk_fst_snd : @Prod.prodMk α β _ fst snd = id := rfl

theorem prodMk_comp {δ} {h : δ → γ} : Prod.prodMk f g ∘ h = Prod.prodMk (f ∘ h) (g ∘ h) := rfl

@[simp] theorem prodMk_fst_snd_comp {f : γ → α × β} : Prod.prodMk (fst ∘ f) (snd ∘ f) = f := rfl

theorem prodMk_eq_iff {f f' : γ → α} {g g' : γ → β} : Prod.prodMk f g = Prod.prodMk f' g' ↔
    f = f' ∧ g = g' := by simp [funext_iff, Prod.ext_iff, forall_and]

@[grind =]
theorem prodMk_const_const (a : α) (b : β) :
    Prod.prodMk (Function.const γ a) (Function.const γ b) = Function.const γ (a, b) := rfl

end

section

/- We can define `Prod.map` in terms of `Prod.prodMk`. -/
theorem map_eq_prodMk {f : α → β} {g : δ → ε} : Prod.map f g =
    Prod.prodMk (f ∘ fst) (g ∘ snd) := rfl

@[grind _=_]
theorem map_prodMk {f : α → β} {g : γ → α} {h : δ → ε} {k : γ → δ} {c} :
    Prod.map f h (Prod.prodMk g k c) = Prod.prodMk (f ∘ g) (h ∘ k) c := rfl

theorem map_comp_prodMk {f : α → β} {g : γ → α} {h : δ → ε} {k : γ → δ} :
  Prod.map f h ∘ Prod.prodMk g k = Prod.prodMk (f ∘ g) (h ∘ k) := rfl

end

/-- The diagonal map into Prod. -/
@[expose] protected def diag : α → α × α := Prod.prodMk id id

section

variable {a b : α}

@[grind =] theorem diag_apply : Prod.diag a = (a, a) := rfl

@[simp, grind =] theorem fst_diag : (Prod.diag a).1 = a := rfl
@[simp, grind =] theorem snd_diag : (Prod.diag a).2 = a := rfl

@[simp, grind =] theorem map_diag {f : α → β} {g : α → δ} : Prod.map f g (Prod.diag a) =
    Prod.prodMk f g a := rfl

theorem map_comp_diag {f : α → β} {g : α → δ} : Prod.map f g ∘ Prod.diag = Prod.prodMk f g := rfl

theorem injective_diag : Function.Injective (Prod.diag (α := α)) := fun _ _ => congrArg fst

theorem exists_diag_apply_iff (p : α × α) : (∃ a, p = Prod.diag a) ↔ p.1 = p.2 := by
  simp [Prod.ext_iff, eq_comm]

@[simp] theorem diag_eq_iff : Prod.diag a = Prod.diag b ↔ a = b := injective_diag.eq_iff

end

end Prod
