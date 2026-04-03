/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Init

/-!

This file defines `(f △ g)`, the operation that pairs two functions `f : γ → α` and
`g : γ → β` into a function `γ → α × β`.

It also defines the special case when `f = g = id`, `Prod.diag`. This is the canonical injection
of a type into its prouduct with itself onto its diagonal.


This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

-/

@[expose] public section

namespace Pi

/-- The mapping into a product type built from maps into each component. -/
protected def prod {ι} {α β : ι → Type*} (f : ∀ i, α i) (g : ∀ i, β i) : ∀ i, α i × β i :=
    fun i ↦ (f i, g i)

@[inherit_doc] infixr:65 " △' " => Pi.prod

section

variable {ι} {α β : ι → Type*} (f f' : ∀ i, α i) (g g' : ∀ i, β i) {c}

@[grind =] theorem prod_apply : (f △' g) c = (f c, g c) := rfl

@[simp] theorem fst_prod : ((f △' g) c).fst = f c := rfl
@[simp] theorem snd_prod : ((f △' g) c).snd = g c := rfl

@[simp] theorem prod_fst_snd {α β} : (Prod.fst : _ → α) △' (Prod.snd : _ → β) = id := rfl
@[simp] theorem prod_snd_fst {α β} : (Prod.snd : _ → β) △' (Prod.fst : _ → α) = .swap := rfl

theorem prod_fst_snd_comp {h : ∀ i, α i × β i} :
   (Prod.fst <| h ·) △' (Prod.snd <| h ·) = h := rfl

theorem fst_comp_prod {f : ∀ i, α i} {g : ∀ i, β i} : (Prod.fst <| (f △' g) ·) = f := rfl
theorem snd_comp_prod {f : ∀ i, α i} {g : ∀ i, β i} : (Prod.snd <| (f △' g) ·) = g := rfl

@[simp]
theorem prod_eq_iff {f : ∀ i, α i} {g : ∀ i, β i} :
    f △' g = f' △' g' ↔ f = f' ∧ g = g' := by simp [funext_iff, Prod.ext_iff, forall_and]

theorem prod_ext_iff {h h' : ∀ i, α i × β i} : h = h' ↔
    (Prod.fst <| h ·) = (Prod.fst <| h' ·) ∧ (Prod.snd <| h ·) = (Prod.snd <| h' ·) := by
  simp [funext_iff, Prod.ext_iff, forall_and]

theorem exists_prod_apply_eq (h : ∀ i, α i × β i) : ∃ f g, (f △' g) = h :=
  ⟨(Prod.fst <| h ·), (Prod.snd <| h ·), prod_fst_snd_comp⟩

theorem exists_fst_comp (f : ∀ i, α i) (g : ∀ i, β i) :
    ∃ h : ∀ i, α i × β i, (Prod.fst <| h ·) = f := ⟨(f △' g), fst_comp_prod⟩
theorem exists_snd_comp (f : ∀ i, α i) (g : ∀ i, β i) :
    ∃ h : ∀ i, α i × β i, (Prod.snd <| h ·) = g := ⟨(f △' g), snd_comp_prod⟩

@[grind =]
theorem prod_const_const {γ} {α β} {a : α} {b : β} :
    (Function.const γ a) △' (Function.const γ b) = Function.const γ (a, b) := rfl

end

end Pi

namespace Prod

variable {α β δ ε : Type*} {γ : Sort*}

/-- This is the pairing operation on functions, dual to `Sum.elim`. -/
protected def pair (f : γ → α) (g : γ → β) : γ → α × β := (f △' g)

@[inherit_doc] infixr:65 " △ " => Prod.pair

section

variable (f : γ → α) (g : γ → β)

@[grind =] theorem pair_apply (c : γ) : (f △ g) c = (f c, g c) := rfl

theorem pair_comp {δ} {h : δ → γ} : (f △ g) ∘ h = (f ∘ h) △ (g ∘ h) := rfl

@[simp] theorem fst_pair {c} : ((f △ g) c).fst = f c := rfl
@[simp] theorem snd_pair {c} : ((f △ g) c).snd = g c := rfl

@[simp] theorem pair_fst_snd : fst (α := α)  △ snd (β := β) = id := rfl
@[simp] theorem pair_snd_fst : snd (β := β) △ fst (α := α) = .swap := rfl

@[simp] theorem pair_fst_snd_comp {f : γ → α × β} : (fst ∘ f) △ (snd ∘ f) = f := rfl

@[simp] theorem fst_comp_pair {f : γ → α} {g : γ → β} : fst ∘ (f △ g) = f := rfl
@[simp] theorem snd_comp_pair {f : γ → α} {g : γ → β} : snd ∘ (f △ g) = g := rfl

theorem pair_eq_iff {f f' : γ → α} {g g' : γ → β} : f △ g = f' △ g' ↔
    f = f' ∧ g = g' := by simp [funext_iff, Prod.ext_iff, forall_and]

theorem pair_ext_iff {h h' : γ → α × β} : h = h' ↔
    Prod.fst ∘ h = Prod.fst ∘ h' ∧ Prod.snd ∘ h = (Prod.snd ∘ h') := by
  simp [funext_iff, Prod.ext_iff, forall_and]

theorem exists_prod_apply_eq (h : γ → α × β) : ∃ f g, f △ g = h :=
  ⟨Prod.fst ∘ h, Prod.snd ∘ h, pair_fst_snd_comp⟩

theorem exists_fst_comp (f : γ → α) (g : γ → β) :
    ∃ h : γ → α × β, Prod.fst ∘ h = f := ⟨f △ g, fst_comp_pair⟩
theorem exists_snd_comp (f : γ → α) (g : γ → β) :
    ∃ h : γ → α × β, Prod.snd ∘ h = g := ⟨f △ g, snd_comp_pair⟩

theorem leftInverse_uncurry_pair_pair_fst_comp_snd_comp : Function.LeftInverse
    (Prod.pair (γ := δ)).uncurry ((fst (α := α) ∘ ·) △ (snd (β := β) ∘ ·)) := fun _ => rfl

theorem rightInverse_uncurry_pair_pair_fst_comp_snd_comp : Function.RightInverse
    (Prod.pair (γ := δ)).uncurry ((fst (α := α) ∘ ·) △ (snd (β := β) ∘ ·)) := fun _ => rfl

@[grind =]
theorem pair_const_const (a : α) (b : β) :
    (Function.const γ a) △  (Function.const γ b) = Function.const γ (a, b) := rfl

theorem const_prod {γ} {α β} {p : α × β} :
    Function.const γ p = (Function.const γ p.1) △ (Function.const γ p.2) := rfl

end

section

/- We can define `Prod.map` in terms of `Prod.pair` (TODO: and we should). -/
theorem map_eq_pair {f : α → β} {g : δ → ε} : Prod.map f g =
    (f ∘ fst) △ (g ∘ snd) := rfl

@[grind _=_]
theorem map_pair {f : α → β} {g : γ → α} {h : δ → ε} {k : γ → δ} {c} :
    Prod.map f h ((g △ k) c) = ((f ∘ g) △ (h ∘ k)) c := rfl

theorem map_comp_pair {f : α → β} {g : γ → α} {h : δ → ε} {k : γ → δ} :
    Prod.map f h ∘ (g △ k) = (f ∘ g) △ (h ∘ k) := rfl

end

/-- The diagonal map into Prod. -/
@[expose] protected def diag : α → α × α := id △ id

@[inherit_doc] prefix:max "Δ " => Prod.diag

section

variable {a b : α}

@[grind =] theorem diag_apply : Δ a = (a, a) := rfl

@[simp, grind =] theorem fst_diag : (Δ a).1 = a := rfl
@[simp, grind =] theorem snd_diag : (Δ a).2 = a := rfl

@[simp, grind =] theorem map_diag {f : α → β} {g : α → δ} : Prod.map f g (Δ a) =
    (f △ g) a := rfl

theorem map_comp_diag {f : α → β} {g : α → δ} : Prod.map f g ∘ Prod.diag = (f △ g) := rfl

theorem injective_diag : Function.Injective (α := α) Prod.diag := fun _ _ => congrArg fst

theorem exists_diag_apply_iff (p : α × α) : (∃ a, p = Δ a) ↔ p.1 = p.2 := by
  simp [Prod.ext_iff, eq_comm]

@[simp] theorem diag_eq_iff : Δ a = Δ b ↔ a = b := injective_diag.eq_iff

end

end Prod
