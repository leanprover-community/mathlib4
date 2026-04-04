/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Init

/-!

This file defines `(f ⇊ g)`, the operation that pairs two functions `f : ι → α` and
`g : ι → β` into a function `ι → α × β`.

It also defines the special case when `f = g = id`, `Function.diag`. This is the canonical injection
of a type into its prouduct with itself onto its diagonal.


This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

-/

@[expose] public section

namespace Pi

/-- The mapping into a product type built from maps into each component. -/
protected def prod {ι} {α β : ι → Type*} (f : ∀ i, α i) (g : ∀ i, β i) : ∀ i, α i × β i :=
    fun i ↦ (f i, g i)

@[inherit_doc] infixr:65 " ⇊' " => Pi.prod

section

variable {ι} {α β : ι → Type*} (f f' : ∀ i, α i) (g g' : ∀ i, β i) {c}

@[grind =] theorem prod_apply : (f ⇊' g) c = (f c, g c) := rfl

@[simp] theorem fst_prod : ((f ⇊' g) c).fst = f c := rfl
@[simp] theorem snd_prod : ((f ⇊' g) c).snd = g c := rfl

@[simp] theorem prod_fst_snd {α β} : (Prod.fst : _ → α) ⇊' (Prod.snd : _ → β) = id := rfl
@[simp] theorem prod_snd_fst {α β} : (Prod.snd : _ → β) ⇊' (Prod.fst : _ → α) = .swap := rfl

theorem prod_fst_snd_comp {h : ∀ i, α i × β i} :
   (Prod.fst <| h ·) ⇊' (Prod.snd <| h ·) = h := rfl

theorem fst_comp_prod {f : ∀ i, α i} {g : ∀ i, β i} : (Prod.fst <| (f ⇊' g) ·) = f := rfl
theorem snd_comp_prod {f : ∀ i, α i} {g : ∀ i, β i} : (Prod.snd <| (f ⇊' g) ·) = g := rfl

@[simp]
theorem prod_eq_iff {f : ∀ i, α i} {g : ∀ i, β i} :
    f ⇊' g = f' ⇊' g' ↔ f = f' ∧ g = g' := by simp [funext_iff, Prod.ext_iff, forall_and]

theorem prod_ext_iff {h h' : ∀ i, α i × β i} : h = h' ↔
    (Prod.fst <| h ·) = (Prod.fst <| h' ·) ∧ (Prod.snd <| h ·) = (Prod.snd <| h' ·) := by
  simp [funext_iff, Prod.ext_iff, forall_and]

theorem exists_prod_apply_eq (h : ∀ i, α i × β i) : ∃ f g, (f ⇊' g) = h :=
  ⟨(Prod.fst <| h ·), (Prod.snd <| h ·), prod_fst_snd_comp⟩

theorem exists_fst_comp (f : ∀ i, α i) (g : ∀ i, β i) :
    ∃ h : ∀ i, α i × β i, (Prod.fst <| h ·) = f := ⟨(f ⇊' g), fst_comp_prod⟩
theorem exists_snd_comp (f : ∀ i, α i) (g : ∀ i, β i) :
    ∃ h : ∀ i, α i × β i, (Prod.snd <| h ·) = g := ⟨(f ⇊' g), snd_comp_prod⟩

@[grind =]
theorem prod_const_const {ι} {α β} {a : α} {b : β} :
    (Function.const ι a) ⇊' (Function.const ι b) = Function.const ι (a, b) := rfl

end

end Pi

namespace Function

variable {α β γ δ : Type*} {ι : Sort*}

/-- This is the pairing operation on functions, dual to `Sum.elim`. -/
protected def prod (f : ι → α) (g : ι → β) : ι → α × β := f ⇊' g

@[inherit_doc] infixr:65 " ⇊ " => Function.prod

section

variable (f : ι → α) (g : ι → β)

@[grind =] theorem prod_apply (c : ι) : (f.prod g) c = (f c, g c) := rfl

theorem prod_comp {γ} {h : γ → ι} : (f ⇊ g) ∘ h = (f ∘ h) ⇊ (g ∘ h) := rfl

@[simp] theorem fst_prod {c} : ((f ⇊ g) c).fst = f c := rfl
@[simp] theorem snd_prod {c} : ((f ⇊ g) c).snd = g c := rfl

@[simp] theorem prod_fst_snd : Prod.fst (α := α) ⇊ Prod.snd (β := β) = id := rfl
@[simp] theorem prod_snd_fst : Prod.snd (β := β) ⇊ Prod.fst (α := α) = .swap := rfl

@[simp] theorem prod_fst_snd_comp {f : ι → α × β} : (Prod.fst ∘ f) ⇊ (Prod.snd ∘ f) = f := rfl

@[simp] theorem fst_comp_prod {f : ι → α} {g : ι → β} : Prod.fst ∘ (f ⇊ g) = f := rfl
@[simp] theorem snd_comp_prod {f : ι → α} {g : ι → β} : Prod.snd ∘ (f ⇊ g) = g := rfl

theorem prod_eq_iff {f f' : ι → α} {g g' : ι → β} : f ⇊ g = f' ⇊ g' ↔
    f = f' ∧ g = g' := by simp [funext_iff, Prod.ext_iff, forall_and]

theorem prod_ext_iff {h h' : ι → α × β} : h = h' ↔
    Prod.fst ∘ h = Prod.fst ∘ h' ∧ Prod.snd ∘ h = (Prod.snd ∘ h') := by
  simp [funext_iff, Prod.ext_iff, forall_and]

theorem exists_prod_apply_eq (h : ι → α × β) : ∃ f g, f ⇊ g = h :=
  ⟨Prod.fst ∘ h, Prod.snd ∘ h, prod_fst_snd_comp⟩

theorem exists_fst_comp (f : ι → α) (g : ι → β) :
    ∃ h : ι → α × β, Prod.fst ∘ h = f := ⟨f ⇊ g, fst_comp_prod⟩
theorem exists_snd_comp (f : ι → α) (g : ι → β) :
    ∃ h : ι → α × β, Prod.snd ∘ h = g := ⟨f ⇊ g, snd_comp_prod⟩

theorem leftInverse_uncurry_prod_prod_fst_comp_snd_comp : Function.LeftInverse
    (Function.prod (ι := γ)).uncurry ((Prod.fst (α := α) ∘ ·) ⇊ (Prod.snd (β := β) ∘ ·)) :=
  fun _ => rfl

theorem rightInverse_uncurry_prod_prod_fst_comp_snd_comp : Function.RightInverse
    (Function.prod (ι := γ)).uncurry ((Prod.fst (α := α) ∘ ·) ⇊ (Prod.snd (β := β) ∘ ·)) :=
  fun _ => rfl

@[grind =]
theorem prod_const_const (a : α) (b : β) :
    (Function.const ι a) ⇊  (Function.const ι b) = Function.const ι (a, b) := rfl

theorem const_prod {ι} {α β} {p : α × β} :
    Function.const ι p = (Function.const ι p.1) ⇊ (Function.const ι p.2) := rfl

end

/-- `Function.prodMap` is `Prod.map` in the `Function` namespace. -/
def prodMap (f : α → β) (g : γ → δ) := (f ∘ Prod.fst) ⇊ (g ∘ Prod.snd)

@[simp, grind =]
theorem prodMap_eq_prod_map {f : α → β} {g : γ → δ} : f.prodMap g = Prod.map f g := rfl

@[grind _=_]
theorem map_prod {f : α → β} {g : ι → α} {h : γ → δ} {k : ι → γ} {c} :
    Prod.map f h ((g ⇊ k) c) = ((f ∘ g) ⇊ (h ∘ k)) c := rfl

theorem map_comp_prod {f : α → β} {g : ι → α} {h : γ → δ} {k : ι → γ} :
    Prod.map f h ∘ (g ⇊ k) = (f ∘ g) ⇊ (h ∘ k) := rfl

/-- The diagonal map into `Prod`. -/
protected def diag : α → α × α := id ⇊ id

@[inherit_doc] prefix:max "⇗" => Function.diag

section

variable {a b : α}

@[grind =] theorem diag_apply : ⇗a = (a, a) := rfl

@[simp, grind =] theorem fst_diag : (⇗a).1 = a := rfl
@[simp, grind =] theorem snd_diag : (⇗a).2 = a := rfl

@[simp, grind =] theorem map_diag {f : α → β} {g : α → γ} : Prod.map f g ⇗a = (f ⇊ g) a := rfl

@[simp] theorem map_comp_diag {f : α → β} {g : α → γ} : Prod.map f g ∘ Function.diag = f ⇊ g := rfl

theorem injective_diag : Function.Injective (α := α) Function.diag := fun _ _ => congrArg Prod.fst

@[simp] theorem exists_diag_apply_iff (p : α × α) : (∃ a, ⇗a = p) ↔ p.1 = p.2 := by
  simp [Prod.ext_iff, eq_comm]

@[simp] theorem diag_eq_iff : ⇗a = ⇗b ↔ a = b := injective_diag.eq_iff

@[simp] theorem prod_diag_diag : Function.diag ⇊ Function.diag (α := α) =
    Function.diag ∘ Function.diag := rfl

end

end Function
