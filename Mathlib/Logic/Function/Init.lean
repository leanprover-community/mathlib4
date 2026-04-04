/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Init

/-!

This file defines `(f ▽ g)`, the operation that pairs two functions `f : ι → α` and
`g : ι → β` into a function `ι → α × β`.

It also defines the special case when `f = g = id`, `Function.diag`. This is the canonical injection
of a type into its prouduct with itself onto its diagonal.


This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

-/

@[expose] public section

namespace Pi

/-- The dependent mapping into a product type built from dependent maps into each component. -/
protected def prod {ι} {α β : ι → Type*} (f : ∀ i, α i) (g : ∀ i, β i) (i : ι) : α i × β i :=
    Prod.mk (f i) (g i)

@[inherit_doc] infixr:95 " ▽' " => Pi.prod

section

variable {ι} {α β : ι → Type*} (f f' : ∀ i, α i) (g g' : ∀ i, β i) {c}

@[simp, grind =] theorem prod_apply : (f ▽' g) c = (f c, g c) := rfl

theorem fst_prod : ((f ▽' g) c).fst = f c := rfl
theorem snd_prod : ((f ▽' g) c).snd = g c := rfl

@[simp] theorem prod_fst_snd {α β} : (Prod.fst : _ → α) ▽' (Prod.snd : _ → β) = id := rfl
@[simp] theorem prod_snd_fst {α β} : (Prod.snd : _ → β) ▽' (Prod.fst : _ → α) = .swap := rfl

theorem prod_fst_snd_comp {h : ∀ i, α i × β i} :
   (Prod.fst <| h ·) ▽' (Prod.snd <| h ·) = h := rfl

theorem fst_comp_prod {f : ∀ i, α i} {g : ∀ i, β i} : (Prod.fst <| (f ▽' g) ·) = f := rfl
theorem snd_comp_prod {f : ∀ i, α i} {g : ∀ i, β i} : (Prod.snd <| (f ▽' g) ·) = g := rfl

@[simp]
theorem prod_eq_iff {f : ∀ i, α i} {g : ∀ i, β i} :
    f ▽' g = f' ▽' g' ↔ f = f' ∧ g = g' := by simp [funext_iff, Prod.ext_iff, forall_and]

theorem prod_ext_iff {h h' : ∀ i, α i × β i} : h = h' ↔
    (Prod.fst <| h ·) = (Prod.fst <| h' ·) ∧ (Prod.snd <| h ·) = (Prod.snd <| h' ·) := by
  simp [funext_iff, Prod.ext_iff, forall_and]

theorem prod_ext {h h' : ∀ i, α i × β i} (h₁ : (Prod.fst <| h ·) = (Prod.fst <| h' ·))
    (h₂ : (Prod.snd <| h ·) = (Prod.snd <| h' ·)) : h = h' := prod_ext_iff.mpr ⟨h₁, h₂⟩

theorem exists_prod_apply_eq (h : ∀ i, α i × β i) : ∃ f g, (f ▽' g) = h :=
  ⟨(Prod.fst <| h ·), (Prod.snd <| h ·), prod_fst_snd_comp⟩

theorem exists_fst_comp (f : ∀ i, α i) (g : ∀ i, β i) :
    ∃ h : ∀ i, α i × β i, (Prod.fst <| h ·) = f := ⟨(f ▽' g), fst_comp_prod⟩
theorem exists_snd_comp (f : ∀ i, α i) (g : ∀ i, β i) :
    ∃ h : ∀ i, α i × β i, (Prod.snd <| h ·) = g := ⟨(f ▽' g), snd_comp_prod⟩

@[grind =]
theorem prod_const_const {ι} {α β} {a : α} {b : β} :
    (Function.const ι a) ▽' (Function.const ι b) = Function.const ι (a, b) := rfl

theorem eq_prod_iff_fst_comp_snd_comp {f g} {h : ∀ i, α i × β i} :
    h = f ▽' g ↔ (Prod.fst <| h ·) = f ∧ (Prod.snd <| h ·) = g := by simp [prod_ext_iff]

theorem eq_prod_of_fst_comp_snd_comp {f g} {h : ∀ i, α i × β i} (h₁ : (Prod.fst <| h ·) = f)
    (h₂ : (Prod.snd <| h ·) = g) : h = f ▽' g := eq_prod_iff_fst_comp_snd_comp.mpr ⟨h₁, h₂⟩

end

end Pi

namespace Function

variable {α β γ δ : Type*} {ι : Sort*}

/-- The map into a product type built from maps into each component. -/
protected def prod : (ι → α) → (ι → β) → ι → α × β := (· ▽' ·)

@[inherit_doc] infixr:95 " ▽ " => Function.prod

section

variable (f : ι → α) (g : ι → β)

@[simp, grind =] theorem prod_apply (c : ι) : (f.prod g) c = (f c, g c) := rfl

theorem prod_comp {γ} {h : γ → ι} : (f ▽ g) ∘ h = (f ∘ h) ▽ (g ∘ h) := rfl

theorem fst_prod {c} : ((f ▽ g) c).fst = f c := by simp
theorem snd_prod {c} : ((f ▽ g) c).snd = g c := by simp

@[simp] theorem prod_fst_snd : Prod.fst (α := α) ▽ Prod.snd (β := β) = id := rfl
@[simp] theorem prod_snd_fst : Prod.snd (β := β) ▽ Prod.fst (α := α) = .swap := rfl

@[simp] theorem prod_fst_snd_comp {f : ι → α × β} : (Prod.fst ∘ f) ▽ (Prod.snd ∘ f) = f := rfl

@[simp] theorem fst_comp_prod {f : ι → α} {g : ι → β} : Prod.fst ∘ (f ▽ g) = f := rfl
@[simp] theorem snd_comp_prod {f : ι → α} {g : ι → β} : Prod.snd ∘ (f ▽ g) = g := rfl

theorem prod_comp_prod {f : ι → α} {g : ι → β} {h : α × β → γ} {k : α × β → δ} :
    (h ▽ k) ∘ (f ▽ g) = (h ∘ (f ▽ g)) ▽ (k ∘ (f ▽ g)) := rfl

theorem comp_prod_comp {f : ι → α} {g : ι → β} {h : α → γ} {k : β → δ} :
    (h ∘ f) ▽ (k ∘ g) = (h ∘ Prod.fst) ▽ (k ∘ Prod.snd) ∘ f ▽ g := rfl

theorem map_comp_prod {f : ι → α} {g : ι → β} {h : α → γ} {k : β → δ} :
    Prod.map h k ∘ f ▽ g = (h ∘ f) ▽ (k ∘ g) := rfl

theorem prod_eq_iff {f f' : ι → α} {g g' : ι → β} : f ▽ g = f' ▽ g' ↔
    f = f' ∧ g = g' := by simp [funext_iff, Prod.ext_iff, forall_and]

theorem prod_ext_iff {h h' : ι → α × β} : h = h' ↔
    Prod.fst ∘ h = Prod.fst ∘ h' ∧ Prod.snd ∘ h = (Prod.snd ∘ h') := by
  simp [funext_iff, Prod.ext_iff, forall_and]

theorem exists_prod_apply_eq (h : ι → α × β) : ∃ f g, f ▽ g = h :=
  ⟨Prod.fst ∘ h, Prod.snd ∘ h, prod_fst_snd_comp⟩

theorem exists_fst_comp (f : ι → α) (g : ι → β) :
    ∃ h : ι → α × β, Prod.fst ∘ h = f := ⟨f ▽ g, fst_comp_prod⟩
theorem exists_snd_comp (f : ι → α) (g : ι → β) :
    ∃ h : ι → α × β, Prod.snd ∘ h = g := ⟨f ▽ g, snd_comp_prod⟩

theorem leftInverse_uncurry_prod_prod_fst_comp_snd_comp : Function.LeftInverse
    (Function.prod (ι := γ)).uncurry ((Prod.fst (α := α) ∘ ·) ▽ (Prod.snd (β := β) ∘ ·)) :=
  fun _ => rfl

theorem rightInverse_uncurry_prod_prod_fst_comp_snd_comp : Function.RightInverse
    (Function.prod (ι := γ)).uncurry ((Prod.fst (α := α) ∘ ·) ▽ (Prod.snd (β := β) ∘ ·)) :=
  fun _ => rfl

@[simp, grind =]
theorem prod_const_const (a : α) (b : β) :
    (Function.const ι a) ▽ (Function.const ι b) = Function.const ι (a, b) := rfl

theorem const_prod {ι} {α β} {p : α × β} :
    Function.const ι p = (Function.const ι p.1) ▽ (Function.const ι p.2) := rfl

theorem eq_prod_iff_fst_comp_snd_comp {f g} {h : ι → α × β} :
    h = f ▽ g ↔ Prod.fst ∘ h = f ∧ Prod.snd ∘ h = g := by simp [prod_ext_iff]

theorem eq_prod_of_fst_comp_snd_comp {f g} {h : ι → α × β} (h₁ : Prod.fst ∘ h = f)
    (h₂ : Prod.snd ∘ h = g) : h = f ▽ g := eq_prod_iff_fst_comp_snd_comp.mpr ⟨h₁, h₂⟩

end

/-- The diagonal map into `Prod`. -/
protected def diag : α → α × α := id ▽ id

@[inherit_doc] prefix:max "⟋" => Function.diag

section

variable {a b : α}

@[grind =] theorem diag_apply : ⟋a = (a, a) := rfl

@[simp] theorem fst_diag : (⟋a).1 = a := rfl
@[simp] theorem snd_diag : (⟋a).2 = a := rfl

theorem map_diag {f : α → β} {g : α → γ} : Prod.map f g ⟋a = (f ▽ g) a := rfl

@[simp] theorem map_comp_diag {f : α → β} {g : α → γ} :
  Prod.map f g ∘ Function.diag = f ▽ g := rfl

theorem injective_diag : Function.Injective (α := α) Function.diag := fun _ _ => congrArg Prod.fst

theorem exists_diag_apply_iff (p : α × α) : (∃ a, ⟋a = p) ↔ p.1 = p.2 := by
  simp [Prod.ext_iff, eq_comm]

theorem diag_eq_iff : ⟋a = ⟋b ↔ a = b := injective_diag.eq_iff

@[simp] theorem diag_prod_diag : Function.diag ▽ Function.diag (α := α) =
    Function.diag ∘ Function.diag := rfl

end

/-- `Function.prodMap` is `Prod.map` in the `Function` namespace. -/
def prodMap (f : α → β) (g : γ → δ) := (f ∘ Prod.fst) ▽ (g ∘ Prod.snd)

section

@[simp, grind =]
theorem prodMap_eq_prod_map {f : α → β} {g : γ → δ} : f.prodMap g = Prod.map f g := rfl

end

end Function
