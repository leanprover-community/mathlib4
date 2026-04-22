/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Init

/-!
# Dependent composition, pairing, and diagonal for functions

This file develops a small API around pairing and diagonal maps on (possibly dependent) functions,
living in the `Function` namespace so that dot notation is available.

## Main definitions

* `Function.dcomp` (notation `∘'`): dependent composition of functions.
* `Function.prod` (notation `▽`): given `f : ∀ i, α i` and `g : ∀ i, β i`, the pointwise pair
  `fun i ↦ (f i, g i)`.
* `Function.fstComp`, `Function.sndComp`: the two components of a function `h : ∀ i, α i × β i`,
  inverse to `Function.prod`.
* `Function.diag` (notation `⟋`): the diagonal `a ↦ (a, a)`, i.e. `id ▽ id`.
* `Function.prodMap`: `Prod.map` re-exposed under `Function` so that `f.prodMap g` works via dot
  notation.

This file should not depend on anything defined in Mathlib (other than notation), so that it can
be upstreamed to Batteries or the Lean standard library easily.
-/

@[expose] public section

namespace Function

/- ### Dependent composition -/

/-- Composition of dependent functions: `(f ∘' g) i = f (g i)`, where the type of `g i` depends on
`i` and the type of `f (g i)` depends on `i` and `g i`. -/
@[inline, reducible] def dcomp {ι} {β : ι → Sort*} {φ : ∀ {i : ι}, β i → Sort*}
    (f : ∀ {i : ι} (y : β i), φ y) (g : ∀ i, β i) (i : ι) : φ (g i) := f (g i)

@[inherit_doc] infixr:90 " ∘' " => dcomp

section

variable {ι} {β : ι → Sort*} {φ : ∀ {i : ι}, β i → Sort*} (f : ∀ {i : ι} (y : β i), φ y)
    (g : ∀ i, β i) (i : ι)

theorem dcomp_apply : dcomp f g i = f (g i) := rfl

theorem dcomp_def : f ∘' g = fun i => f (g i) := rfl

@[simp] theorem dcomp_eq_comp {α β γ} (f : β → γ) (g : α → β) : f ∘' g = f ∘ g := rfl

@[simp] theorem id_dcomp {α β} (f : α → β) : (fun {_} => id) ∘' f = f := rfl

@[simp] theorem dcomp_id {α β} (f : α → β) : f ∘' (id : α → α) = f := rfl

theorem dcomp_assoc {κ : Sort*} (h : κ → ι) : f ∘' g ∘' h = (f ∘' g) ∘' h := rfl

@[simp] theorem const_dcomp {α β γ} (a : α) (g : γ → β) :
    (const β a) ∘' g = const γ a := rfl

@[simp] theorem dcomp_const {α β δ} (f : α → δ) (a : α) :
    f ∘' (const β a) = const β (f a) := rfl

end

/-- Product of functions: `(f ▽ g) i = (f i, g i)`, where the types of `f i` and `g i`
may depend on `i`. -/
@[inline] def prod {ι} {α β : ι → Type*} (f : ∀ i, α i) (g : ∀ i, β i) (i : ι) :
    α i × β i := ⟨f i, g i⟩

/-- The first component of a map into a product. -/
@[inline] def fstComp {ι} {α β : ι → Type*} (h : (i : ι) → α i × β i) (i : ι) :
    α i := (h i).1

/-- The second component of a map into a product. -/
@[inline] def sndComp {ι} {α β : ι → Type*} (h : (i : ι) → α i × β i) (i : ι) :
    β i := (h i).2

@[inherit_doc] infixr:95 " ▽ " => prod

section

variable {ι κ} {α β : ι → Type*} (f f' : ∀ i, α i) (g g' : ∀ i, β i) (h : ∀ i, α i × β i)
  (i : ι)

@[simp, grind =] theorem prod_apply : (f ▽ g) i = (f i, g i) := rfl
@[simp, grind =] theorem fstComp_apply : fstComp h i = (h i).1 := rfl
@[simp, grind =] theorem sndComp_apply : sndComp h i = (h i).2 := rfl

theorem prod_def : f ▽ g = fun i => (f i, g i) := rfl

theorem fst_dcomp : Prod.fst ∘' h = fstComp h := rfl
theorem snd_dcomp : Prod.snd ∘' h = sndComp h := rfl

@[simp, grind! .] theorem fstComp_prod {f : ∀ i, α i} {g : ∀ i, β i} :
    fstComp (f ▽ g) = f := rfl
@[simp, grind! .] theorem sndComp_prod {f : ∀ i, α i} {g : ∀ i, β i} :
    sndComp (f ▽ g) = g := rfl
@[simp, grind! .] theorem fstComp_prod_sndComp {h : ∀ i, α i × β i} :
  fstComp h ▽ sndComp h = h := rfl

theorem fstComp_sndComp_ext {h h' : ∀ i, α i × β i} (H₁ : fstComp h = fstComp h')
    (H₂ : sndComp h = sndComp h') : h = h' := by grind

theorem fstComp_sndComp_ext_iff {h h' : ∀ i, α i × β i} :
    h = h' ↔ fstComp h = fstComp h' ∧ sndComp h = sndComp h' := by grind

theorem left_eq_of_prod_eq (H : f ▽ g = f' ▽ g') : f = f' := by grind
theorem right_eq_of_prod_eq (H : f ▽ g = f' ▽ g') : g = g' := by grind

@[simp] theorem prod_inj {f f' : ∀ i, α i} {g g' : ∀ i, β i} :
    f ▽ g = f' ▽ g' ↔ f = f' ∧ g = g' := by grind

theorem exists_pair_prod : ∃ f g, f ▽ g = h :=
  ⟨fstComp h, sndComp h, fstComp_prod_sndComp⟩
theorem exists_fstComp [Nonempty (∀ i, β i)] : ∃ h : ∀ i, α i × β i, fstComp h = f :=
  ⟨f ▽ Classical.ofNonempty, fstComp_prod⟩
theorem exists_sndComp [Nonempty (∀ i, α i)] : ∃ h : ∀ i, α i × β i, sndComp h = g :=
  ⟨Classical.ofNonempty ▽ g, sndComp_prod⟩

theorem prod_eq_iff : f ▽ g = h ↔ f = fstComp h ∧ g = sndComp h := by grind
theorem eq_prod_iff : h = f ▽ g ↔ fstComp h = f ∧ sndComp h = g := by grind

theorem prod_dcomp (h : κ → ι) : (f ▽ g) ∘' h = (f ∘' h) ▽ (g ∘' h) := rfl

theorem dcomp_prod_dcomp {γ : ∀ {i : ι}, α i → Type*} {δ : ∀ {i : ι}, β i → Type*}
    (h : ∀ {i : ι}, (a : α i) → γ a) (k : ∀ {i : ι}, (b : β i) → δ b) :
    (h ∘' f) ▽ (k ∘' g) = (h ∘' Prod.fst) ▽ (k ∘' Prod.snd) ∘' f ▽ g := rfl

@[simp] theorem swap_dcomp_prod : Prod.swap ∘' (f ▽ g) = g ▽ f := rfl

end

section

variable {ι : Type*} {α β : ι → Type*}

theorem leftInverse_uncurry_prod_fstComp_prod_sndComp :
    LeftInverse prod.uncurry (fstComp (α := α) ▽ sndComp (β := β)) := by
  simp [LeftInverse]

theorem rightInverse_uncurry_prod_fstComp_prod_sndComp :
    RightInverse prod.uncurry (fstComp (α := α) ▽ sndComp (β := β)) := by
  simp [RightInverse, LeftInverse]

theorem uncurry_prod_injective : (prod (α := α) (β := β)).uncurry.Injective :=
  rightInverse_uncurry_prod_fstComp_prod_sndComp.injective

theorem uncurry_prod_surjective : (prod (α := α) (β := β)).uncurry.Surjective :=
  RightInverse.surjective leftInverse_uncurry_prod_fstComp_prod_sndComp

end

section

variable {α β γ δ : Type*} {ι κ : Sort*} (f : ι → α) (g : ι → β)
  (a : α) (b : β) (p : α × β)

theorem fst_comp (h : ι → α × β) : Prod.fst ∘ h = fstComp h := rfl
theorem snd_comp (h : ι → α × β) : Prod.snd ∘ h = sndComp h := rfl

@[simp] theorem fstComp_mk : fstComp (Prod.mk a : β → α × β) = const β a := rfl
@[simp] theorem sndComp_mk : sndComp (Prod.mk a : β → α × β) = id := rfl

@[simp] theorem fstComp_mk_flip : fstComp ((Prod.mk · b) : α → α × β) = id := rfl
@[simp] theorem sndComp_mk_flip : sndComp ((Prod.mk · b) : α → α × β) = const α b := rfl

@[simp] theorem fst_prod_snd : (Prod.fst : _ → α) ▽ (Prod.snd : _ → β) = id := rfl
@[simp] theorem snd_prod_fst : (Prod.snd : _ → β) ▽ (Prod.fst : _ → α) = .swap := rfl

@[simp] theorem const_prod_const : const ι a ▽ const ι b = const ι (a, b) := rfl

theorem const_of_prod : const ι p = (const ι p.1) ▽ (const ι p.2) := rfl

theorem prod_comp (h : κ → ι) : (f ▽ g) ∘ h = (f ∘ h) ▽ (g ∘ h) := rfl

theorem comp_prod_comp (h : α → γ) (k : β → δ) :
    (h ∘ f) ▽ (k ∘ g) = (h ∘ Prod.fst) ▽ (k ∘ Prod.snd) ∘ f ▽ g := rfl

theorem map_comp_prod (h : α → γ) (k : β → δ) :
    Prod.map h k ∘ f ▽ g = (h ∘ f) ▽ (k ∘ g) := rfl

@[simp] theorem swap_comp_prod : Prod.swap ∘ (f ▽ g) = g ▽ f := rfl

end

/-- The diagonal map into `Prod`. -/
@[inline] def diag {α} : α → α × α := id ▽ id

@[inherit_doc] prefix:max "⟋" => diag

section

variable {α β γ} (f : α → β) (g : α → γ) (a b : α)

@[simp, grind =] theorem diag_apply : ⟋a = (a, a) := rfl

@[simp] theorem id_prod_id : id ▽ id = diag (α := α) := rfl
@[simp] theorem fstComp_diag : fstComp (diag (α := α)) = id := rfl
@[simp] theorem sndComp_diag : sndComp (diag (α := α)) = id := rfl

@[simp] theorem diag_comp : diag ∘ f = f ▽ f := rfl

@[simp] theorem map_comp_diag : Prod.map f g ∘ diag = f ▽ g := rfl

theorem injective_diag : Injective (α := α) diag := fun _ _ => congrArg Prod.fst

theorem exists_diag_apply_iff (p : α × α) : (∃ a, ⟋a = p) ↔ p.1 = p.2 := by
  simp [Prod.ext_iff]

@[simp] theorem swap_comp_diag : Prod.swap ∘ diag = diag (α := α) := rfl

end

/-- Dot-notation alias for `Prod.map`. Collapses to `Prod.map` under `simp` via
`prodMap_eq_prod_map`, so existing `Prod.map` API applies unchanged. -/
@[inline] def prodMap {α₁ α₂ β₁ β₂} (f : α₁ → α₂) (g : β₁ → β₂) : α₁ × β₁ → α₂ × β₂ :=
  (f ∘ Prod.fst) ▽ (g ∘ Prod.snd)

section

variable {α₁ α₂ α₃ β₁ β₂ β₃} (f f₁ : α₁ → α₂) (f₂ : α₂ → α₃) (g g₁ : β₁ → β₂) (g₂ : β₂ → β₃)
    (p : α₁ × β₁)

theorem prodMap_apply : f.prodMap g p = (f p.1, g p.2) := rfl

theorem prodMap_comp : f₂.prodMap g₂ ∘ f₁.prodMap g₁ = (f₂ ∘ f₁).prodMap (g₂ ∘ g₁) := rfl

@[simp] theorem prodMap_id : (id : α₁ → α₁).prodMap (id : β₁ → β₁) = id := rfl

@[simp, grind =]
theorem prodMap_eq_prod_map : f.prodMap g = Prod.map f g := rfl

end

end Function
