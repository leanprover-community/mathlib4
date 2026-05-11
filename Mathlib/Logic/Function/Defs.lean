/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Haitao Zhang
-/
module

public import Mathlib.Init

import Mathlib.Tactic.Attr.Register

/-!
# General operations on functions
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

namespace Function

variable {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₅}

lemma flip_def {f : α → β → φ} : flip f = fun b a => f a b := rfl

/-- Composition of dependent functions: `(f ∘' g) x = f (g x)`, where type of `g x` depends on `x`
and type of `f (g x)` depends on `x` and `g x`. -/
@[inline, reducible]
def dcomp {β : α → Sort u₂} {φ : ∀ {x : α}, β x → Sort u₃} (f : ∀ {x : α} (y : β x), φ y)
    (g : ∀ x, β x) : ∀ x, φ (g x) := fun x => f (g x)

@[inherit_doc] infixr:80 " ∘' " => Function.dcomp

section DComp

variable {ι} {β : ι → Sort*} {φ : ∀ {i : ι}, β i → Sort*} (f : ∀ {i : ι} (y : β i), φ y)
    (g : ∀ i, β i) (i : ι)

theorem dcomp_def : f ∘' g = fun i => f (g i) := rfl

theorem dcomp_apply : dcomp f g i = f (g i) := rfl

@[simp] theorem dcomp_eq_comp {α β γ} (f : β → γ) (g : α → β) : f ∘' g = f ∘ g := rfl
@[simp] theorem id_dcomp {α β} (f : α → β) : id ∘' f = f := rfl
@[simp] theorem dcomp_id {α β} (f : α → β) : f ∘' id = f := rfl

theorem dcomp_assoc {κ : Sort*} (h : κ → ι) : f ∘' g ∘' h = (f ∘' g) ∘' h := rfl

@[simp] theorem const_dcomp {α β γ} (a : α) (g : γ → β) : const β a ∘' g = const γ a := rfl
@[simp] theorem dcomp_const {α β δ} (f : α → δ) (a : α) : f ∘' const β a = const β (f a) := rfl

end DComp

/-- Product of functions: `Function.prod f g i = (f i, g i)`, where the types of `f i` and
`g i` may depend on `i`. -/
protected def prod {ι} {α β : ι → Type*} (f : ∀ i, α i) (g : ∀ i, β i) (i : ι) :
    α i × β i := (f i, g i)

@[simp] lemma prod_apply {ι} {α β : ι → Type*} (f : ∀ i, α i) (g : ∀ i, β i) (i : ι) :
    Function.prod f g i = (f i , g i) := rfl

lemma prod_fst_snd {α β} : Function.prod (Prod.fst : α × β → α) (Prod.snd : α × β → β) = id :=
  rfl
lemma prod_snd_fst {α β} : Function.prod (Prod.snd : α × β → β) (Prod.fst : α × β → α) = .swap :=
  rfl

/-- Given functions `f : β → β → φ` and `g : α → β`, produce a function `α → α → φ` that evaluates
`g` on each argument, then applies `f` to the results. Can be used, e.g., to transfer a relation
from `β` to `α`. -/
abbrev onFun (f : β → β → φ) (g : α → β) : α → α → φ := fun x y => f (g x) (g y)

@[inherit_doc onFun]
scoped infixl:2 " on " => onFun

/-- For a two-argument function `f`, `swap f` is the same function but taking the arguments
in the reverse order. `swap f y x = f x y`. -/
abbrev swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y := fun y x => f x y

theorem swap_def {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : swap f = fun y x => f x y := rfl

theorem onFun_swap_comm (f : β → β → φ) (g : α → β) : (swap f on g) = swap (f on g) := rfl

attribute [mfld_simps] id_comp comp_id

theorem comp_assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ g ∘ h :=
  rfl

/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f

theorem Bijective.comp {g : β → φ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
  | ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩

theorem bijective_id : Bijective (@id α) :=
  ⟨injective_id, surjective_id⟩

variable {f : α → β}

theorem Injective.beq_eq {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (I : Injective f) {a b : α} : (f a == f b) = (a == b) := by
  by_cases h : a == b <;> simp [h] <;> simpa [I.eq_iff] using h

section Bicomp

variable {α β γ δ ε : Sort*}

/-- Compose a binary function `f` with a pair of unary functions `g` and `h`.
If both arguments of `f` have the same type and `g = h`, then `bicompl f g g = f on g`. -/
def bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a b) :=
  f (g a) (h b)

/-- Compose a unary function `f` with a binary function `g`. -/
def bicompr (f : γ → δ) (g : α → β → γ) (a b) :=
  f (g a b)

-- Suggested local notation:
local notation f " ∘₂ " g => bicompr f g

theorem uncurry_bicompr {α β γ δ} (f : α → β → γ) (g : γ → δ) : uncurry (g ∘₂ f) = g ∘ uncurry f :=
  rfl

theorem uncurry_bicompl {α β γ δ ε} (f : γ → δ → ε) (g : α → γ) (h : β → δ) :
    uncurry (bicompl f g h) = uncurry f ∘ Prod.map g h :=
  rfl

end Bicomp

end Function

namespace Function

variable {α : Type u₁} {β : Type u₂}

/-- A point `x` is a fixed point of `f : α → α` if `f x = x`. -/
def IsFixedPt (f : α → α) (x : α) := f x = x

/-- If `x` is a fixed point of `f`, then `f x = x`. This is useful, e.g., for `rw` or `simp`. -/
protected theorem IsFixedPt.eq {f : α → α} {x : α} (hf : IsFixedPt f x) : f x = x :=
  hf

instance IsFixedPt.decidable [h : DecidableEq α] {f : α → α} {x : α} : Decidable (IsFixedPt f x) :=
  h (f x) x

@[nontriviality]
theorem IsFixedPt.of_subsingleton [Subsingleton α] (f : α → α) (x : α) : IsFixedPt f x :=
  Subsingleton.elim _ _

/-- Every point is a fixed point of `id`. -/
theorem isFixedPt_id (x : α) : IsFixedPt id x :=
  rfl

/-- A function fixes every point iff it is the identity. -/
@[simp] theorem forall_isFixedPt_iff {f : α → α} : (∀ x, IsFixedPt f x) ↔ f = id :=
  ⟨funext, fun h ↦ h ▸ isFixedPt_id⟩

end Function

namespace Pi

variable {ι : Sort*} {α β : ι → Sort*}

/-- Sends a dependent function `a : ∀ i, α i` to a dependent function `Pi.map f a : ∀ i, β i`
by applying `f i` to `i`-th component. -/
protected def map (f : ∀ i, α i → β i) : (∀ i, α i) → (∀ i, β i) := fun a i ↦ f i (a i)

@[simp]
lemma map_apply (f : ∀ i, α i → β i) (a : ∀ i, α i) (i : ι) : Pi.map f a i = f i (a i) := rfl

end Pi
