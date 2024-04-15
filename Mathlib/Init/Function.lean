/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Haitao Zhang
-/
import Mathlib.Tactic.Basic
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Eqns
import Mathlib.Tactic.TypeStar

#align_import init.function from "leanprover-community/lean"@"03a6a6015c0b12dce7b36b4a1f7205a92dfaa592"

/-!
# General operations on functions
-/

universe u₁ u₂ u₃ u₄ u₅

namespace Function

-- Porting note: fix the universe of `ζ`, it used to be `u₁`
variable {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₅}

#align function.comp Function.comp

attribute [eqns comp_def] comp

lemma flip_def {f : α → β → φ} : flip f = fun b a => f a b := rfl

-- Adaptation note: nightly-2024-03-16
-- Because of changes in how equation lemmas are generated,
-- `@[eqns]` will only work properly when used immediately after the definition
-- (and when none of the default equation lemmas are needed).
-- Thus this usage is no longer allowed:
-- attribute [eqns flip_def] flip

/-- Composition of dependent functions: `(f ∘' g) x = f (g x)`, where type of `g x` depends on `x`
and type of `f (g x)` depends on `x` and `g x`. -/
@[inline, reducible]
def dcomp {β : α → Sort u₂} {φ : ∀ {x : α}, β x → Sort u₃} (f : ∀ {x : α} (y : β x), φ y)
    (g : ∀ x, β x) : ∀ x, φ (g x) := fun x => f (g x)
#align function.dcomp Function.dcomp

@[inherit_doc] infixr:80 " ∘' " => Function.dcomp

@[reducible, deprecated] -- Deprecated since 13 January 2024
def compRight (f : β → β → β) (g : α → β) : β → α → β := fun b a => f b (g a)
#align function.comp_right Function.compRight

@[reducible, deprecated] -- Deprecated since 13 January 2024
def compLeft (f : β → β → β) (g : α → β) : α → β → β := fun a b => f (g a) b
#align function.comp_left Function.compLeft

/-- Given functions `f : β → β → φ` and `g : α → β`, produce a function `α → α → φ` that evaluates
`g` on each argument, then applies `f` to the results. Can be used, e.g., to transfer a relation
from `β` to `α`. -/
@[reducible]
def onFun (f : β → β → φ) (g : α → β) : α → α → φ := fun x y => f (g x) (g y)
#align function.on_fun Function.onFun

@[inherit_doc onFun]
infixl:2 " on " => onFun

/-- Given functions `f : α → β → φ`, `g : α → β → δ` and a binary operator `op : φ → δ → ζ`,
produce a function `α → β → ζ` that applies `f` and `g` on each argument and then applies
`op` to the results.
-/
-- Porting note: the ζ variable was originally constrained to `Sort u₁`, but this seems to
-- have been an oversight.
@[reducible, deprecated] -- Deprecated since 13 January 2024
def combine (f : α → β → φ) (op : φ → δ → ζ) (g : α → β → δ) : α → β → ζ := fun x y =>
  op (f x y) (g x y)
#align function.combine Function.combine

#align function.const Function.const

@[reducible]
def swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y := fun y x => f x y
#align function.swap Function.swap

-- Adaptation note: nightly-2024-03-16: added to replace simp [Function.swap]
theorem swap_def {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : swap f = fun y x => f x y := rfl

@[reducible, deprecated] -- Deprecated since 13 January 2024
def app {β : α → Sort u₂} (f : ∀ x, β x) (x : α) : β x :=
  f x
#align function.app Function.app

-- Porting note: removed, it was never used
-- notation f " -[" op "]- " g => combine f op g

@[simp, mfld_simps]
theorem id_comp (f : α → β) : id ∘ f = f := rfl
#align function.left_id Function.id_comp
#align function.comp.left_id Function.id_comp

@[deprecated] alias left_id := id_comp -- Deprecated since 14 January 2014
@[deprecated] alias comp.left_id := id_comp -- Deprecated since 14 January 2014

@[simp, mfld_simps]
theorem comp_id (f : α → β) : f ∘ id = f := rfl
#align function.right_id Function.comp_id
#align function.comp.right_id Function.comp_id

@[deprecated] alias right_id := comp_id -- Deprecated since 14 January 2014
@[deprecated] alias comp.right_id := comp_id -- Deprecated since 14 January 2014

#align function.comp_app Function.comp_apply

theorem comp.assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ g ∘ h :=
  rfl
#align function.comp.assoc Function.comp.assoc

@[simp] theorem const_comp {γ : Sort*} (f : α → β) (c : γ) : const β c ∘ f = const α c := rfl
#align function.const_comp Function.const_comp

@[simp] theorem comp_const (f : β → φ) (b : β) : f ∘ const α b = const α (f b) := rfl
#align function.comp_const_right Function.comp_const

@[deprecated] alias comp_const_right := comp_const -- Deprecated since 14 January 2014

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
#align function.injective Function.Injective

theorem Injective.comp {g : β → φ} {f : α → β} (hg : Injective g) (hf : Injective f) :
    Injective (g ∘ f) := fun _a₁ _a₂ => fun h => hf (hg h)
#align function.injective.comp Function.Injective.comp

/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b
#align function.surjective Function.Surjective

theorem Surjective.comp {g : β → φ} {f : α → β} (hg : Surjective g) (hf : Surjective f) :
    Surjective (g ∘ f) := fun c : φ =>
  Exists.elim (hg c) fun b hb =>
    Exists.elim (hf b) fun a ha =>
      Exists.intro a (show g (f a) = c from Eq.trans (congr_arg g ha) hb)
#align function.surjective.comp Function.Surjective.comp

/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f
#align function.bijective Function.Bijective

theorem Bijective.comp {g : β → φ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
  | ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩
#align function.bijective.comp Function.Bijective.comp

/-- `LeftInverse g f` means that g is a left inverse to f. That is, `g ∘ f = id`. -/
def LeftInverse (g : β → α) (f : α → β) : Prop :=
  ∀ x, g (f x) = x
#align function.left_inverse Function.LeftInverse

/-- `HasLeftInverse f` means that `f` has an unspecified left inverse. -/
def HasLeftInverse (f : α → β) : Prop :=
  ∃ finv : β → α, LeftInverse finv f
#align function.has_left_inverse Function.HasLeftInverse

/-- `RightInverse g f` means that g is a right inverse to f. That is, `f ∘ g = id`. -/
def RightInverse (g : β → α) (f : α → β) : Prop :=
  LeftInverse f g
#align function.right_inverse Function.RightInverse

/-- `HasRightInverse f` means that `f` has an unspecified right inverse. -/
def HasRightInverse (f : α → β) : Prop :=
  ∃ finv : β → α, RightInverse finv f
#align function.has_right_inverse Function.HasRightInverse

theorem LeftInverse.injective {g : β → α} {f : α → β} : LeftInverse g f → Injective f :=
  fun h a b faeqfb =>
  calc
    a = g (f a) := (h a).symm
    _ = g (f b) := congr_arg g faeqfb
    _ = b := h b
#align function.left_inverse.injective Function.LeftInverse.injective

theorem HasLeftInverse.injective {f : α → β} : HasLeftInverse f → Injective f := fun h =>
  Exists.elim h fun _finv inv => inv.injective
#align function.has_left_inverse.injective Function.HasLeftInverse.injective

theorem rightInverse_of_injective_of_leftInverse {f : α → β} {g : β → α} (injf : Injective f)
    (lfg : LeftInverse f g) : RightInverse f g := fun x =>
  have h : f (g (f x)) = f x := lfg (f x)
  injf h
#align function.right_inverse_of_injective_of_left_inverse Function.rightInverse_of_injective_of_leftInverse

theorem RightInverse.surjective {f : α → β} {g : β → α} (h : RightInverse g f) : Surjective f :=
  fun y => ⟨g y, h y⟩
#align function.right_inverse.surjective Function.RightInverse.surjective

theorem HasRightInverse.surjective {f : α → β} : HasRightInverse f → Surjective f
  | ⟨_finv, inv⟩ => inv.surjective
#align function.has_right_inverse.surjective Function.HasRightInverse.surjective

theorem leftInverse_of_surjective_of_rightInverse {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  Exists.elim (surjf y) fun x hx =>
    calc
      f (g y) = f (g (f x)) := hx ▸ rfl
      _ = f x := Eq.symm (rfg x) ▸ rfl
      _ = y := hx
#align function.left_inverse_of_surjective_of_right_inverse Function.leftInverse_of_surjective_of_rightInverse

theorem injective_id : Injective (@id α) := fun _a₁ _a₂ h => h
#align function.injective_id Function.injective_id

theorem surjective_id : Surjective (@id α) := fun a => ⟨a, rfl⟩
#align function.surjective_id Function.surjective_id

theorem bijective_id : Bijective (@id α) :=
  ⟨injective_id, surjective_id⟩
#align function.bijective_id Function.bijective_id

end Function

namespace Function

variable {α : Type u₁} {β : Type u₂} {φ : Type u₃}

/-- Interpret a function on `α × β` as a function with two arguments. -/
@[inline]
def curry : (α × β → φ) → α → β → φ := fun f a b => f (a, b)
#align function.curry Function.curry

/-- Interpret a function with two arguments as a function on `α × β` -/
@[inline]
def uncurry : (α → β → φ) → α × β → φ := fun f a => f a.1 a.2
#align function.uncurry Function.uncurry

@[simp]
theorem curry_uncurry (f : α → β → φ) : curry (uncurry f) = f :=
  rfl
#align function.curry_uncurry Function.curry_uncurry

@[simp]
theorem uncurry_curry (f : α × β → φ) : uncurry (curry f) = f :=
  funext fun ⟨_a, _b⟩ => rfl
#align function.uncurry_curry Function.uncurry_curry

protected theorem LeftInverse.id {g : β → α} {f : α → β} (h : LeftInverse g f) : g ∘ f = id :=
  funext h
#align function.left_inverse.id Function.LeftInverse.id

protected theorem RightInverse.id {g : β → α} {f : α → β} (h : RightInverse g f) : f ∘ g = id :=
  funext h
#align function.right_inverse.id Function.RightInverse.id

end Function
