/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Haitao Zhang
-/
-- a port of core Lean `init/function.lean`

/-!
# General operations on functions
-/

namespace Function

variable {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₁}

@[reducible] def comp_right (f : β → β → β) (g : α → β) : β → α → β :=
λ b a => f b (g a)

@[reducible] def comp_left (f : β → β → β) (g : α → β) : α → β → β :=
λ a b => f (g a) b

/-- Given functions `f : β → β → φ` and `g : α → β`, produce a function `α → α → φ` that evaluates
`g` on each argument, then applies `f` to the results. Can be used, e.g., to transfer a relation
from `β` to `α`. -/
@[reducible] def on_fun (f : β → β → φ) (g : α → β) : α → α → φ :=
λ x y => f (g x) (g y)

@[reducible] def combine (f : α → β → φ) (op : φ → δ → ζ) (g : α → β → δ)
  : α → β → ζ :=
λ x y => op (f x y) (g x y)

@[reducible] def swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y :=
λ y x => f x y

@[reducible] def app {β : α → Sort u₂} (f : ∀ x, β x) (x : α) : β x :=
f x

theorem left_id (f : α → β) : id ∘ f = f := rfl

theorem right_id (f : α → β) : f ∘ id = f := rfl

theorem comp.assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

@[simp] theorem comp.left_id (f : α → β) : id ∘ f = f := rfl

@[simp] theorem comp.right_id (f : α → β) : f ∘ id = f := rfl

theorem comp_const_right (f : β → φ) (b : β) : f ∘ (const α b) = const α (f b) := rfl

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
@[reducible] def injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

theorem injective.comp {g : β → φ} {f : α → β} (hg : injective g) (hf : injective f) :
  injective (g ∘ f) :=
fun _ _ h => hf (hg h)

/-- A function `f : α → β` is calles surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
@[reducible] def surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b

theorem surjective.comp {g : β → φ} {f : α → β} (hg : surjective g) (hf : surjective f) :
  surjective (g ∘ f) :=
λ (c : φ) => Exists.elim (hg c) (λ b hb => Exists.elim (hf b) (λ a ha =>
  Exists.intro a (show g (f a) = c from (Eq.trans (congrArg g ha) hb))))

/-- A function is called bijective if it is both injective and surjective. -/
def bijective (f : α → β) := injective f ∧ surjective f

theorem bijective.comp {g : β → φ} {f : α → β} : bijective g → bijective f → bijective (g ∘ f)
| ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩

/-- `LeftInverse g f` means that g is a left inverse to f. That is, `g ∘ f = id`. -/
def LeftInverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x

/-- `has_LeftInverse f` means that `f` has an unspecified left inverse. -/
def has_LeftInverse (f : α → β) : Prop := ∃ finv : β → α, LeftInverse finv f

/-- `RightInverse g f` means that g is a right inverse to f. That is, `f ∘ g = id`. -/
def RightInverse (g : β → α) (f : α → β) : Prop := LeftInverse f g

/-- `has_RightInverse f` means that `f` has an unspecified right inverse. -/
def has_RightInverse (f : α → β) : Prop := ∃ finv : β → α, RightInverse finv f

theorem LeftInverse.injective {g : β → α} {f : α → β} : LeftInverse g f → injective f :=
λ h a b hf => h a ▸ h b ▸ hf ▸ rfl

theorem has_LeftInverse.injective {f : α → β} : has_LeftInverse f → injective f :=
λ h => Exists.elim h (λ finv inv => inv.injective)

theorem RightInverse_of_injective_of_LeftInverse {f : α → β} {g : β → α}
    (injf : injective f) (lfg : LeftInverse f g) :
  RightInverse f g :=
λ x => injf $ lfg $ f x

theorem RightInverse.surjective {f : α → β} {g : β → α} (h : RightInverse g f) : surjective f :=
λ y => ⟨g y, h y⟩

theorem has_RightInverse.surjective {f : α → β} : has_RightInverse f → surjective f
| ⟨finv, inv⟩ => inv.surjective

theorem LeftInverse_of_surjective_of_RightInverse {f : α → β} {g : β → α} (surjf : surjective f)
  (rfg : RightInverse f g) : LeftInverse f g :=
λ y =>
  let ⟨x, hx⟩ := surjf y
  by rw [← hx, rfg]

theorem injective_id : injective (@id α) := fun _ _ => id

theorem surjective_id : surjective (@id α) := λ a => ⟨a, rfl⟩

theorem bijective_id : bijective (@id α) := ⟨injective_id, surjective_id⟩

end Function

namespace Function

variable {α : Type u₁} {β : Type u₂} {φ : Type u₃}

/-- Interpret a function on `α × β` as a function with two arguments. -/
@[inline] def curry : (α × β → φ) → α → β → φ :=
λ f a b => f (a, b)

/-- Interpret a function with two arguments as a function on `α × β` -/
@[inline] def uncurry : (α → β → φ) → α × β → φ :=
λ f a => f a.1 a.2

@[simp] theorem curry_uncurry (f : α → β → φ) : curry (uncurry f) = f :=
rfl

@[simp] theorem uncurry_curry (f : α × β → φ) : uncurry (curry f) = f :=
funext (λ ⟨a, b⟩ => rfl)

protected theorem LeftInverse.id {g : β → α} {f : α → β} (h : LeftInverse g f) : g ∘ f = id :=
funext h

protected theorem RightInverse.id {g : β → α} {f : α → β} (h : RightInverse g f) : f ∘ g = id :=
funext h

end Function
