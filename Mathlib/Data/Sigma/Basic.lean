/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Init.Function
import Std.Tactic.Ext
import Mathlib.Logic.Function.Basic

/-!
# Sigma types

This file proves basic results about sigma types.

A sigma type is a dependent pair type. Like `α × β` but where the type of the second component
depends on the first component. More precisely, given `β : ι → Type*`, `Sigma β` is made of stuff
which is of type `β i` for some `i : ι`, so the sigma type is a disjoint union of types.
For example, the sum type `X ⊕ Y` can be emulated using a sigma type, by taking `ι` with
exactly two elements (see `Equiv.sumEquivSigmaBool`).

`Σ x, A x` is notation for `Sigma A` (note that this is `\Sigma`, not the sum operator `∑`).
`Σ x y z ..., A x y z ...` is notation for `Σ x, Σ y, Σ z, ..., A x y z ...`. Here we have
`α : Type _`, `β : α → Type _`, `γ : Π a : α, β a → Type _`, ...,
`A : Π (a : α) (b : β a) (c : γ a b) ..., Type _`  with `x : α` `y : β x`, `z : γ x y`, ...

## Notes

The definition of `Sigma` takes values in `Type _`. This effectively forbids `Prop`- valued sigma
types. To that effect, we have `PSigma`, which takes value in `Sort _` and carries a more
complicated universe signature as a consequence.
-/

section Sigma

variable {α α₁ α₂ : Type _} {β : α → Type _} {β₁ : α₁ → Type _} {β₂ : α₂ → Type _}

namespace Sigma

instance [Inhabited α] [Inhabited (β default)] : Inhabited (Sigma β) :=
  ⟨⟨default, default⟩⟩

instance [h₁ : DecidableEq α] [h₂ : ∀ a, DecidableEq (β a)] : DecidableEq (Sigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, isTrue (Eq.refl _) =>
      match b₁, b₂, h₂ _ b₁ b₂ with
      | _, _, isTrue (Eq.refl _) => isTrue rfl
      | _, _, isFalse n => isFalse fun h => Sigma.noConfusion h fun _ e₂ => n <| eq_of_heq e₂
    | _, _, _, _, isFalse n => isFalse fun h => Sigma.noConfusion h fun e₁ _ => n e₁

-- sometimes the built-in injectivity support does not work
@[simp] -- @[nolint simpNF]
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ HEq b₁ b₂ :=
  ⟨λ h => by cases h; exact ⟨rfl, heq_of_eq rfl⟩, -- in Lean 3 `simp` solved this
   λ ⟨h₁, h₂⟩ => by subst h₁; rw [eq_of_heq h₂]⟩

@[simp]
theorem eta : ∀ x : Σa, β a, Sigma.mk x.1 x.2 = x
  | ⟨_, _⟩ => rfl

@[ext]
theorem ext {x₀ x₁ : Sigma β} (h₀ : x₀.1 = x₁.1) (h₁ : HEq x₀.2 x₁.2) : x₀ = x₁ := by
  cases x₀; cases x₁; cases h₀; cases h₁; rfl

theorem ext_iff {x₀ x₁ : Sigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ HEq x₀.2 x₁.2 := by
  cases x₀; cases x₁; exact Sigma.mk.inj_iff

/-- A specialized ext lemma for equality of sigma types over an indexed subtype. -/
@[ext]
theorem subtype_ext {β : Type _} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σa, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

theorem subtype_ext_iff {β : Type _} {p : α → β → Prop} {x₀ x₁ : Σa, Subtype (p a)} :
    x₀ = x₁ ↔ x₀.fst = x₁.fst ∧ (x₀.snd : β) = x₁.snd :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => subtype_ext h₁ h₂⟩

@[simp]
theorem «forall» {p : (Σa, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

@[simp]
theorem «exists» {p : (Σa, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) (x : Sigma β₁) : Sigma β₂ :=
  ⟨f₁ x.1, f₂ x.1 x.2⟩

end Sigma

theorem sigma_mk_injective {i : α} : Function.Injective (@Sigma.mk α β i)
  | _, _, rfl => rfl

theorem Function.Injective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
  (h₁ : Function.Injective f₁) (h₂ : ∀ a, Function.Injective (f₂ a)) :
    Function.Injective (Sigma.map f₁ f₂)
  | ⟨i, x⟩, ⟨j, y⟩, h => by
    obtain rfl : i = j := h₁ (Sigma.mk.inj_iff.mp h).1
    obtain rfl : x = y := h₂ i (sigma_mk_injective h)
    rfl

theorem Function.Injective.of_sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h : Function.Injective (Sigma.map f₁ f₂)) (a : α₁) : Function.Injective (f₂ a) :=
  fun x y hxy =>
  sigma_mk_injective <| @h ⟨a, x⟩ ⟨a, y⟩ (Sigma.ext rfl (heq_of_eq hxy))

theorem Function.Injective.sigma_map_iff {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
  (h₁ : Function.Injective f₁) :
    Function.Injective (Sigma.map f₁ f₂) ↔ ∀ a, Function.Injective (f₂ a) :=
  ⟨fun h => h.of_sigma_map, h₁.sigma_map⟩

theorem Function.Surjective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
  (h₁ : Function.Surjective f₁) (h₂ : ∀ a, Function.Surjective (f₂ a)) :
    Function.Surjective (Sigma.map f₁ f₂) := by
  simp only [Function.Surjective, Sigma.forall, h₁.forall]
  exact fun i => (h₂ _).forall.2 fun x => ⟨⟨i, x⟩, rfl⟩

/-- Interpret a function on `Σ x : α, β x` as a dependent function with two arguments.

This also exists as an `equiv` as `equiv.Pi_curry γ`. -/
def Sigma.curry {γ : ∀ a, β a → Type _} (f : ∀ x : Sigma β, γ x.1 x.2) (x : α) (y : β x) : γ x y :=
  f ⟨x, y⟩

/-- Interpret a dependent function with two arguments as a function on `Σ x : α, β x`.

This also exists as an `equiv` as `(equiv.Pi_curry γ).symm`. -/
def Sigma.uncurry {γ : ∀ a, β a → Type _} (f : ∀ (x) (y : β x), γ x y) (x : Sigma β) : γ x.1 x.2 :=
  f x.1 x.2

@[simp]
theorem Sigma.uncurry_curry {γ : ∀ a, β a → Type _} (f : ∀ x : Sigma β, γ x.1 x.2) :
    Sigma.uncurry (Sigma.curry f) = f :=
  funext fun ⟨_, _⟩ => rfl

@[simp]
theorem Sigma.curry_uncurry {γ : ∀ a, β a → Type _} (f : ∀ (x) (y : β x), γ x y) :
    Sigma.curry (Sigma.uncurry f) = f :=
  rfl

/-- Convert a product type to a Σ-type. -/
def Prod.toSigma {α β} (p : α × β) : Σ_ : α, β :=
  ⟨p.1, p.2⟩

@[simp]
theorem Prod.fst_comp_to_sigma {α β} : Sigma.fst ∘ @Prod.toSigma α β = Prod.fst :=
  rfl

@[simp]
theorem Prod.fst_to_sigma {α β} (x : α × β) : (Prod.toSigma x).fst = x.fst :=
  rfl

@[simp]
theorem Prod.snd_to_sigma {α β} (x : α × β) : (Prod.toSigma x).snd = x.snd :=
  rfl

@[simp]
theorem Prod.to_sigma_mk {α β} (x : α) (y : β) : (x, y).toSigma = ⟨x, y⟩ :=
  rfl

-- Porting note: the meta instance `has_reflect (Σa, β a)` was removed here.

end Sigma

namespace PSigma

variable {α : Sort _} {β : α → Sort _}

/-- Nondependent eliminator for `psigma`. -/
def elim {γ} (f : ∀ a, β a → γ) (a : PSigma β) : γ :=
  PSigma.casesOn a f

@[simp]
theorem elim_val {γ} (f : ∀ a, β a → γ) (a b) : PSigma.elim f ⟨a, b⟩ = f a b :=
  rfl

instance [Inhabited α] [Inhabited (β default)] : Inhabited (PSigma β) :=
  ⟨⟨default, default⟩⟩

instance [h₁ : DecidableEq α] [h₂ : ∀ a, DecidableEq (β a)] : DecidableEq (PSigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, isTrue (Eq.refl _) =>
      match b₁, b₂, h₂ _ b₁ b₂ with
      | _, _, isTrue (Eq.refl _) => isTrue rfl
      | _, _, isFalse n => isFalse fun h => PSigma.noConfusion h fun _ e₂ => n <| eq_of_heq e₂
    | _, _, _, _, isFalse n => isFalse fun h => PSigma.noConfusion h fun e₁ _ => n e₁

-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/porting.20data.2Esigma.2Ebasic/near/304855864
-- for an explanation of why this is currently needed. It generates `PSigma.mk.inj`.
-- This could be done elsewhere.
gen_injective_theorems% PSigma

theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    @PSigma.mk α β a₁ b₁ = @PSigma.mk α β a₂ b₂ ↔ a₁ = a₂ ∧ HEq b₁ b₂ :=
  (Iff.intro PSigma.mk.inj) fun ⟨h₁, h₂⟩ =>
    match a₁, a₂, b₁, b₂, h₁, h₂ with
    | _, _, _, _, Eq.refl _, HEq.refl _ => rfl

@[ext]
theorem ext {x₀ x₁ : PSigma β} (h₀ : x₀.1 = x₁.1) (h₁ : HEq x₀.2 x₁.2) : x₀ = x₁ := by
  cases x₀; cases x₁; cases h₀; cases h₁; rfl

theorem ext_iff {x₀ x₁ : PSigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ HEq x₀.2 x₁.2 := by
  cases x₀; cases x₁; exact PSigma.mk.inj_iff

@[simp]
theorem «forall» {p : (Σ'a, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

@[simp]
theorem «exists» {p : (Σ'a, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

/-- A specialized ext lemma for equality of psigma types over an indexed subtype. -/
@[ext]
theorem subtype_ext {β : Sort _} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σ'a, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

theorem subtype_ext_iff {β : Sort _} {p : α → β → Prop} {x₀ x₁ : Σ'a, Subtype (p a)} :
    x₀ = x₁ ↔ x₀.fst = x₁.fst ∧ (x₀.snd : β) = x₁.snd :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => subtype_ext h₁ h₂⟩

variable {α₁ : Sort _} {α₂ : Sort _} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _}

/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) : PSigma β₁ → PSigma β₂
  | ⟨a, b⟩ => ⟨f₁ a, f₂ a b⟩

end PSigma
