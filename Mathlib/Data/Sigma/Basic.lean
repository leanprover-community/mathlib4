/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Init.Function
import Std.Tactic.Ext
import Mathlib.Logic.Function.Basic

#align_import data.sigma.basic from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

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
`α : Type*`, `β : α → Type*`, `γ : Π a : α, β a → Type*`, ...,
`A : Π (a : α) (b : β a) (c : γ a b) ..., Type*` with `x : α` `y : β x`, `z : γ x y`, ...

## Notes

The definition of `Sigma` takes values in `Type*`. This effectively forbids `Prop`- valued sigma
types. To that effect, we have `PSigma`, which takes value in `Sort*` and carries a more
complicated universe signature as a consequence.
-/

section Sigma

variable {α α₁ α₂ : Type*} {β : α → Type*} {β₁ : α₁ → Type*} {β₂ : α₂ → Type*}

namespace Sigma

instance instInhabitedSigma [Inhabited α] [Inhabited (β default)] : Inhabited (Sigma β) :=
  ⟨⟨default, default⟩⟩

instance instDecidableEqSigma [h₁ : DecidableEq α] [h₂ : ∀ a, DecidableEq (β a)] :
    DecidableEq (Sigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, isTrue (Eq.refl _) =>
      match b₁, b₂, h₂ _ b₁ b₂ with
      | _, _, isTrue (Eq.refl _) => isTrue rfl
      | _, _, isFalse n => isFalse fun h ↦ Sigma.noConfusion h fun _ e₂ ↦ n <| eq_of_heq e₂
    | _, _, _, _, isFalse n => isFalse fun h ↦ Sigma.noConfusion h fun e₁ _ ↦ n e₁

-- sometimes the built-in injectivity support does not work
@[simp] -- @[nolint simpNF]
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ HEq b₁ b₂ :=
  ⟨λ h => by cases h; exact ⟨rfl, heq_of_eq rfl⟩, -- in Lean 3 `simp` solved this
             -- ⊢ a₁ = a₁ ∧ HEq b₁ b₁
                      -- 🎉 no goals
   λ ⟨h₁, h₂⟩ => by subst h₁; rw [eq_of_heq h₂]⟩
                    -- ⊢ { fst := a₁, snd := b₁ } = { fst := a₁, snd := b₂ }
                              -- 🎉 no goals
#align sigma.mk.inj_iff Sigma.mk.inj_iff

@[simp]
theorem eta : ∀ x : Σa, β a, Sigma.mk x.1 x.2 = x
  | ⟨_, _⟩ => rfl
#align sigma.eta Sigma.eta

@[ext]
theorem ext {x₀ x₁ : Sigma β} (h₀ : x₀.1 = x₁.1) (h₁ : HEq x₀.2 x₁.2) : x₀ = x₁ := by
  cases x₀; cases x₁; cases h₀; cases h₁; rfl
  -- ⊢ { fst := fst✝, snd := snd✝ } = x₁
            -- ⊢ { fst := fst✝¹, snd := snd✝¹ } = { fst := fst✝, snd := snd✝ }
                      -- ⊢ { fst := fst✝, snd := snd✝¹ } = { fst := fst✝, snd := snd✝ }
                                -- ⊢ { fst := fst✝, snd := snd✝ } = { fst := fst✝, snd := snd✝ }
                                          -- 🎉 no goals
#align sigma.ext Sigma.ext

theorem ext_iff {x₀ x₁ : Sigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ HEq x₀.2 x₁.2 := by
  cases x₀; cases x₁; exact Sigma.mk.inj_iff
  -- ⊢ { fst := fst✝, snd := snd✝ } = x₁ ↔ { fst := fst✝, snd := snd✝ }.fst = x₁.fs …
            -- ⊢ { fst := fst✝¹, snd := snd✝¹ } = { fst := fst✝, snd := snd✝ } ↔ { fst := fst …
                      -- 🎉 no goals
#align sigma.ext_iff Sigma.ext_iff

/-- A version of `Iff.mp Sigma.ext_iff` for functions from a nonempty type to a sigma type. -/
theorem _root_.Function.eq_of_sigmaMk_comp {γ : Type*} [Nonempty γ]
    {a b : α} {f : γ → β a} {g : γ → β b} (h : Sigma.mk a ∘ f = Sigma.mk b ∘ g) :
    a = b ∧ HEq f g := by
  rcases ‹Nonempty γ› with ⟨i⟩
  -- ⊢ a = b ∧ HEq f g
  obtain rfl : a = b := congr_arg Sigma.fst (congr_fun h i)
  -- ⊢ a = a ∧ HEq f g
  simpa [Function.funext_iff] using h
  -- 🎉 no goals

/-- A specialized ext lemma for equality of sigma types over an indexed subtype. -/
@[ext]
theorem subtype_ext {β : Type*} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σa, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl
#align sigma.subtype_ext Sigma.subtype_ext

theorem subtype_ext_iff {β : Type*} {p : α → β → Prop} {x₀ x₁ : Σa, Subtype (p a)} :
    x₀ = x₁ ↔ x₀.fst = x₁.fst ∧ (x₀.snd : β) = x₁.snd :=
  ⟨fun h ↦ h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ ↦ subtype_ext h₁ h₂⟩
#align sigma.subtype_ext_iff Sigma.subtype_ext_iff

@[simp]
theorem «forall» {p : (Σa, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b ↦ h ⟨a, b⟩, fun h ⟨a, b⟩ ↦ h a b⟩
#align sigma.forall Sigma.forall

@[simp]
theorem «exists» {p : (Σa, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩
#align sigma.exists Sigma.exists

/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) (x : Sigma β₁) : Sigma β₂ :=
  ⟨f₁ x.1, f₂ x.1 x.2⟩
#align sigma.map Sigma.map

lemma map_mk (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) (x : α₁) (y : β₁ x) :
    map f₁ f₂ ⟨x, y⟩ = ⟨f₁ x, f₂ x y⟩ := rfl
end Sigma

theorem sigma_mk_injective {i : α} : Function.Injective (@Sigma.mk α β i)
  | _, _, rfl => rfl
#align sigma_mk_injective sigma_mk_injective

theorem Function.Injective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
  (h₁ : Function.Injective f₁) (h₂ : ∀ a, Function.Injective (f₂ a)) :
    Function.Injective (Sigma.map f₁ f₂)
  | ⟨i, x⟩, ⟨j, y⟩, h => by
    obtain rfl : i = j := h₁ (Sigma.mk.inj_iff.mp h).1
    -- ⊢ { fst := i, snd := x } = { fst := i, snd := y }
    obtain rfl : x = y := h₂ i (sigma_mk_injective h)
    -- ⊢ { fst := i, snd := x } = { fst := i, snd := x }
    rfl
    -- 🎉 no goals
#align function.injective.sigma_map Function.Injective.sigma_map

theorem Function.Injective.of_sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h : Function.Injective (Sigma.map f₁ f₂)) (a : α₁) : Function.Injective (f₂ a) :=
  fun x y hxy ↦
  sigma_mk_injective <| @h ⟨a, x⟩ ⟨a, y⟩ (Sigma.ext rfl (heq_of_eq hxy))
#align function.injective.of_sigma_map Function.Injective.of_sigma_map

theorem Function.Injective.sigma_map_iff {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
  (h₁ : Function.Injective f₁) :
    Function.Injective (Sigma.map f₁ f₂) ↔ ∀ a, Function.Injective (f₂ a) :=
  ⟨fun h ↦ h.of_sigma_map, h₁.sigma_map⟩
#align function.injective.sigma_map_iff Function.Injective.sigma_map_iff

theorem Function.Surjective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
  (h₁ : Function.Surjective f₁) (h₂ : ∀ a, Function.Surjective (f₂ a)) :
    Function.Surjective (Sigma.map f₁ f₂) := by
  simp only [Function.Surjective, Sigma.forall, h₁.forall]
  -- ⊢ ∀ (x : α₁) (b : β₂ (f₁ x)), ∃ a, Sigma.map f₁ f₂ a = { fst := f₁ x, snd := b }
  exact fun i ↦ (h₂ _).forall.2 fun x ↦ ⟨⟨i, x⟩, rfl⟩
  -- 🎉 no goals
#align function.surjective.sigma_map Function.Surjective.sigma_map

/-- Interpret a function on `Σ x : α, β x` as a dependent function with two arguments.

This also exists as an `Equiv` as `Equiv.piCurry γ`. -/
def Sigma.curry {γ : ∀ a, β a → Type*} (f : ∀ x : Sigma β, γ x.1 x.2) (x : α) (y : β x) : γ x y :=
  f ⟨x, y⟩
#align sigma.curry Sigma.curry

/-- Interpret a dependent function with two arguments as a function on `Σ x : α, β x`.

This also exists as an `Equiv` as `(Equiv.piCurry γ).symm`. -/
def Sigma.uncurry {γ : ∀ a, β a → Type*} (f : ∀ (x) (y : β x), γ x y) (x : Sigma β) : γ x.1 x.2 :=
  f x.1 x.2
#align sigma.uncurry Sigma.uncurry

@[simp]
theorem Sigma.uncurry_curry {γ : ∀ a, β a → Type*} (f : ∀ x : Sigma β, γ x.1 x.2) :
    Sigma.uncurry (Sigma.curry f) = f :=
  funext fun ⟨_, _⟩ ↦ rfl
#align sigma.uncurry_curry Sigma.uncurry_curry

@[simp]
theorem Sigma.curry_uncurry {γ : ∀ a, β a → Type*} (f : ∀ (x) (y : β x), γ x y) :
    Sigma.curry (Sigma.uncurry f) = f :=
  rfl
#align sigma.curry_uncurry Sigma.curry_uncurry

/-- Convert a product type to a Σ-type. -/
def Prod.toSigma {α β} (p : α × β) : Σ_ : α, β :=
  ⟨p.1, p.2⟩
#align prod.to_sigma Prod.toSigma

@[simp]
theorem Prod.fst_comp_toSigma {α β} : Sigma.fst ∘ @Prod.toSigma α β = Prod.fst :=
  rfl
#align prod.fst_comp_to_sigma Prod.fst_comp_toSigma

@[simp]
theorem Prod.fst_toSigma {α β} (x : α × β) : (Prod.toSigma x).fst = x.fst :=
  rfl
#align prod.fst_to_sigma Prod.fst_toSigma

@[simp]
theorem Prod.snd_toSigma {α β} (x : α × β) : (Prod.toSigma x).snd = x.snd :=
  rfl
#align prod.snd_to_sigma Prod.snd_toSigma

@[simp]
theorem Prod.toSigma_mk {α β} (x : α) (y : β) : (x, y).toSigma = ⟨x, y⟩ :=
  rfl
#align prod.to_sigma_mk Prod.toSigma_mk

-- Porting note: the meta instance `has_reflect (Σa, β a)` was removed here.

end Sigma

namespace PSigma

variable {α : Sort*} {β : α → Sort*}

/-- Nondependent eliminator for `PSigma`. -/
def elim {γ} (f : ∀ a, β a → γ) (a : PSigma β) : γ :=
  PSigma.casesOn a f
#align psigma.elim PSigma.elim

@[simp]
theorem elim_val {γ} (f : ∀ a, β a → γ) (a b) : PSigma.elim f ⟨a, b⟩ = f a b :=
  rfl
#align psigma.elim_val PSigma.elim_val

instance [Inhabited α] [Inhabited (β default)] : Inhabited (PSigma β) :=
  ⟨⟨default, default⟩⟩

instance decidableEq [h₁ : DecidableEq α] [h₂ : ∀ a, DecidableEq (β a)] : DecidableEq (PSigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, isTrue (Eq.refl _) =>
      match b₁, b₂, h₂ _ b₁ b₂ with
      | _, _, isTrue (Eq.refl _) => isTrue rfl
      | _, _, isFalse n => isFalse fun h ↦ PSigma.noConfusion h fun _ e₂ ↦ n <| eq_of_heq e₂
    | _, _, _, _, isFalse n => isFalse fun h ↦ PSigma.noConfusion h fun e₁ _ ↦ n e₁

-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/porting.20data.2Esigma.2Ebasic/near/304855864
-- for an explanation of why this is currently needed. It generates `PSigma.mk.inj`.
-- This could be done elsewhere.
gen_injective_theorems% PSigma

theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    @PSigma.mk α β a₁ b₁ = @PSigma.mk α β a₂ b₂ ↔ a₁ = a₂ ∧ HEq b₁ b₂ :=
  (Iff.intro PSigma.mk.inj) fun ⟨h₁, h₂⟩ ↦
    match a₁, a₂, b₁, b₂, h₁, h₂ with
    | _, _, _, _, Eq.refl _, HEq.refl _ => rfl
#align psigma.mk.inj_iff PSigma.mk.inj_iff

@[ext]
theorem ext {x₀ x₁ : PSigma β} (h₀ : x₀.1 = x₁.1) (h₁ : HEq x₀.2 x₁.2) : x₀ = x₁ := by
  cases x₀; cases x₁; cases h₀; cases h₁; rfl
  -- ⊢ { fst := fst✝, snd := snd✝ } = x₁
            -- ⊢ { fst := fst✝¹, snd := snd✝¹ } = { fst := fst✝, snd := snd✝ }
                      -- ⊢ { fst := fst✝, snd := snd✝¹ } = { fst := fst✝, snd := snd✝ }
                                -- ⊢ { fst := fst✝, snd := snd✝ } = { fst := fst✝, snd := snd✝ }
                                          -- 🎉 no goals
#align psigma.ext PSigma.ext

theorem ext_iff {x₀ x₁ : PSigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ HEq x₀.2 x₁.2 := by
  cases x₀; cases x₁; exact PSigma.mk.inj_iff
  -- ⊢ { fst := fst✝, snd := snd✝ } = x₁ ↔ { fst := fst✝, snd := snd✝ }.fst = x₁.fs …
            -- ⊢ { fst := fst✝¹, snd := snd✝¹ } = { fst := fst✝, snd := snd✝ } ↔ { fst := fst …
                      -- 🎉 no goals
#align psigma.ext_iff PSigma.ext_iff

@[simp]
theorem «forall» {p : (Σ'a, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b ↦ h ⟨a, b⟩, fun h ⟨a, b⟩ ↦ h a b⟩
#align psigma.forall PSigma.forall

@[simp]
theorem «exists» {p : (Σ'a, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩
#align psigma.exists PSigma.exists

/-- A specialized ext lemma for equality of `PSigma` types over an indexed subtype. -/
@[ext]
theorem subtype_ext {β : Sort*} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σ'a, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl
#align psigma.subtype_ext PSigma.subtype_ext

theorem subtype_ext_iff {β : Sort*} {p : α → β → Prop} {x₀ x₁ : Σ'a, Subtype (p a)} :
    x₀ = x₁ ↔ x₀.fst = x₁.fst ∧ (x₀.snd : β) = x₁.snd :=
  ⟨fun h ↦ h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ ↦ subtype_ext h₁ h₂⟩
#align psigma.subtype_ext_iff PSigma.subtype_ext_iff

variable {α₁ : Sort*} {α₂ : Sort*} {β₁ : α₁ → Sort*} {β₂ : α₂ → Sort*}

/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) : PSigma β₁ → PSigma β₂
  | ⟨a, b⟩ => ⟨f₁ a, f₂ a b⟩
#align psigma.map PSigma.map

end PSigma
