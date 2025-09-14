/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Logic.Function.Defs
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
`α : Type*`, `β : α → Type*`, `γ : Π a : α, β a → Type*`, ...,
`A : Π (a : α) (b : β a) (c : γ a b) ..., Type*` with `x : α` `y : β x`, `z : γ x y`, ...

## Notes

The definition of `Sigma` takes values in `Type*`. This effectively forbids `Prop`-valued sigma
types. To that effect, we have `PSigma`, which takes value in `Sort*` and carries a more
complicated universe signature as a consequence.
-/

open Function

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

theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂ := by simp

@[simp]
theorem eta : ∀ x : Σ a, β a, Sigma.mk x.1 x.2 = x
  | ⟨_, _⟩ => rfl

protected theorem eq {α : Type*} {β : α → Type*} : ∀ {p₁ p₂ : Σ a, β a} (h₁ : p₁.1 = p₂.1),
    (Eq.recOn h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨_, _⟩, _, rfl, rfl => rfl

/-- A version of `Iff.mp Sigma.ext_iff` for functions from a nonempty type to a sigma type. -/
theorem _root_.Function.eq_of_sigmaMk_comp {γ : Type*} [Nonempty γ]
    {a b : α} {f : γ → β a} {g : γ → β b} (h : Sigma.mk a ∘ f = Sigma.mk b ∘ g) :
    a = b ∧ f ≍ g := by
  rcases ‹Nonempty γ› with ⟨i⟩
  obtain rfl : a = b := congr_arg Sigma.fst (congr_fun h i)
  simpa [funext_iff] using h

/-- A specialized ext lemma for equality of sigma types over an indexed subtype. -/
@[ext]
theorem subtype_ext {β : Type*} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σ a, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

-- This is not a good simp lemma, as its discrimination tree key is just an arrow.
theorem «forall» {p : (Σ a, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b ↦ h ⟨a, b⟩, fun h ⟨a, b⟩ ↦ h a b⟩

@[simp]
theorem «exists» {p : (Σ a, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩

lemma exists' {p : ∀ a, β a → Prop} : (∃ a b, p a b) ↔ ∃ x : Σ a, β a, p x.1 x.2 :=
  (Sigma.exists (p := fun x ↦ p x.1 x.2)).symm

lemma forall' {p : ∀ a, β a → Prop} : (∀ a b, p a b) ↔ ∀ x : Σ a, β a, p x.1 x.2 :=
  (Sigma.forall (p := fun x ↦ p x.1 x.2)).symm

theorem _root_.sigma_mk_injective {i : α} : Injective (@Sigma.mk α β i)
  | _, _, rfl => rfl

theorem fst_surjective [h : ∀ a, Nonempty (β a)] : Surjective (fst : (Σ a, β a) → α) := fun a ↦
  let ⟨b⟩ := h a; ⟨⟨a, b⟩, rfl⟩

theorem fst_surjective_iff : Surjective (fst : (Σ a, β a) → α) ↔ ∀ a, Nonempty (β a) :=
  ⟨fun h a ↦ let ⟨x, hx⟩ := h a; hx ▸ ⟨x.2⟩, @fst_surjective _ _⟩

theorem fst_injective [h : ∀ a, Subsingleton (β a)] : Injective (fst : (Σ a, β a) → α) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (rfl : a₁ = a₂)
  exact congr_arg (mk a₁) <| Subsingleton.elim _ _

theorem fst_injective_iff : Injective (fst : (Σ a, β a) → α) ↔ ∀ a, Subsingleton (β a) :=
  ⟨fun h _ ↦ ⟨fun _ _ ↦ sigma_mk_injective <| h rfl⟩, @fst_injective _ _⟩

/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) (x : Sigma β₁) : Sigma β₂ :=
  ⟨f₁ x.1, f₂ x.1 x.2⟩

lemma map_mk (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) (x : α₁) (y : β₁ x) :
    map f₁ f₂ ⟨x, y⟩ = ⟨f₁ x, f₂ x y⟩ := rfl
end Sigma

theorem Function.Injective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Injective f₁) (h₂ : ∀ a, Injective (f₂ a)) : Injective (Sigma.map f₁ f₂)
  | ⟨i, x⟩, ⟨j, y⟩, h => by
    obtain rfl : i = j := h₁ (Sigma.mk.inj_iff.mp h).1
    obtain rfl : x = y := h₂ i (sigma_mk_injective h)
    rfl

theorem Function.Injective.of_sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h : Injective (Sigma.map f₁ f₂)) (a : α₁) : Injective (f₂ a) := fun x y hxy ↦
  sigma_mk_injective <| @h ⟨a, x⟩ ⟨a, y⟩ (Sigma.ext rfl (heq_of_eq hxy))

theorem Function.Injective.sigma_map_iff {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Injective f₁) : Injective (Sigma.map f₁ f₂) ↔ ∀ a, Injective (f₂ a) :=
  ⟨fun h ↦ h.of_sigma_map, h₁.sigma_map⟩

theorem Function.Surjective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Surjective f₁) (h₂ : ∀ a, Surjective (f₂ a)) : Surjective (Sigma.map f₁ f₂) := by
  simp only [Surjective, Sigma.forall, h₁.forall]
  exact fun i ↦ (h₂ _).forall.2 fun x ↦ ⟨⟨i, x⟩, rfl⟩

/-- Interpret a function on `Σ x : α, β x` as a dependent function with two arguments.

This also exists as an `Equiv` as `Equiv.piCurry γ`. -/
def Sigma.curry {γ : ∀ a, β a → Type*} (f : ∀ x : Sigma β, γ x.1 x.2) (x : α) (y : β x) : γ x y :=
  f ⟨x, y⟩

/-- Interpret a dependent function with two arguments as a function on `Σ x : α, β x`.

This also exists as an `Equiv` as `(Equiv.piCurry γ).symm`. -/
def Sigma.uncurry {γ : ∀ a, β a → Type*} (f : ∀ (x) (y : β x), γ x y) (x : Sigma β) : γ x.1 x.2 :=
  f x.1 x.2

@[simp]
theorem Sigma.uncurry_curry {γ : ∀ a, β a → Type*} (f : ∀ x : Sigma β, γ x.1 x.2) :
    Sigma.uncurry (Sigma.curry f) = f :=
  funext fun ⟨_, _⟩ ↦ rfl

@[simp]
theorem Sigma.curry_uncurry {γ : ∀ a, β a → Type*} (f : ∀ (x) (y : β x), γ x y) :
    Sigma.curry (Sigma.uncurry f) = f :=
  rfl

theorem Sigma.curry_update {γ : ∀ a, β a → Type*} [DecidableEq α] [∀ a, DecidableEq (β a)]
    (i : Σ a, β a) (f : (i : Σ a, β a) → γ i.1 i.2) (x : γ i.1 i.2) :
    Sigma.curry (Function.update f i x) =
      Function.update (Sigma.curry f) i.1 (Function.update (Sigma.curry f i.1) i.2 x) := by
  obtain ⟨ia, ib⟩ := i
  ext ja jb
  unfold Sigma.curry
  obtain rfl | ha := eq_or_ne ia ja
  · obtain rfl | hb := eq_or_ne ib jb
    · simp
    · simp only [update_self]
      rw [Function.update_of_ne (mt _ hb.symm), Function.update_of_ne hb.symm]
      rintro h
      injection h
  · rw [Function.update_of_ne (ne_of_apply_ne Sigma.fst _), Function.update_of_ne]
    · exact ha.symm
    · exact ha.symm

/-- Convert a product type to a Σ-type. -/
def Prod.toSigma {α β} (p : α × β) : Σ _ : α, β :=
  ⟨p.1, p.2⟩

@[simp]
theorem Prod.fst_comp_toSigma {α β} : Sigma.fst ∘ @Prod.toSigma α β = Prod.fst :=
  rfl

@[simp]
theorem Prod.fst_toSigma {α β} (x : α × β) : (Prod.toSigma x).fst = x.fst :=
  rfl

@[simp]
theorem Prod.snd_toSigma {α β} (x : α × β) : (Prod.toSigma x).snd = x.snd :=
  rfl

@[simp]
theorem Prod.toSigma_mk {α β} (x : α) (y : β) : (x, y).toSigma = ⟨x, y⟩ :=
  rfl

theorem Prod.toSigma_injective {α β} : Function.Injective (α := α × β) Prod.toSigma := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp_all

@[simp]
theorem Prod.toSigma_inj {α β} {x y : α × β} : x.toSigma = y.toSigma ↔ x = y :=
  Prod.toSigma_injective.eq_iff

end Sigma

namespace PSigma

variable {α : Sort*} {β : α → Sort*}

/-- Nondependent eliminator for `PSigma`. -/
def elim {γ} (f : ∀ a, β a → γ) (a : PSigma β) : γ :=
  PSigma.casesOn a f

@[simp]
theorem elim_val {γ} (f : ∀ a, β a → γ) (a b) : PSigma.elim f ⟨a, b⟩ = f a b :=
  rfl

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

theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    @PSigma.mk α β a₁ b₁ = @PSigma.mk α β a₂ b₂ ↔ a₁ = a₂ ∧ b₁ ≍ b₂ :=
  (Iff.intro PSigma.mk.inj) fun ⟨h₁, h₂⟩ ↦
    match a₁, a₂, b₁, b₂, h₁, h₂ with
    | _, _, _, _, Eq.refl _, HEq.refl _ => rfl

-- This should not be a simp lemma, since its discrimination tree key would just be `→`.
theorem «forall» {p : (Σ' a, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b ↦ h ⟨a, b⟩, fun h ⟨a, b⟩ ↦ h a b⟩

@[simp] lemma «exists» {p : (Σ' a, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩

/-- A specialized ext lemma for equality of `PSigma` types over an indexed subtype. -/
@[ext]
theorem subtype_ext {β : Sort*} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σ' a, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

variable {α₁ : Sort*} {α₂ : Sort*} {β₁ : α₁ → Sort*} {β₂ : α₂ → Sort*}

/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) : PSigma β₁ → PSigma β₂
  | ⟨a, b⟩ => ⟨f₁ a, f₂ a b⟩

end PSigma
