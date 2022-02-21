/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Init.Function
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ext

/-!
# Extra facts about `Prod`

This file defines `Prod.swap : α × β → β × α` and proves various simple lemmas about `Prod`.
-/

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

@[simp] lemma prod_map (f : α → γ) (g : β → δ) (p : α × β) : Prod.map f g p = (f p.1, g p.2) := by
  cases p; rfl

namespace Prod

@[simp] theorem «forall» {p : α × β → Prop} : (∀ x, p x) ↔ (∀ a b, p (a, b)) :=
⟨λ h a b => h (a, b), λ h ⟨a, b⟩ => h a b⟩

@[simp] theorem «exists» {p : α × β → Prop} : (∃ x, p x) ↔ (∃ a b, p (a, b)) :=
⟨λ ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, λ ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

theorem forall' {p : α → β → Prop} : (∀ x : α × β, p x.1 x.2) ↔ ∀ a b, p a b :=
Prod.forall

theorem exists' {p : α → β → Prop} : (∃ x : α × β, p x.1 x.2) ↔ ∃ a b, p a b :=
Prod.exists

lemma map_mk (f : α → γ) (g : β → δ) (a : α) (b : β) : map f g (a, b) = (f a, g b) := rfl

lemma map_fst (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).1 = f (p.1) := by simp

lemma map_snd (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).2 = g (p.2) := by simp

lemma map_fst' (f : α → γ) (g : β → δ) : (Prod.fst ∘ map f g) = f ∘ Prod.fst :=
funext $ map_fst f g

lemma map_snd' (f : α → γ) (g : β → δ) : (Prod.snd ∘ map f g) = g ∘ Prod.snd :=
funext $ map_snd f g

/--
Composing a `prod.map` with another `prod.map` is equal to
a single `prod.map` of composed functions.
-/
lemma map_comp_map {ε ζ : Type _}
  (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) :
  Prod.map g g' ∘ Prod.map f f' = Prod.map (g ∘ f) (g' ∘ f') :=
by ext x; simp

/--
Composing a `prod.map` with another `prod.map` is equal to
a single `prod.map` of composed functions, fully applied.
-/
lemma map_map {ε ζ : Type _}
  (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) (x : α × γ) :
  Prod.map g g' (Prod.map f f' x) = Prod.map (g ∘ f) (g' ∘ f') x := by simp

theorem mk.inj_iff {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ (a₁ = a₂ ∧ b₁ = b₂) :=
⟨Prod.mk.inj,
 by intro hab; rw [hab.left, hab.right]⟩

lemma mk.inj_left {α β : Type _} (a : α) :
  Function.injective (Prod.mk a : β → α × β) :=
fun _ _ h => (Prod.mk.inj h).right

lemma mk.inj_right {α β : Type _} (b : β) :
  Function.injective (λ a => Prod.mk a b : α → α × β) :=
fun _ _ h => (Prod.mk.inj h).left

-- Port note: this lemma comes from lean3/library/init/data/prod.lean.
@[simp] lemma mk.eta : ∀{p : α × β}, (p.1, p.2) = p
| (a,b) => rfl

lemma ext_iff {p q : α × β} : p = q ↔ p.1 = q.1 ∧ p.2 = q.2 :=
by rw [← @mk.eta _ _ p, ← @mk.eta _ _ q, mk.inj_iff]

-- Port note: in mathlib this is named `ext`, but Lean4 has already defined that to be something
-- with a slightly different signature.
@[ext]
lemma ext' {α β} {p q : α × β} (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q :=
ext_iff.2 ⟨h₁, h₂⟩

lemma map_def {f : α → γ} {g : β → δ} : Prod.map f g = λ p => (f p.1, g p.2) :=
by ext <;> simp

lemma id_prod : (λ (p : α × α) => (p.1, p.2)) = id :=
funext $ λ ⟨a, b⟩ => rfl

lemma fst_surjective [h : Nonempty β] : Function.surjective (@fst α β) :=
λ x => h.elim $ λ y => ⟨⟨x, y⟩, rfl⟩

lemma snd_surjective [h : Nonempty α] : Function.surjective (@snd α β) :=
λ y => h.elim $ λ x => ⟨⟨x, y⟩, rfl⟩

lemma fst_injective [Subsingleton β] : Function.injective (@fst α β) :=
λ {x y} h => ext' h (Subsingleton.elim x.snd y.snd)

lemma snd_injective [Subsingleton α] : Function.injective (@snd α β) :=
λ {x y} h => ext' (Subsingleton.elim _ _) h

/-- Swap the factors of a product. `swap (a, b) = (b, a)` -/
def swap : α × β → β × α := λp => (p.2, p.1)

@[simp] lemma swap_swap : ∀ x : α × β, swap (swap x) = x
| ⟨a, b⟩ => rfl

@[simp] lemma fst_swap {p : α × β} : (swap p).1 = p.2 := rfl

@[simp] lemma snd_swap {p : α × β} : (swap p).2 = p.1 := rfl

@[simp] lemma swap_prod_mk {a : α} {b : β} : swap (a, b) = (b, a) := rfl

@[simp] lemma swap_swap_eq : swap ∘ swap = @id (α × β) :=
funext swap_swap

lemma swap_LeftInverse : Function.LeftInverse (@swap α β) swap :=
swap_swap

lemma swap_RightInverse : Function.RightInverse (@swap α β) swap :=
swap_swap

lemma swap_injective : Function.injective (@swap α β) :=
swap_LeftInverse.injective

lemma swap_surjective : Function.surjective (@swap α β) :=
Function.RightInverse.surjective swap_LeftInverse

lemma swap_bijective : Function.bijective (@swap α β) :=
⟨swap_injective, swap_surjective⟩

@[simp] lemma swap_inj {p q : α × β} : swap p = swap q ↔ p = q :=
swap_injective.eq_iff

lemma eq_iff_fst_eq_snd_eq : ∀{p q : α × β}, p = q ↔ (p.1 = q.1 ∧ p.2 = q.2)
| ⟨p₁, p₂⟩, ⟨q₁, q₂⟩ => by simp

lemma fst_eq_iff : ∀ {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)
| ⟨a, b⟩, x => by simp

lemma snd_eq_iff : ∀ {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)
| ⟨a, b⟩, x => by simp

theorem lex_def (r : α → α → Prop) (s : β → β → Prop)
  {p q : α × β} : Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2 :=
⟨(λ h => match h with
    | Lex.left b1 b2 h1 => by simp [h1]
    | Lex.right a h1 => by simp [h1] ),
 λ h => match p, q, h with
 | (a, b), (c, d), Or.inl h => Lex.left _ _ h
 | (a, b), (c, d), Or.inr ⟨e, h⟩ =>
   by subst e; exact Lex.right _ h ⟩

instance Lex.decidable [DecidableEq α]
  (r : α → α → Prop) (s : β → β → Prop) [DecidableRel r] [DecidableRel s] :
  DecidableRel (Prod.Lex r s) :=
λ p q => decidable_of_decidable_of_iff (by infer_instance) (lex_def r s).symm

end Prod

open Function

lemma Function.injective.prod_map {f : α → γ} {g : β → δ} (hf : injective f) (hg : injective g) :
  injective (Prod.map f g) :=
by intros x y h
   have h1 := (Prod.ext_iff.1 h).1
   rw [Prod.map_fst, Prod.map_fst] at h1
   have h2 := (Prod.ext_iff.1 h).2
   rw [Prod.map_snd, Prod.map_snd] at h2
   exact Prod.ext' (hf h1) (hg h2)

lemma Function.surjective.prod_map {f : α → γ} {g : β → δ} (hf : surjective f) (hg : surjective g) :
  surjective (Prod.map f g) :=
λ p => let ⟨x, hx⟩ := hf p.1
       let ⟨y, hy⟩ := hg p.2
       ⟨(x, y), Prod.ext' hx hy⟩
