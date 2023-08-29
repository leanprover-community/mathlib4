/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Init.Core
import Mathlib.Init.Data.Prod
import Mathlib.Init.Function
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Common

#align_import data.prod.basic from "leanprover-community/mathlib"@"d07245fd37786daa997af4f1a73a49fa3b748408"

/-!
# Extra facts about `Prod`

This file defines `Prod.swap : α × β → β × α` and proves various simple lemmas about `Prod`.
-/

set_option autoImplicit true

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

@[simp]
theorem Prod_map (f : α → γ) (g : β → δ) (p : α × β) : Prod.map f g p = (f p.1, g p.2) :=
  rfl
#align prod_map Prod_map

namespace Prod

@[simp]
theorem «forall» {p : α × β → Prop} : (∀ x, p x) ↔ ∀ a b, p (a, b) :=
  ⟨fun h a b ↦ h (a, b), fun h ⟨a, b⟩ ↦ h a b⟩
#align prod.forall Prod.forall

@[simp]
theorem «exists» {p : α × β → Prop} : (∃ x, p x) ↔ ∃ a b, p (a, b) :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩
#align prod.exists Prod.exists

theorem forall' {p : α → β → Prop} : (∀ x : α × β, p x.1 x.2) ↔ ∀ a b, p a b :=
  Prod.forall
#align prod.forall' Prod.forall'

theorem exists' {p : α → β → Prop} : (∃ x : α × β, p x.1 x.2) ↔ ∃ a b, p a b :=
  Prod.exists
#align prod.exists' Prod.exists'

@[simp]
theorem snd_comp_mk (x : α) : Prod.snd ∘ (Prod.mk x : β → α × β) = id :=
  rfl
#align prod.snd_comp_mk Prod.snd_comp_mk

@[simp]
theorem fst_comp_mk (x : α) : Prod.fst ∘ (Prod.mk x : β → α × β) = Function.const β x :=
  rfl
#align prod.fst_comp_mk Prod.fst_comp_mk

@[simp, mfld_simps]
theorem map_mk (f : α → γ) (g : β → δ) (a : α) (b : β) : map f g (a, b) = (f a, g b) :=
  rfl
#align prod.map_mk Prod.map_mk

theorem map_fst (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).1 = f p.1 :=
  rfl
#align prod.map_fst Prod.map_fst

theorem map_snd (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).2 = g p.2 :=
  rfl
#align prod.map_snd Prod.map_snd

theorem map_fst' (f : α → γ) (g : β → δ) : Prod.fst ∘ map f g = f ∘ Prod.fst :=
  funext <| map_fst f g
#align prod.map_fst' Prod.map_fst'

theorem map_snd' (f : α → γ) (g : β → δ) : Prod.snd ∘ map f g = g ∘ Prod.snd :=
  funext <| map_snd f g
#align prod.map_snd' Prod.map_snd'

/-- Composing a `Prod.map` with another `Prod.map` is equal to
a single `Prod.map` of composed functions.
-/
theorem map_comp_map {ε ζ : Type*} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) :
    Prod.map g g' ∘ Prod.map f f' = Prod.map (g ∘ f) (g' ∘ f') :=
  rfl
#align prod.map_comp_map Prod.map_comp_map

/-- Composing a `Prod.map` with another `Prod.map` is equal to
a single `Prod.map` of composed functions, fully applied.
-/
theorem map_map {ε ζ : Type*} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) (x : α × γ) :
    Prod.map g g' (Prod.map f f' x) = Prod.map (g ∘ f) (g' ∘ f') x :=
  rfl
#align prod.map_map Prod.map_map

-- Porting note: mathlib3 proof uses `by cc` for the mpr direction
-- Porting note: `@[simp]` tag removed because auto-generated `mk.injEq` simplifies LHS
-- @[simp]
theorem mk.inj_iff {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  Iff.of_eq (mk.injEq _ _ _ _)
#align prod.mk.inj_iff Prod.mk.inj_iff

theorem mk.inj_left {α β : Type*} (a : α) : Function.Injective (Prod.mk a : β → α × β) := by
  intro b₁ b₂ h
  -- ⊢ b₁ = b₂
  simpa only [true_and, Prod.mk.inj_iff, eq_self_iff_true] using h
  -- 🎉 no goals
#align prod.mk.inj_left Prod.mk.inj_left

theorem mk.inj_right {α β : Type*} (b : β) :
    Function.Injective (fun a ↦ Prod.mk a b : α → α × β) := by
  intro b₁ b₂ h
  -- ⊢ b₁ = b₂
  simpa only [and_true, eq_self_iff_true, mk.inj_iff] using h
  -- 🎉 no goals
#align prod.mk.inj_right Prod.mk.inj_right

lemma mk_inj_left : (a, b₁) = (a, b₂) ↔ b₁ = b₂ := (mk.inj_left _).eq_iff
#align prod.mk_inj_left Prod.mk_inj_left

lemma mk_inj_right : (a₁, b) = (a₂, b) ↔ a₁ = a₂ := (mk.inj_right _).eq_iff
#align prod.mk_inj_right Prod.mk_inj_right

theorem ext_iff {p q : α × β} : p = q ↔ p.1 = q.1 ∧ p.2 = q.2 := by
  rw [← @mk.eta _ _ p, ← @mk.eta _ _ q, mk.inj_iff]
  -- 🎉 no goals
#align prod.ext_iff Prod.ext_iff

@[ext]
theorem ext {α β} {p q : α × β} (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q :=
  ext_iff.2 ⟨h₁, h₂⟩
#align prod.ext Prod.ext

theorem map_def {f : α → γ} {g : β → δ} : Prod.map f g = fun p : α × β ↦ (f p.1, g p.2) :=
  funext fun p ↦ ext (map_fst f g p) (map_snd f g p)
#align prod.map_def Prod.map_def

theorem id_prod : (fun p : α × β ↦ (p.1, p.2)) = id :=
  rfl
#align prod.id_prod Prod.id_prod

@[simp]
theorem map_id : Prod.map (@id α) (@id β) = id :=
  id_prod
#align prod.map_id Prod.map_id

theorem fst_surjective [h : Nonempty β] : Function.Surjective (@fst α β) :=
  fun x ↦ h.elim fun y ↦ ⟨⟨x, y⟩, rfl⟩
#align prod.fst_surjective Prod.fst_surjective

theorem snd_surjective [h : Nonempty α] : Function.Surjective (@snd α β) :=
  fun y ↦ h.elim fun x ↦ ⟨⟨x, y⟩, rfl⟩
#align prod.snd_surjective Prod.snd_surjective

theorem fst_injective [Subsingleton β] : Function.Injective (@fst α β) :=
  fun _ _ h ↦ ext h (Subsingleton.elim _ _)
#align prod.fst_injective Prod.fst_injective

theorem snd_injective [Subsingleton α] : Function.Injective (@snd α β) :=
  fun _ _ h ↦ ext (Subsingleton.elim _ _) h
#align prod.snd_injective Prod.snd_injective

/-- Swap the factors of a product. `swap (a, b) = (b, a)` -/
def swap : α × β → β × α := fun p ↦ (p.2, p.1)
#align prod.swap Prod.swap

@[simp]
theorem swap_swap : ∀ x : α × β, swap (swap x) = x
  | ⟨_, _⟩ => rfl
#align prod.swap_swap Prod.swap_swap

@[simp]
theorem fst_swap {p : α × β} : (swap p).1 = p.2 :=
  rfl
#align prod.fst_swap Prod.fst_swap

@[simp]
theorem snd_swap {p : α × β} : (swap p).2 = p.1 :=
  rfl
#align prod.snd_swap Prod.snd_swap

@[simp]
theorem swap_prod_mk {a : α} {b : β} : swap (a, b) = (b, a) :=
  rfl
#align prod.swap_prod_mk Prod.swap_prod_mk

@[simp]
theorem swap_swap_eq : swap ∘ swap = @id (α × β) :=
  funext swap_swap
#align prod.swap_swap_eq Prod.swap_swap_eq

@[simp]
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap
#align prod.swap_left_inverse Prod.swap_leftInverse

@[simp]
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap
#align prod.swap_right_inverse Prod.swap_rightInverse

theorem swap_injective : Function.Injective (@swap α β) :=
  swap_leftInverse.injective
#align prod.swap_injective Prod.swap_injective

theorem swap_surjective : Function.Surjective (@swap α β) :=
  swap_leftInverse.surjective
#align prod.swap_surjective Prod.swap_surjective

theorem swap_bijective : Function.Bijective (@swap α β) :=
  ⟨swap_injective, swap_surjective⟩
#align prod.swap_bijective Prod.swap_bijective

@[simp]
theorem swap_inj {p q : α × β} : swap p = swap q ↔ p = q :=
  swap_injective.eq_iff
#align prod.swap_inj Prod.swap_inj

theorem eq_iff_fst_eq_snd_eq : ∀ {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
  | ⟨p₁, p₂⟩, ⟨q₁, q₂⟩ => by simp
                             -- 🎉 no goals
#align prod.eq_iff_fst_eq_snd_eq Prod.eq_iff_fst_eq_snd_eq

theorem fst_eq_iff : ∀ {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)
  | ⟨a, b⟩, x => by simp
                    -- 🎉 no goals
#align prod.fst_eq_iff Prod.fst_eq_iff

theorem snd_eq_iff : ∀ {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)
  | ⟨a, b⟩, x => by simp
                    -- 🎉 no goals
#align prod.snd_eq_iff Prod.snd_eq_iff

variable {r : α → α → Prop} {s : β → β → Prop} {x y : α × β}

theorem lex_def (r : α → α → Prop) (s : β → β → Prop) {p q : α × β} :
    Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2 :=
  ⟨fun h ↦ by cases h <;> simp [*], fun h ↦
              -- ⊢ r (a₁✝, b₁✝).fst (a₂✝, b₂✝).fst ∨ (a₁✝, b₁✝).fst = (a₂✝, b₂✝).fst ∧ s (a₁✝,  …
                          -- 🎉 no goals
                          -- 🎉 no goals
    match p, q, h with
    | (a, b), (c, d), Or.inl h => Lex.left _ _ h
    | (a, b), (c, d), Or.inr ⟨e, h⟩ => by subst e; exact Lex.right _ h⟩
                                          -- ⊢ Prod.Lex r s (a, b) ((a, b).fst, d)
                                                   -- 🎉 no goals
#align prod.lex_def Prod.lex_def

lemma lex_iff : Prod.Lex r s x y ↔ r x.1 y.1 ∨ x.1 = y.1 ∧ s x.2 y.2 := lex_def _ _
#align prod.lex_iff Prod.lex_iff

instance Lex.decidable [DecidableEq α]
    (r : α → α → Prop) (s : β → β → Prop) [DecidableRel r] [DecidableRel s] :
    DecidableRel (Prod.Lex r s) :=
  fun _ _ ↦ decidable_of_decidable_of_iff (lex_def r s).symm

@[refl]
theorem Lex.refl_left (r : α → α → Prop) (s : β → β → Prop) [IsRefl α r] : ∀ x, Prod.Lex r s x x
  | (_, _) => Lex.left _ _ (refl _)
#align prod.lex.refl_left Prod.Lex.refl_left

instance {r : α → α → Prop} {s : β → β → Prop} [IsRefl α r] : IsRefl (α × β) (Prod.Lex r s) :=
  ⟨Lex.refl_left _ _⟩

@[refl]
theorem Lex.refl_right (r : α → α → Prop) (s : β → β → Prop) [IsRefl β s] : ∀ x, Prod.Lex r s x x
  | (_, _) => Lex.right _ (refl _)
#align prod.lex.refl_right Prod.Lex.refl_right

instance {r : α → α → Prop} {s : β → β → Prop} [IsRefl β s] : IsRefl (α × β) (Prod.Lex r s) :=
  ⟨Lex.refl_right _ _⟩

instance isIrrefl [IsIrrefl α r] [IsIrrefl β s] : IsIrrefl (α × β) (Prod.Lex r s) :=
  ⟨by rintro ⟨i, a⟩ (⟨_, _, h⟩ | ⟨_, h⟩) <;> exact irrefl _ h⟩
      -- ⊢ False
                                             -- 🎉 no goals
                                             -- 🎉 no goals

@[trans]
theorem Lex.trans {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] :
    ∀ {x y z : α × β}, Prod.Lex r s x y → Prod.Lex r s y z → Prod.Lex r s x z
  | (_, _), (_, _), (_, _), left  _ _ hxy₁, left  _ _ hyz₁ => left  _ _ (_root_.trans hxy₁ hyz₁)
  | (_, _), (_, _), (_, _), left  _ _ hxy₁, right _ _      => left  _ _ hxy₁
  | (_, _), (_, _), (_, _), right _ _,      left  _ _ hyz₁ => left  _ _ hyz₁
  | (_, _), (_, _), (_, _), right _ hxy₂,   right _ hyz₂   => right _ (_root_.trans hxy₂ hyz₂)
#align prod.lex.trans Prod.Lex.trans

instance {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] :
  IsTrans (α × β) (Prod.Lex r s) :=
  ⟨fun _ _ _ ↦ Lex.trans⟩

instance {r : α → α → Prop} {s : β → β → Prop} [IsStrictOrder α r] [IsAntisymm β s] :
    IsAntisymm (α × β) (Prod.Lex r s) :=
  ⟨fun x₁ x₂ h₁₂ h₂₁ ↦
    match x₁, x₂, h₁₂, h₂₁ with
    | (a, _), (_, _), .left  _ _ hr₁, .left  _ _ hr₂ => (irrefl a (_root_.trans hr₁ hr₂)).elim
    | (_, _), (_, _), .left  _ _ hr₁, .right _ _     => (irrefl _ hr₁).elim
    | (_, _), (_, _), .right _ _,     .left  _ _ hr₂ => (irrefl _ hr₂).elim
    | (_, _), (_, _), .right _ hs₁,   .right _ hs₂   => antisymm hs₁ hs₂ ▸ rfl⟩

instance isTotal_left {r : α → α → Prop} {s : β → β → Prop} [IsTotal α r] :
    IsTotal (α × β) (Prod.Lex r s) :=
  ⟨fun ⟨a₁, _⟩ ⟨a₂, _⟩ ↦ (IsTotal.total a₁ a₂).imp (Lex.left _ _) (Lex.left _ _)⟩
#align prod.is_total_left Prod.isTotal_left

instance isTotal_right {r : α → α → Prop} {s : β → β → Prop} [IsTrichotomous α r] [IsTotal β s] :
    IsTotal (α × β) (Prod.Lex r s) :=
  ⟨fun ⟨i, a⟩ ⟨j, b⟩ ↦ by
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (.left _ _ hij)
      -- 🎉 no goals
    · exact (total_of s a b).imp (.right _) (.right _)
      -- 🎉 no goals
    · exact Or.inr (.left _ _ hji) ⟩
      -- 🎉 no goals
#align prod.is_total_right Prod.isTotal_right

instance IsTrichotomous [IsTrichotomous α r] [IsTrichotomous β s] :
  IsTrichotomous (α × β) (Prod.Lex r s) :=
⟨fun ⟨i, a⟩ ⟨j, b⟩ ↦ by
  obtain hij | rfl | hji := trichotomous_of r i j
  { exact Or.inl (Lex.left _ _ hij) }
  -- ⊢ Prod.Lex r s (i, a) (i, b) ∨ (i, a) = (i, b) ∨ Prod.Lex r s (i, b) (i, a)
  { exact (trichotomous_of (s) a b).imp3 (Lex.right _) (congr_arg _) (Lex.right _) }
  -- ⊢ Prod.Lex r s (i, a) (j, b) ∨ (i, a) = (j, b) ∨ Prod.Lex r s (j, b) (i, a)
  { exact Or.inr (Or.inr $ Lex.left _ _ hji) }⟩
  -- 🎉 no goals

end Prod

open Prod

namespace Function

variable {f : α → γ} {g : β → δ} {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ}

theorem Injective.Prod_map (hf : Injective f) (hg : Injective g) : Injective (map f g) :=
  fun _ _ h ↦ ext (hf (ext_iff.1 h).1) (hg <| (ext_iff.1 h).2)
#align function.injective.prod_map Function.Injective.Prod_map

theorem Surjective.Prod_map (hf : Surjective f) (hg : Surjective g) : Surjective (map f g) :=
  fun p ↦
  let ⟨x, hx⟩ := hf p.1
  let ⟨y, hy⟩ := hg p.2
  ⟨(x, y), Prod.ext hx hy⟩
#align function.surjective.prod_map Function.Surjective.Prod_map

theorem Bijective.Prod_map (hf : Bijective f) (hg : Bijective g) : Bijective (map f g) :=
  ⟨hf.1.Prod_map hg.1, hf.2.Prod_map hg.2⟩
#align function.bijective.prod_map Function.Bijective.Prod_map

theorem LeftInverse.Prod_map (hf : LeftInverse f₁ f₂) (hg : LeftInverse g₁ g₂) :
    LeftInverse (map f₁ g₁) (map f₂ g₂) :=
  fun a ↦ by rw [Prod.map_map, hf.comp_eq_id, hg.comp_eq_id, map_id, id]
             -- 🎉 no goals
#align function.left_inverse.prod_map Function.LeftInverse.Prod_map

theorem RightInverse.Prod_map :
    RightInverse f₁ f₂ → RightInverse g₁ g₂ → RightInverse (map f₁ g₁) (map f₂ g₂) :=
  LeftInverse.Prod_map
#align function.right_inverse.prod_map Function.RightInverse.Prod_map

theorem Involutive.Prod_map {f : α → α} {g : β → β} :
    Involutive f → Involutive g → Involutive (map f g) :=
  LeftInverse.Prod_map
#align function.involutive.prod_map Function.Involutive.Prod_map

end Function

namespace Prod

open Function

@[simp]
theorem map_injective [Nonempty α] [Nonempty β] {f : α → γ} {g : β → δ} :
    Injective (map f g) ↔ Injective f ∧ Injective g :=
  ⟨fun h =>
    ⟨fun a₁ a₂ ha => by
      inhabit β
      -- ⊢ a₁ = a₂
      injection
        @h (a₁, default) (a₂, default) (congr_arg (fun c : γ => Prod.mk c (g default)) ha : _),
      fun b₁ b₂ hb => by
      inhabit α
      -- ⊢ b₁ = b₂
      injection @h (default, b₁) (default, b₂) (congr_arg (Prod.mk (f default)) hb : _)⟩,
      -- 🎉 no goals
    fun h => h.1.Prod_map h.2⟩
#align prod.map_injective Prod.map_injective

@[simp]
theorem map_surjective [Nonempty γ] [Nonempty δ] {f : α → γ} {g : β → δ} :
    Surjective (map f g) ↔ Surjective f ∧ Surjective g :=
  ⟨fun h =>
    ⟨fun c => by
      inhabit δ
      -- ⊢ ∃ a, f a = c
      obtain ⟨⟨a, b⟩, h⟩ := h (c, default)
      -- ⊢ ∃ a, f a = c
      exact ⟨a, congr_arg Prod.fst h⟩,
      -- 🎉 no goals
      fun d => by
      inhabit γ
      -- ⊢ ∃ a, g a = d
      obtain ⟨⟨a, b⟩, h⟩ := h (default, d)
      -- ⊢ ∃ a, g a = d
      exact ⟨b, congr_arg Prod.snd h⟩⟩,
      -- 🎉 no goals
    fun h => h.1.Prod_map h.2⟩
#align prod.map_surjective Prod.map_surjective

@[simp]
theorem map_bijective [Nonempty α] [Nonempty β] {f : α → γ} {g : β → δ} :
    Bijective (map f g) ↔ Bijective f ∧ Bijective g := by
  haveI := Nonempty.map f ‹_›
  -- ⊢ Bijective (map f g) ↔ Bijective f ∧ Bijective g
  haveI := Nonempty.map g ‹_›
  -- ⊢ Bijective (map f g) ↔ Bijective f ∧ Bijective g
  exact (map_injective.and map_surjective).trans (and_and_and_comm)
  -- 🎉 no goals
#align prod.map_bijective Prod.map_bijective

@[simp]
theorem map_leftInverse [Nonempty β] [Nonempty δ] {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α}
    {g₂ : δ → γ} : LeftInverse (map f₁ g₁) (map f₂ g₂) ↔ LeftInverse f₁ f₂ ∧ LeftInverse g₁ g₂ :=
  ⟨fun h =>
    ⟨fun b => by
      inhabit δ
      -- ⊢ f₁ (f₂ b) = b
      exact congr_arg Prod.fst (h (b, default)),
      -- 🎉 no goals
      fun d => by
      inhabit β
      -- ⊢ g₁ (g₂ d) = d
      exact congr_arg Prod.snd (h (default, d))⟩,
      -- 🎉 no goals
    fun h => h.1.Prod_map h.2 ⟩
#align prod.map_left_inverse Prod.map_leftInverse

@[simp]
theorem map_rightInverse [Nonempty α] [Nonempty γ] {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α}
    {g₂ : δ → γ} : RightInverse (map f₁ g₁) (map f₂ g₂) ↔ RightInverse f₁ f₂ ∧ RightInverse g₁ g₂ :=
  map_leftInverse
#align prod.map_right_inverse Prod.map_rightInverse

@[simp]
theorem map_involutive [Nonempty α] [Nonempty β] {f : α → α} {g : β → β} :
    Involutive (map f g) ↔ Involutive f ∧ Involutive g :=
  map_leftInverse
#align prod.map_involutive Prod.map_involutive

end Prod
