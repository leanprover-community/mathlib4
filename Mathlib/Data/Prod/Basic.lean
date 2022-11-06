/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Init.Core
import Mathlib.Init.Data.Prod
import Mathlib.Init.Function
import Mathlib.Logic.Function.Basic

/-!
# Extra facts about `prod`

This file defines `prod.swap : α × β → β × α` and proves various simple lemmas about `prod`.
-/

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

@[simp]
theorem Prod_map (f : α → γ) (g : β → δ) (p : α × β) : Prod.map f g p = (f p.1, g p.2) :=
  rfl
#align prod_map Prod_map

namespace Prod

@[simp]
theorem «forall» {p : α × β → Prop} : (∀ x, p x) ↔ ∀ a b, p (a, b) :=
  ⟨fun h a b => h (a, b), fun h ⟨a, b⟩ => h a b⟩

@[simp]
theorem «exists» {p : α × β → Prop} : (∃ x, p x) ↔ ∃ a b, p (a, b) :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

theorem forall' {p : α → β → Prop} : (∀ x : α × β, p x.1 x.2) ↔ ∀ a b, p a b :=
  Prod.forall

theorem exists' {p : α → β → Prop} : (∃ x : α × β, p x.1 x.2) ↔ ∃ a b, p a b :=
  Prod.exists

@[simp]
theorem snd_comp_mk (x : α) : Prod.snd ∘ (Prod.mk x : β → α × β) = id :=
  rfl

@[simp]
theorem fst_comp_mk (x : α) : Prod.fst ∘ (Prod.mk x : β → α × β) = Function.const β x :=
  rfl

@[simp]
theorem map_mk (f : α → γ) (g : β → δ) (a : α) (b : β) : map f g (a, b) = (f a, g b) :=
  rfl

theorem map_fst (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).1 = f p.1 :=
  rfl

theorem map_snd (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).2 = g p.2 :=
  rfl

theorem map_fst' (f : α → γ) (g : β → δ) : Prod.fst ∘ map f g = f ∘ Prod.fst :=
  funext <| map_fst f g

theorem map_snd' (f : α → γ) (g : β → δ) : Prod.snd ∘ map f g = g ∘ Prod.snd :=
  funext <| map_snd f g

/-- Composing a `Prod.map` with another `Prod.map` is equal to
a single `Prod.map` of composed functions.
-/
theorem map_comp_map {ε ζ : Type _} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) :
    Prod.map g g' ∘ Prod.map f f' = Prod.map (g ∘ f) (g' ∘ f') :=
  rfl

/-- Composing a `Prod.map` with another `Prod.map` is equal to
a single `Prod.map` of composed functions, fully applied.
-/
theorem map_map {ε ζ : Type _} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) (x : α × γ) :
    Prod.map g g' (Prod.map f f' x) = Prod.map (g ∘ f) (g' ∘ f') x :=
  rfl

-- Porting note: mathlib3 proof uses `by cc` for the mpr direction
-- Porting note: `@[simp]` tag removed because auto-generated `mk.injEq` simplifies LHS
-- @[simp]
theorem mk.inj_iff {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  Iff.of_eq (mk.injEq _ _ _ _)

theorem mk.inj_left {α β : Type _} (a : α) : Function.Injective (Prod.mk a : β → α × β) := by
  intro b₁ b₂ h
  simpa only [true_and, Prod.mk.inj_iff, eq_self_iff_true] using h

theorem mk.inj_right {α β : Type _} (b : β) :
    Function.Injective (fun a => Prod.mk a b : α → α × β) := by
  intro b₁ b₂ h
  simpa only [and_true, eq_self_iff_true, mk.inj_iff] using h

theorem ext_iff {p q : α × β} : p = q ↔ p.1 = q.1 ∧ p.2 = q.2 := by
  rw [← @mk.eta _ _ p, ← @mk.eta _ _ q, mk.inj_iff]

@[ext]
theorem extₓ {α β} {p q : α × β} (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q :=
  ext_iff.2 ⟨h₁, h₂⟩
#align prod.ext Prod.extₓ

theorem map_def {f : α → γ} {g : β → δ} : Prod.map f g = fun p : α × β => (f p.1, g p.2) :=
  funext fun p => extₓ (map_fst f g p) (map_snd f g p)

theorem id_prod : (fun p : α × β => (p.1, p.2)) = id :=
  rfl

theorem map_id : Prod.map (@id α) (@id β) = id :=
  id_prod

theorem fst_surjective [h : Nonempty β] : Function.Surjective (@fst α β) :=
  fun x => h.elim fun y => ⟨⟨x, y⟩, rfl⟩

theorem snd_surjective [h : Nonempty α] : Function.Surjective (@snd α β) :=
  fun y => h.elim fun x => ⟨⟨x, y⟩, rfl⟩

theorem fst_injective [Subsingleton β] : Function.Injective (@fst α β) :=
  fun _ _ h => extₓ h (Subsingleton.elim _ _)

theorem snd_injective [Subsingleton α] : Function.Injective (@snd α β) :=
  fun _ _ h => extₓ (Subsingleton.elim _ _) h

/-- Swap the factors of a product. `swap (a, b) = (b, a)` -/
def swap : α × β → β × α := fun p => (p.2, p.1)

@[simp]
theorem swap_swap : ∀ x : α × β, swap (swap x) = x
  | ⟨_, _⟩ => rfl

@[simp]
theorem fst_swap {p : α × β} : (swap p).1 = p.2 :=
  rfl

@[simp]
theorem snd_swap {p : α × β} : (swap p).2 = p.1 :=
  rfl

@[simp]
theorem swap_prod_mk {a : α} {b : β} : swap (a, b) = (b, a) :=
  rfl

@[simp]
theorem swap_swap_eq : swap ∘ swap = @id (α × β) :=
  funext swap_swap

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

theorem swap_surjective : Function.Surjective (@swap α β) :=
  swap_leftInverse.surjective

/- warning: prod.swap_bijective -> Prod.swap_bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.Bijective.{(max (succ u_1) (succ u_2)) (max (succ u_2) (succ u_1))} (Prod.{u_1 u_2} α β) (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.Bijective.{(max (succ u_1) (succ u_2)) (max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β)
Case conversion may be inaccurate. Consider using '#align prod.swap_bijective Prod.swap_bijectiveₓ'. -/
theorem swap_bijective : Function.Bijective (@swap α β) :=
  ⟨swap_injective, swap_surjective⟩

/- warning: prod.swap_inj -> Prod.swap_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_2) (succ u_1))} (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β p) (Prod.swap.{u_1 u_2} α β q)) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p q)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β p) (Prod.swap.{u_1 u_2} α β q)) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p q)
Case conversion may be inaccurate. Consider using '#align prod.swap_inj Prod.swap_injₓ'. -/
@[simp]
theorem swap_inj {p q : α × β} : swap p = swap q ↔ p = q :=
  swap_injective.eq_iff

/- warning: prod.eq_iff_fst_eq_snd_eq -> Prod.eq_iff_fst_eq_snd_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p q) (And (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) (Prod.fst.{u_1 u_2} α β q)) (Eq.{succ u_2} β (Prod.snd.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β q)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p q) (And (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) (Prod.fst.{u_1 u_2} α β q)) (Eq.{succ u_2} β (Prod.snd.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β q)))
Case conversion may be inaccurate. Consider using '#align prod.eq_iff_fst_eq_snd_eq Prod.eq_iff_fst_eq_snd_eqₓ'. -/
theorem eq_iff_fst_eq_snd_eq : ∀ {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
  | ⟨p₁, p₂⟩, ⟨q₁, q₂⟩ => by simp

/- warning: prod.fst_eq_iff -> Prod.fst_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {x : α}, Iff (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) x) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p (Prod.mk.{u_1 u_2} α β x (Prod.snd.{u_1 u_2} α β p)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {x : α}, Iff (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) x) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p (Prod.mk.{u_1 u_2} α β x (Prod.snd.{u_1 u_2} α β p)))
Case conversion may be inaccurate. Consider using '#align prod.fst_eq_iff Prod.fst_eq_iffₓ'. -/
theorem fst_eq_iff : ∀ {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)
  | ⟨a, b⟩, x => by simp

/- warning: prod.snd_eq_iff -> Prod.snd_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {x : β}, Iff (Eq.{succ u_2} β (Prod.snd.{u_1 u_2} α β p) x) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p (Prod.mk.{u_1 u_2} α β (Prod.fst.{u_1 u_2} α β p) x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {x : β}, Iff (Eq.{succ u_2} β (Prod.snd.{u_1 u_2} α β p) x) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p (Prod.mk.{u_1 u_2} α β (Prod.fst.{u_1 u_2} α β p) x))
Case conversion may be inaccurate. Consider using '#align prod.snd_eq_iff Prod.snd_eq_iffₓ'. -/
theorem snd_eq_iff : ∀ {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)
  | ⟨a, b⟩, x => by simp

/- warning: prod.lex_def -> Prod.lex_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (r : α -> α -> Prop) (s : β -> β -> Prop) {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Prod.Lex.{u_1 u_2} α β r s p q) (Or (r (Prod.fst.{u_1 u_2} α β p) (Prod.fst.{u_1 u_2} α β q)) (And (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) (Prod.fst.{u_1 u_2} α β q)) (s (Prod.snd.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β q))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (r : α -> α -> Prop) (s : β -> β -> Prop) {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Prod.Lex.{u_1 u_2} α β r s p q) (Or (r (Prod.fst.{u_1 u_2} α β p) (Prod.fst.{u_1 u_2} α β q)) (And (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) (Prod.fst.{u_1 u_2} α β q)) (s (Prod.snd.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β q))))
Case conversion may be inaccurate. Consider using '#align prod.lex_def Prod.lex_defₓ'. -/
theorem lex_def (r : α → α → Prop) (s : β → β → Prop) {p q : α × β} :
    Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2 :=
  ⟨fun h => by cases h <;> simp [*], fun h =>
    match p, q, h with
    | (a, b), (c, d), Or.inl h => Lex.left _ _ h
    | (a, b), (c, d), Or.inr ⟨e, h⟩ => by change a = c at e <;> subst e <;> exact lex.right _ h⟩

instance Lex.decidable [DecidableEq α] (r : α → α → Prop) (s : β → β → Prop) [DecidableRel r] [DecidableRel s] :
    DecidableRel (Prod.Lex r s) := fun p q => decidable_of_decidable_of_iff (by infer_instance) (lex_def r s).symm

@[refl]
theorem Lex.refl_left (r : α → α → Prop) (s : β → β → Prop) [IsRefl α r] : ∀ x, Prod.Lex r s x x
  | (x₁, x₂) => Lex.left _ _ (refl _)

instance is_refl_left {r : α → α → Prop} {s : β → β → Prop} [IsRefl α r] : IsRefl (α × β) (Lex r s) :=
  ⟨Lex.refl_left _ _⟩

@[refl]
theorem Lex.refl_right (r : α → α → Prop) (s : β → β → Prop) [IsRefl β s] : ∀ x, Prod.Lex r s x x
  | (x₁, x₂) => Lex.right _ (refl _)

instance is_refl_right {r : α → α → Prop} {s : β → β → Prop} [IsRefl β s] : IsRefl (α × β) (Lex r s) :=
  ⟨Lex.refl_right _ _⟩

@[trans]
theorem Lex.trans {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] :
    ∀ {x y z : α × β}, Prod.Lex r s x y → Prod.Lex r s y z → Prod.Lex r s x z
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.left _ _ hxy₁, lex.left _ _ hyz₁ => Lex.left _ _ (trans hxy₁ hyz₁)
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.left _ _ hxy₁, lex.right _ hyz₂ => Lex.left _ _ hxy₁
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.right _ _, lex.left _ _ hyz₁ => Lex.left _ _ hyz₁
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.right _ hxy₂, lex.right _ hyz₂ => Lex.right _ (trans hxy₂ hyz₂)

instance {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] : IsTrans (α × β) (Lex r s) :=
  ⟨fun _ _ _ => Lex.trans⟩

instance {r : α → α → Prop} {s : β → β → Prop} [IsStrictOrder α r] [IsAntisymm β s] : IsAntisymm (α × β) (Lex r s) :=
  ⟨fun x₁ x₂ h₁₂ h₂₁ =>
    match x₁, x₂, h₁₂, h₂₁ with
    | (a₁, b₁), (a₂, b₂), lex.left _ _ hr₁, lex.left _ _ hr₂ => (irrefl a₁ (trans hr₁ hr₂)).elim
    | (a₁, b₁), (a₂, b₂), lex.left _ _ hr₁, lex.right _ _ => (irrefl _ hr₁).elim
    | (a₁, b₁), (a₂, b₂), lex.right _ _, lex.left _ _ hr₂ => (irrefl _ hr₂).elim
    | (a₁, b₁), (a₂, b₂), lex.right _ hs₁, lex.right _ hs₂ => antisymm hs₁ hs₂ ▸ rfl⟩

instance is_total_left {r : α → α → Prop} {s : β → β → Prop} [IsTotal α r] : IsTotal (α × β) (Lex r s) :=
  ⟨fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => (IsTotal.total a₁ a₂).imp (Lex.left _ _) (Lex.left _ _)⟩

instance is_total_right {r : α → α → Prop} {s : β → β → Prop} [IsTrichotomous α r] [IsTotal β s] :
    IsTotal (α × β) (Lex r s) :=
  ⟨fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (lex.left _ _ hij)

    · exact (total_of s a b).imp (lex.right _) (lex.right _)

    · exact Or.inr (lex.left _ _ hji)
      ⟩

end Prod

open Prod

namespace Function

variable {f : α → γ} {g : β → δ} {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ}

/- warning: function.injective.prod_map -> Function.Injective.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, (Function.Injective.{succ u_1 succ u_3} α γ f) -> (Function.Injective.{succ u_2 succ u_4} β δ g) -> (Function.Injective.{(max (succ u_1) (succ u_2)) (max (succ u_3) (succ u_4))} (Prod.{u_1 u_2} α β) (Prod.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_2}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, (Function.Injective.{succ u_1 succ u_2} α γ f) -> (Function.Injective.{succ u_3 succ u_4} β δ g) -> (Function.Injective.{(max (succ u_3) (succ u_1)) (max (succ u_4) (succ u_2))} (Prod.{u_1 u_3} α β) (Prod.{u_2 u_4} γ δ) (Prod.map.{u_1 u_2 u_3 u_4} α γ β δ f g))
Case conversion may be inaccurate. Consider using '#align function.injective.prod_map Function.Injective.prod_mapₓ'. -/
theorem Injective.prod_map (hf : Injective f) (hg : Injective g) : Injective (map f g) := fun x y h =>
  ext (hf (ext_iff.1 h).1) (hg <| (ext_iff.1 h).2)

/- warning: function.surjective.prod_map -> Function.Surjective.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, (Function.Surjective.{succ u_1 succ u_3} α γ f) -> (Function.Surjective.{succ u_2 succ u_4} β δ g) -> (Function.Surjective.{(max (succ u_1) (succ u_2)) (max (succ u_3) (succ u_4))} (Prod.{u_1 u_2} α β) (Prod.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_2}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, (Function.Surjective.{succ u_1 succ u_2} α γ f) -> (Function.Surjective.{succ u_3 succ u_4} β δ g) -> (Function.Surjective.{(max (succ u_3) (succ u_1)) (max (succ u_4) (succ u_2))} (Prod.{u_1 u_3} α β) (Prod.{u_2 u_4} γ δ) (Prod.map.{u_1 u_2 u_3 u_4} α γ β δ f g))
Case conversion may be inaccurate. Consider using '#align function.surjective.prod_map Function.Surjective.prod_mapₓ'. -/
theorem Surjective.prod_map (hf : Surjective f) (hg : Surjective g) : Surjective (map f g) := fun p =>
  let ⟨x, hx⟩ := hf p.1
  let ⟨y, hy⟩ := hg p.2
  ⟨(x, y), Prod.ext hx hy⟩

theorem Bijective.prod_map (hf : Bijective f) (hg : Bijective g) : Bijective (map f g) :=
  ⟨hf.1.prod_map hg.1, hf.2.prod_map hg.2⟩

theorem LeftInverse.prod_map (hf : LeftInverse f₁ f₂) (hg : LeftInverse g₁ g₂) : LeftInverse (map f₁ g₁) (map f₂ g₂) :=
  fun a => by rw [Prod.map_map, hf.comp_eq_id, hg.comp_eq_id, map_id, id]

theorem RightInverse.prod_map : RightInverse f₁ f₂ → RightInverse g₁ g₂ → RightInverse (map f₁ g₁) (map f₂ g₂) :=
  left_inverse.prod_map

theorem Involutive.prod_map {f : α → α} {g : β → β} : Involutive f → Involutive g → Involutive (map f g) :=
  left_inverse.prod_map

end Function
