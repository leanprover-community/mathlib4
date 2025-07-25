/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Function.Iterate
import Aesop
import Mathlib.Tactic.Inhabit

/-!
# Extra facts about `Prod`

This file proves various simple lemmas about `Prod`.
It also defines better delaborators for product projections.
-/

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

namespace Prod

lemma swap_eq_iff_eq_swap {x : α × β} {y : β × α} : x.swap = y ↔ x = y.swap := by aesop

def mk.injArrow {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort*⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ ↦ Prod.noConfusion h₁ h₂

@[simp]
theorem mk.eta : ∀ {p : α × β}, (p.1, p.2) = p
  | (_, _) => rfl

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

attribute [mfld_simps] map_apply

-- This was previously a `simp` lemma, but no longer is on the basis that it destructures the pair.
--  See `map_apply`, `map_fst`, and `map_snd` for slightly weaker lemmas in the `simp` set.
theorem map_apply' (f : α → γ) (g : β → δ) (p : α × β) : map f g p = (f p.1, g p.2) :=
  rfl

theorem map_fst' (f : α → γ) (g : β → δ) : Prod.fst ∘ map f g = f ∘ Prod.fst :=
  funext <| map_fst f g

theorem map_snd' (f : α → γ) (g : β → δ) : Prod.snd ∘ map f g = g ∘ Prod.snd :=
  funext <| map_snd f g

theorem mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂ := by simp

@[deprecated (since := "2025-03-06")] alias mk.inj_iff := mk_inj

theorem mk_right_injective {α β : Type*} (a : α) : (mk a : β → α × β).Injective := by
  intro b₁ b₂ h
  simpa only [true_and, Prod.mk_inj, eq_self_iff_true] using h

@[deprecated (since := "2025-03-06")] alias mk.inj_left := mk_right_injective

theorem mk_left_injective {α β : Type*} (b : β) : (fun a ↦ mk a b : α → α × β).Injective := by
  intro b₁ b₂ h
  simpa only [and_true, eq_self_iff_true, mk_inj] using h

@[deprecated (since := "2025-03-06")] alias mk.inj_right := mk_left_injective

lemma mk_right_inj {a : α} {b₁ b₂ : β} : (a, b₁) = (a, b₂) ↔ b₁ = b₂ :=
    (mk_right_injective _).eq_iff

lemma mk_left_inj {a₁ a₂ : α} {b : β} : (a₁, b) = (a₂, b) ↔ a₁ = a₂ := (mk_left_injective _).eq_iff

@[deprecated (since := "2025-03-06")] alias mk_inj_left := mk_right_inj
@[deprecated (since := "2025-03-06")] alias mk_inj_right := mk_left_inj

theorem map_def {f : α → γ} {g : β → δ} : Prod.map f g = fun p : α × β ↦ (f p.1, g p.2) :=
  funext fun p ↦ Prod.ext (map_fst f g p) (map_snd f g p)

theorem id_prod : (fun p : α × β ↦ (p.1, p.2)) = id :=
  rfl

@[simp]
theorem map_iterate (f : α → α) (g : β → β) (n : ℕ) :
    (Prod.map f g)^[n] = Prod.map f^[n] g^[n] := by induction n <;> simp [*, Prod.map_comp_map]

theorem fst_surjective [h : Nonempty β] : Function.Surjective (@fst α β) :=
  fun x ↦ h.elim fun y ↦ ⟨⟨x, y⟩, rfl⟩

theorem snd_surjective [h : Nonempty α] : Function.Surjective (@snd α β) :=
  fun y ↦ h.elim fun x ↦ ⟨⟨x, y⟩, rfl⟩

theorem fst_injective [Subsingleton β] : Function.Injective (@fst α β) :=
  fun _ _ h ↦ Prod.ext h (Subsingleton.elim _ _)

theorem snd_injective [Subsingleton α] : Function.Injective (@snd α β) :=
  fun _ _ h ↦ Prod.ext (Subsingleton.elim _ _) h

@[simp]
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap

@[simp]
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap

theorem swap_injective : Function.Injective (@swap α β) :=
  swap_leftInverse.injective

theorem swap_surjective : Function.Surjective (@swap α β) :=
  swap_leftInverse.surjective

theorem swap_bijective : Function.Bijective (@swap α β) :=
  ⟨swap_injective, swap_surjective⟩

theorem _root_.Function.Semiconj.swap_map (f : α → α) (g : β → β) :
    Function.Semiconj swap (map f g) (map g f) :=
  Function.semiconj_iff_comp_eq.2 (map_comp_swap g f).symm

theorem eq_iff_fst_eq_snd_eq : ∀ {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
  | ⟨p₁, p₂⟩, ⟨q₁, q₂⟩ => by simp

theorem fst_eq_iff : ∀ {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)
  | ⟨a, b⟩, x => by simp

theorem snd_eq_iff : ∀ {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)
  | ⟨a, b⟩, x => by simp

variable {r : α → α → Prop} {s : β → β → Prop} {x y : α × β}

lemma lex_iff : Prod.Lex r s x y ↔ r x.1 y.1 ∨ x.1 = y.1 ∧ s x.2 y.2 := lex_def

instance Lex.decidable [DecidableEq α]
    (r : α → α → Prop) (s : β → β → Prop) [DecidableRel r] [DecidableRel s] :
    DecidableRel (Prod.Lex r s) :=
  fun _ _ ↦ decidable_of_decidable_of_iff lex_def.symm

@[refl]
theorem Lex.refl_left (r : α → α → Prop) (s : β → β → Prop) [IsRefl α r] : ∀ x, Prod.Lex r s x x
  | (_, _) => Lex.left _ _ (refl _)

instance {r : α → α → Prop} {s : β → β → Prop} [IsRefl α r] : IsRefl (α × β) (Prod.Lex r s) :=
  ⟨Lex.refl_left _ _⟩

@[refl]
theorem Lex.refl_right (r : α → α → Prop) (s : β → β → Prop) [IsRefl β s] : ∀ x, Prod.Lex r s x x
  | (_, _) => Lex.right _ (refl _)

instance {r : α → α → Prop} {s : β → β → Prop} [IsRefl β s] : IsRefl (α × β) (Prod.Lex r s) :=
  ⟨Lex.refl_right _ _⟩

instance isIrrefl [IsIrrefl α r] [IsIrrefl β s] : IsIrrefl (α × β) (Prod.Lex r s) :=
  ⟨by rintro ⟨i, a⟩ (⟨_, _, h⟩ | ⟨_, h⟩) <;> exact irrefl _ h⟩

set_option linter.style.commandStart false in
@[trans]
theorem Lex.trans {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] :
    ∀ {x y z : α × β}, Prod.Lex r s x y → Prod.Lex r s y z → Prod.Lex r s x z
  | (_, _), (_, _), (_, _), left  _ _ hxy₁, left  _ _ hyz₁ => left  _ _ (_root_.trans hxy₁ hyz₁)
  | (_, _), (_, _), (_, _), left  _ _ hxy₁, right _ _      => left  _ _ hxy₁
  | (_, _), (_, _), (_, _), right _ _,      left  _ _ hyz₁ => left  _ _ hyz₁
  | (_, _), (_, _), (_, _), right _ hxy₂,   right _ hyz₂   => right _ (_root_.trans hxy₂ hyz₂)

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

instance isTotal_right {r : α → α → Prop} {s : β → β → Prop} [IsTrichotomous α r] [IsTotal β s] :
    IsTotal (α × β) (Prod.Lex r s) :=
  ⟨fun ⟨i, a⟩ ⟨j, b⟩ ↦ by
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (.left _ _ hij)
    · exact (total_of s a b).imp (.right _) (.right _)
    · exact Or.inr (.left _ _ hji) ⟩

instance IsTrichotomous [IsTrichotomous α r] [IsTrichotomous β s] :
    IsTrichotomous (α × β) (Prod.Lex r s) :=
⟨fun ⟨i, a⟩ ⟨j, b⟩ ↦ by
  obtain hij | rfl | hji := trichotomous_of r i j
  { exact Or.inl (Lex.left _ _ hij) }
  { exact (trichotomous_of (s) a b).imp3 (Lex.right _) (congr_arg _) (Lex.right _) }
  { exact Or.inr (Or.inr <| Lex.left _ _ hji) }⟩

instance [IsAsymm α r] [IsAsymm β s] :
    IsAsymm (α × β) (Prod.Lex r s) where
  asymm
  | (_a₁, _a₂), (_b₁, _b₂), .left _ _ h₁, .left _ _ h₂ => IsAsymm.asymm _ _ h₂ h₁
  | (_a₁, _a₂), (_, _b₂), .left _ _ h₁, .right _ _ => IsAsymm.asymm _ _ h₁ h₁
  | (_a₁, _a₂), (_, _b₂), .right _ _, .left _ _ h₂ => IsAsymm.asymm _ _ h₂ h₂
  | (_a₁, _a₂), (_, _b₂), .right _ h₁, .right _ h₂ => IsAsymm.asymm _ _ h₁ h₂

end Prod

open Prod

namespace Function

variable {f : α → γ} {g : β → δ} {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ}

theorem Injective.prodMap (hf : Injective f) (hg : Injective g) : Injective (map f g) :=
  fun _ _ h ↦ Prod.ext (hf <| congr_arg Prod.fst h) (hg <| congr_arg Prod.snd h)

theorem Surjective.prodMap (hf : Surjective f) (hg : Surjective g) : Surjective (map f g) :=
  fun p ↦
  let ⟨x, hx⟩ := hf p.1
  let ⟨y, hy⟩ := hg p.2
  ⟨(x, y), Prod.ext hx hy⟩

theorem Bijective.prodMap (hf : Bijective f) (hg : Bijective g) : Bijective (map f g) :=
  ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩

theorem LeftInverse.prodMap (hf : LeftInverse f₁ f₂) (hg : LeftInverse g₁ g₂) :
    LeftInverse (map f₁ g₁) (map f₂ g₂) :=
  fun a ↦ by rw [Prod.map_map, hf.comp_eq_id, hg.comp_eq_id, map_id, id]

theorem RightInverse.prodMap :
    RightInverse f₁ f₂ → RightInverse g₁ g₂ → RightInverse (map f₁ g₁) (map f₂ g₂) :=
  LeftInverse.prodMap

theorem Involutive.prodMap {f : α → α} {g : β → β} :
    Involutive f → Involutive g → Involutive (map f g) :=
  LeftInverse.prodMap

end Function

namespace Prod

open Function

@[simp]
theorem map_injective [Nonempty α] [Nonempty β] {f : α → γ} {g : β → δ} :
    Injective (map f g) ↔ Injective f ∧ Injective g :=
  ⟨fun h =>
    ⟨fun a₁ a₂ ha => by
      inhabit β
      injection
        @h (a₁, default) (a₂, default) (congr_arg (fun c : γ => Prod.mk c (g default)) ha :),
      fun b₁ b₂ hb => by
      inhabit α
      injection @h (default, b₁) (default, b₂) (congr_arg (Prod.mk (f default)) hb :)⟩,
    fun h => h.1.prodMap h.2⟩

@[simp]
theorem map_surjective [Nonempty γ] [Nonempty δ] {f : α → γ} {g : β → δ} :
    Surjective (map f g) ↔ Surjective f ∧ Surjective g :=
  ⟨fun h =>
    ⟨fun c => by
      inhabit δ
      obtain ⟨⟨a, b⟩, h⟩ := h (c, default)
      exact ⟨a, congr_arg Prod.fst h⟩,
      fun d => by
      inhabit γ
      obtain ⟨⟨a, b⟩, h⟩ := h (default, d)
      exact ⟨b, congr_arg Prod.snd h⟩⟩,
    fun h => h.1.prodMap h.2⟩

@[simp]
theorem map_bijective [Nonempty α] [Nonempty β] {f : α → γ} {g : β → δ} :
    Bijective (map f g) ↔ Bijective f ∧ Bijective g := by
  haveI := Nonempty.map f ‹_›
  haveI := Nonempty.map g ‹_›
  exact (map_injective.and map_surjective).trans and_and_and_comm

@[simp]
theorem map_leftInverse [Nonempty β] [Nonempty δ] {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α}
    {g₂ : δ → γ} : LeftInverse (map f₁ g₁) (map f₂ g₂) ↔ LeftInverse f₁ f₂ ∧ LeftInverse g₁ g₂ :=
  ⟨fun h =>
    ⟨fun b => by
      inhabit δ
      exact congr_arg Prod.fst (h (b, default)),
      fun d => by
      inhabit β
      exact congr_arg Prod.snd (h (default, d))⟩,
    fun h => h.1.prodMap h.2 ⟩

@[simp]
theorem map_rightInverse [Nonempty α] [Nonempty γ] {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α}
    {g₂ : δ → γ} : RightInverse (map f₁ g₁) (map f₂ g₂) ↔ RightInverse f₁ f₂ ∧ RightInverse g₁ g₂ :=
  map_leftInverse

@[simp]
theorem map_involutive [Nonempty α] [Nonempty β] {f : α → α} {g : β → β} :
    Involutive (map f g) ↔ Involutive f ∧ Involutive g :=
  map_leftInverse

namespace PrettyPrinting
open Lean PrettyPrinter Delaborator

/--
When true, then `Prod.fst x` and `Prod.snd x` pretty print as `x.1` and `x.2`
rather than as `x.fst` and `x.snd`.
-/
register_option pp.numericProj.prod : Bool := {
  defValue := true
  descr := "enable pretty printing `Prod.fst x` as `x.1` and `Prod.snd x` as `x.2`."
}

/-- Tell whether pretty-printing should use numeric projection notations `.1`
and `.2` for `Prod.fst` and `Prod.snd`. -/
def getPPNumericProjProd (o : Options) : Bool :=
  o.get pp.numericProj.prod.name pp.numericProj.prod.defValue

/-- Delaborator for `Prod.fst x` as `x.1`. -/
@[app_delab Prod.fst]
def delabProdFst : Delab :=
  whenPPOption getPPNumericProjProd <|
  whenPPOption getPPFieldNotation <|
  whenNotPPOption getPPExplicit <|
  withOverApp 3 do
    let x ← SubExpr.withAppArg delab
    `($(x).1)

/-- Delaborator for `Prod.snd x` as `x.2`. -/
@[app_delab Prod.snd]
def delabProdSnd : Delab :=
  whenPPOption getPPNumericProjProd <|
  whenPPOption getPPFieldNotation <|
  whenNotPPOption getPPExplicit <|
  withOverApp 3 do
    let x ← SubExpr.withAppArg delab
    `($(x).2)

end PrettyPrinting

end Prod
