/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.sigma.lex
! leanprover-community/lean commit 9af482290ef68e8aaa5ead01aa7b09b7be7019fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Mathlib.Init.Data.Sigma.Basic
import Mathlib.Init.Meta.Default

universe u v

namespace PSigma

section

variable {α : Sort u} {β : α → Sort v}

variable (r : α → α → Prop)

variable (s : ∀ a, β a → β a → Prop)

#print PSigma.Lex /-
-- Lexicographical order based on r and s
inductive Lex : PSigma β → PSigma β → Prop
  | left : ∀ {a₁ : α} (b₁ : β a₁) {a₂ : α} (b₂ : β a₂), r a₁ a₂ → Lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  | right : ∀ (a : α) {b₁ b₂ : β a}, s a b₁ b₂ → Lex ⟨a, b₁⟩ ⟨a, b₂⟩
#align psigma.lex PSigma.Lex
-/

end

section

open WellFounded Tactic

parameter {α : Sort u} {β : α → Sort v}

parameter {r : α → α → Prop} {s : ∀ a : α, β a → β a → Prop}

local infixl:50 "≺" => Lex r s

theorem lex_accessible {a} (aca : Acc r a) (acb : ∀ a, WellFounded (s a)) :
    ∀ b : β a, Acc (Lex r s) ⟨a, b⟩ :=
  Acc.recOn aca fun xa aca (iha : ∀ y, r y xa → ∀ b : β y, Acc (Lex r s) ⟨y, b⟩) => fun b : β xa =>
    Acc.recOn (WellFounded.apply (acb xa) b)
      fun xb acb (ihb : ∀ y : β xa, s xa y xb → Acc (Lex r s) ⟨xa, y⟩) =>
      Acc.intro ⟨xa, xb⟩ fun p (lt : p≺⟨xa, xb⟩) =>
        have aux : xa = xa → HEq xb xb → Acc (Lex r s) p :=
          @PSigma.Lex.rec_on α β r s (fun p₁ p₂ => p₂.1 = xa → HEq p₂.2 xb → Acc (Lex r s) p₁) p
            ⟨xa, xb⟩ lt
            (fun (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) (h : r a₁ a₂) (eq₂ : a₂ = xa)
                (eq₃ : HEq b₂ xb) =>
              by subst eq₂; exact iha a₁ h b₁)
            fun (a : α) (b₁ b₂ : β a) (h : s a b₁ b₂) (eq₂ : a = xa) (eq₃ : HEq b₂ xb) => by
            subst eq₂
            have new_eq₃ := eq_of_hEq eq₃
            subst new_eq₃
            exact ihb b₁ h
        aux rfl (HEq.refl xb)
#align psigma.lex_accessible PSigma.lex_accessible

-- The lexicographical order of well founded relations is well-founded
theorem lex_wf (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lex_accessible (WellFounded.apply ha a) hb b
#align psigma.lex_wf PSigma.lex_wf

end

section

parameter {α : Sort u} {β : Sort v}

def LexNdep (r : α → α → Prop) (s : β → β → Prop) :=
  Lex r fun a : α => s
#align psigma.lex_ndep PSigma.LexNdep

theorem lexNdep_wf {r : α → α → Prop} {s : β → β → Prop} (ha : WellFounded r) (hb : WellFounded s) :
    WellFounded (lex_ndep r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lex_accessible (WellFounded.apply ha a) (fun x => hb) b
#align psigma.lex_ndep_wf PSigma.lexNdep_wf

end

section

variable {α : Sort u} {β : Sort v}

variable (r : α → α → Prop)

variable (s : β → β → Prop)

#print PSigma.RevLex /-
-- Reverse lexicographical order based on r and s
inductive RevLex : (@PSigma α fun a => β) → (@PSigma α fun a => β) → Prop
  | left : ∀ {a₁ a₂ : α} (b : β), r a₁ a₂ → rev_lex ⟨a₁, b⟩ ⟨a₂, b⟩
  | right : ∀ (a₁ : α) {b₁ : β} (a₂ : α) {b₂ : β}, s b₁ b₂ → rev_lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
#align psigma.rev_lex PSigma.RevLex
-/

end

section

open WellFounded Tactic

parameter {α : Sort u} {β : Sort v}

parameter {r : α → α → Prop} {s : β → β → Prop}

local infixl:50 "≺" => RevLex r s

theorem revLex_accessible {b} (acb : Acc s b) (aca : ∀ a, Acc r a) : ∀ a, Acc (RevLex r s) ⟨a, b⟩ :=
  Acc.recOn acb fun xb acb (ihb : ∀ y, s y xb → ∀ a, Acc (RevLex r s) ⟨a, y⟩) => fun a =>
    Acc.recOn (aca a) fun xa aca (iha : ∀ y, r y xa → Acc (RevLex r s) (mk y xb)) =>
      Acc.intro ⟨xa, xb⟩ fun p (lt : p≺⟨xa, xb⟩) =>
        have aux : xa = xa → xb = xb → Acc (RevLex r s) p :=
          @RevLex.rec_on α β r s (fun p₁ p₂ => fst p₂ = xa → snd p₂ = xb → Acc (RevLex r s) p₁) p
            ⟨xa, xb⟩ lt
            (fun a₁ a₂ b (h : r a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b = xb) =>
              show Acc (RevLex r s) ⟨a₁, b⟩ from
                have r₁ : r a₁ xa := Eq.recOn eq₂ h
                have aux : Acc (RevLex r s) ⟨a₁, xb⟩ := iha a₁ r₁
                Eq.recOn (Eq.symm eq₃) aux)
            fun a₁ b₁ a₂ b₂ (h : s b₁ b₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb) =>
            show Acc (RevLex r s) (mk a₁ b₁) from
              have s₁ : s b₁ xb := Eq.recOn eq₃ h
              ihb b₁ s₁ a₁
        aux rfl rfl
#align psigma.rev_lex_accessible PSigma.revLex_accessible

theorem revLex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => rev_lex_accessible (apply hb b) (WellFounded.apply ha) a
#align psigma.rev_lex_wf PSigma.revLex_wf

end

section

#print PSigma.SkipLeft /-
def SkipLeft (α : Type u) {β : Type v} (s : β → β → Prop) :
    (@PSigma α fun a => β) → (@PSigma α fun a => β) → Prop :=
  RevLex EmptyRelation s
#align psigma.skip_left PSigma.SkipLeft
-/

theorem skipLeft_wf (α : Type u) {β : Type v} {s : β → β → Prop} (hb : WellFounded s) :
    WellFounded (SkipLeft α s) :=
  revLex_wf empty_wf hb
#align psigma.skip_left_wf PSigma.skipLeft_wf

theorem mk_skipLeft {α : Type u} {β : Type v} {b₁ b₂ : β} {s : β → β → Prop} (a₁ a₂ : α)
    (h : s b₁ b₂) : SkipLeft α s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ :=
  RevLex.right _ _ h
#align psigma.mk_skip_left PSigma.mk_skipLeft

end

instance hasWellFounded {α : Type u} {β : α → Type v} [s₁ : WellFoundedRelation α]
    [s₂ : ∀ a, WellFoundedRelation (β a)] : WellFoundedRelation (PSigma β) where
  R := Lex s₁.R fun a => (s₂ a).R
  wf := lex_wf s₁.wf fun a => (s₂ a).wf
#align psigma.has_well_founded PSigma.hasWellFounded

end PSigma

