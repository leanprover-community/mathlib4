/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Part
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.Common

/-!
# Monotonicity of monadic operations on `Part`
-/

open Part

variable {α β γ : Type*} [Preorder α]

section bind
variable {f : α → Part β} {g : α → β → Part γ}

lemma Monotone.partBind (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x ↦ (f x).bind (g x) := by
  rintro x y h a
  simp only [and_imp, Part.mem_bind_iff, exists_imp]
  exact fun b hb ha ↦ ⟨b, hf h _ hb, hg h _ _ ha⟩

lemma Antitone.partBind (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x ↦ (f x).bind (g x) := by
  rintro x y h a
  simp only [and_imp, Part.mem_bind_iff, exists_imp]
  exact fun b hb ha ↦ ⟨b, hf h _ hb, hg h _ _ ha⟩

end bind

section map
variable {f : β → γ} {g : α → Part β}

lemma Monotone.partMap (hg : Monotone g) : Monotone fun x ↦ (g x).map f := by
  simpa only [← bind_some_eq_map] using hg.partBind monotone_const

lemma Antitone.partMap (hg : Antitone g) : Antitone fun x ↦ (g x).map f := by
  simpa only [← bind_some_eq_map] using hg.partBind antitone_const

end map

section seq
variable {β γ : Type _} {f : α → Part (β → γ)} {g : α → Part β}

lemma Monotone.partSeq (hf : Monotone f) (hg : Monotone g) : Monotone fun x ↦ f x <*> g x := by
  simpa only [seq_eq_bind_map] using hf.partBind <| Monotone.of_apply₂ fun _ ↦ hg.partMap

lemma Antitone.partSeq (hf : Antitone f) (hg : Antitone g) : Antitone fun x ↦ f x <*> g x := by
  simpa only [seq_eq_bind_map] using hf.partBind <| Antitone.of_apply₂ fun _ ↦ hg.partMap

end seq

namespace OrderHom

/-- `Part.bind` as a monotone function -/
@[simps]
def partBind (f : α →o Part β) (g : α →o β → Part γ) : α →o Part γ where
  toFun x := (f x).bind (g x)
  monotone' := f.2.partBind g.2

end OrderHom
