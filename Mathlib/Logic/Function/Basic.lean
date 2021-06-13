/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Logic.Basic
import Mathlib.Function

namespace Function

theorem left_inverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : left_inverse f g) (hh : left_inverse h i) : left_inverse (h ∘ f) (g ∘ i) :=
λ a => show h (f (g (i a))) = a by rw [hf (i a), hh a]

theorem right_inverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : right_inverse f g) (hh : right_inverse h i) : right_inverse (h ∘ f) (g ∘ i) :=
left_inverse.comp hh hf

@[simp] theorem injective.eq_iff {f: α → β} (I: injective f) {a b: α}:
  f a = f b ↔ a = b := ⟨@I _ _, congr_arg f⟩

theorem injective.eq_iff' {f: α → β} (I: injective f) {a b: α} {c: β} (h: f b = c) :
  f a = c ↔ a = b :=
  h ▸ I.eq_iff
