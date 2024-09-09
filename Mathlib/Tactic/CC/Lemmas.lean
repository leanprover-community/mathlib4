/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Mathlib.Init.Logic

/-! Lemmas use by the congruence closure module -/

namespace Mathlib.Tactic.CC

theorem iff_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ↔ b) = b :=
  h.symm ▸ propext true_iff_iff

theorem iff_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ↔ b) = a :=
  h.symm ▸ propext iff_true_iff

theorem iff_eq_true_of_eq {a b : Prop} (h : a = b) : (a ↔ b) = True :=
  h ▸ propext (iff_self_iff _)

theorem and_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ∧ b) = b :=
  h.symm ▸ propext (true_and_iff _)

theorem and_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ∧ b) = a :=
  h.symm ▸ propext (and_true_iff _)

theorem and_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a ∧ b) = False :=
  h.symm ▸ propext (false_and_iff _)

theorem and_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a ∧ b) = False :=
  h.symm ▸ propext (and_false_iff _)

theorem and_eq_of_eq {a b : Prop} (h : a = b) : (a ∧ b) = a :=
  h ▸ propext and_self_iff

theorem or_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ∨ b) = True :=
  h.symm ▸ propext (true_or_iff _)

theorem or_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ∨ b) = True :=
  h.symm ▸ propext (or_true_iff _)

theorem or_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a ∨ b) = b :=
  h.symm ▸ propext (false_or_iff _)

theorem or_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a ∨ b) = a :=
  h.symm ▸ propext (or_false_iff _)

theorem or_eq_of_eq {a b : Prop} (h : a = b) : (a ∨ b) = a :=
  h ▸ propext or_self_iff

theorem imp_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a → b) = b :=
  h.symm ▸ propext ⟨fun h ↦ h trivial, fun h₁ _ ↦ h₁⟩

theorem imp_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a → b) = True :=
  h.symm ▸ propext ⟨fun _ ↦ trivial, fun h₁ _ ↦ h₁⟩

theorem imp_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a → b) = True :=
  h.symm ▸ propext ⟨fun _ ↦ trivial, fun _ h₂ ↦ False.elim h₂⟩

theorem imp_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a → b) = Not a :=
  h.symm ▸ propext ⟨fun h ↦ h, fun hna ha ↦ hna ha⟩

/- Remark: the congruence closure module will only use the following lemma is
   `CCConfig.em` is `true`. -/
theorem not_imp_eq_of_eq_false_right {a b : Prop} (h : b = False) : (Not a → b) = a :=
  h.symm ▸ propext (Iff.intro (
    fun h' ↦ Classical.byContradiction fun hna ↦ h' hna) fun ha hna ↦ hna ha)

theorem imp_eq_true_of_eq {a b : Prop} (h : a = b) : (a → b) = True :=
  h ▸ propext ⟨fun _ ↦ trivial, fun _ ha ↦ ha⟩

theorem not_eq_of_eq_true {a : Prop} (h : a = True) : Not a = False :=
  h.symm ▸ propext not_true

theorem not_eq_of_eq_false {a : Prop} (h : a = False) : Not a = True :=
  h.symm ▸ propext not_false_iff

theorem false_of_a_eq_not_a {a : Prop} (h : a = Not a) : False :=
  have : Not a := fun ha ↦ absurd ha (Eq.mp h ha)
  absurd (Eq.mpr h this) this

universe u

theorem if_eq_of_eq_true {c : Prop} [d : Decidable c] {α : Sort u} (t e : α) (h : c = True) :
    @ite α c d t e = t :=
  if_pos (of_eq_true h)

theorem if_eq_of_eq_false {c : Prop} [d : Decidable c] {α : Sort u} (t e : α) (h : c = False) :
    @ite α c d t e = e :=
  if_neg (not_of_eq_false h)

theorem if_eq_of_eq (c : Prop) [d : Decidable c] {α : Sort u} {t e : α} (h : t = e) :
    @ite α c d t e = t :=
  match d with
  | isTrue _ => rfl
  | isFalse _ => Eq.symm h

theorem eq_true_of_and_eq_true_left {a b : Prop} (h : (a ∧ b) = True) : a = True :=
  eq_true (And.left (of_eq_true h))

theorem eq_true_of_and_eq_true_right {a b : Prop} (h : (a ∧ b) = True) : b = True :=
  eq_true (And.right (of_eq_true h))

theorem eq_false_of_or_eq_false_left {a b : Prop} (h : (a ∨ b) = False) : a = False :=
  eq_false fun ha ↦ False.elim (Eq.mp h (Or.inl ha))

theorem eq_false_of_or_eq_false_right {a b : Prop} (h : (a ∨ b) = False) : b = False :=
  eq_false fun hb ↦ False.elim (Eq.mp h (Or.inr hb))

theorem eq_false_of_not_eq_true {a : Prop} (h : Not a = True) : a = False :=
  eq_false fun ha ↦ absurd ha (Eq.mpr h trivial)

/- Remark: the congruence closure module will only use the following lemma is
   `CCConfig.em` is `true`. -/
theorem eq_true_of_not_eq_false {a : Prop} (h : Not a = False) : a = True :=
  eq_true (Classical.byContradiction fun hna ↦ Eq.mp h hna)

end Mathlib.Tactic.CC
