/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Data.Set.Subsingleton

/-!
# Subsingleton

Defines the predicate `Subsingleton s : Prop`, saying that `s` has at most one element.

-/

open Function

universe u v

namespace Set

/-! ### Subsingleton -/

section Subsingleton

variable {α : Type u} {s t : Set α} (a : α)

/-- A set `s` is a `Subsingleton` if it has at most one element. -/
protected def Subsingleton (s : Set α) : Prop :=
  ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), x = y
#align set.subsingleton Set.Subsingleton

theorem Subsingleton.anti (ht : t.Subsingleton) (hst : s ⊆ t) : s.Subsingleton := fun _ hx _ hy =>
  ht (hst hx) (hst hy)
#align set.subsingleton.anti Set.Subsingleton.anti

theorem Subsingleton.eq_singleton_of_mem (hs : s.Subsingleton) {x : α} (hx : x ∈ s) : s = {x} :=
  ext fun _ => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩
#align set.subsingleton.eq_singleton_of_mem Set.Subsingleton.eq_singleton_of_mem

@[simp]
theorem subsingleton_empty : (∅ : Set α).Subsingleton := fun _ => False.elim
#align set.subsingleton_empty Set.subsingleton_empty

@[simp]
theorem subsingleton_singleton {a} : ({a} : Set α).Subsingleton := fun _ hx _ hy =>
  (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl
#align set.subsingleton_singleton Set.subsingleton_singleton

theorem subsingleton_of_subset_singleton (h : s ⊆ {a}) : s.Subsingleton :=
  subsingleton_singleton.anti h
#align set.subsingleton_of_subset_singleton Set.subsingleton_of_subset_singleton

theorem subsingleton_of_forall_eq (a : α) (h : ∀ b ∈ s, b = a) : s.Subsingleton := fun _ hb _ hc =>
  (h _ hb).trans (h _ hc).symm
#align set.subsingleton_of_forall_eq Set.subsingleton_of_forall_eq

theorem subsingleton_iff_singleton {x} (hx : x ∈ s) : s.Subsingleton ↔ s = {x} :=
  ⟨fun h => h.eq_singleton_of_mem hx, fun h => h.symm ▸ subsingleton_singleton⟩
#align set.subsingleton_iff_singleton Set.subsingleton_iff_singleton

theorem Subsingleton.eq_empty_or_singleton (hs : s.Subsingleton) : s = ∅ ∨ ∃ x, s = {x} :=
  s.eq_empty_or_nonempty.elim Or.inl fun ⟨x, hx⟩ => Or.inr ⟨x, hs.eq_singleton_of_mem hx⟩
#align set.subsingleton.eq_empty_or_singleton Set.Subsingleton.eq_empty_or_singleton

theorem Subsingleton.induction_on {p : Set α → Prop} (hs : s.Subsingleton) (he : p ∅)
    (h₁ : ∀ x, p {x}) : p s := by
  rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  exacts [he, h₁ _]
#align set.subsingleton.induction_on Set.Subsingleton.induction_on

theorem subsingleton_univ [Subsingleton α] : (univ : Set α).Subsingleton := fun x _ y _ =>
  Subsingleton.elim x y
#align set.subsingleton_univ Set.subsingleton_univ

theorem subsingleton_of_univ_subsingleton (h : (univ : Set α).Subsingleton) : Subsingleton α :=
  ⟨fun a b => h (mem_univ a) (mem_univ b)⟩
#align set.subsingleton_of_univ_subsingleton Set.subsingleton_of_univ_subsingleton

@[simp]
theorem subsingleton_univ_iff : (univ : Set α).Subsingleton ↔ Subsingleton α :=
  ⟨subsingleton_of_univ_subsingleton, fun h => @subsingleton_univ _ h⟩
#align set.subsingleton_univ_iff Set.subsingleton_univ_iff

theorem subsingleton_of_subsingleton [Subsingleton α] {s : Set α} : Set.Subsingleton s :=
  subsingleton_univ.anti (subset_univ s)
#align set.subsingleton_of_subsingleton Set.subsingleton_of_subsingleton

theorem subsingleton_isTop (α : Type*) [PartialOrder α] : Set.Subsingleton { x : α | IsTop x } :=
  fun x hx _ hy => hx.isMax.eq_of_le (hy x)
#align set.subsingleton_is_top Set.subsingleton_isTop

theorem subsingleton_isBot (α : Type*) [PartialOrder α] : Set.Subsingleton { x : α | IsBot x } :=
  fun x hx _ hy => hx.isMin.eq_of_ge (hy x)
#align set.subsingleton_is_bot Set.subsingleton_isBot

theorem exists_eq_singleton_iff_nonempty_subsingleton :
    (∃ a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton := by
  refine' ⟨_, fun h => _⟩
  · rintro ⟨a, rfl⟩
    exact ⟨singleton_nonempty a, subsingleton_singleton⟩
  · exact h.2.eq_empty_or_singleton.resolve_left h.1.ne_empty
#align set.exists_eq_singleton_iff_nonempty_subsingleton Set.exists_eq_singleton_iff_nonempty_subsingleton

/-- `s`, coerced to a type, is a subsingleton type if and only if `s` is a subsingleton set. -/
@[simp, norm_cast]
theorem subsingleton_coe (s : Set α) : Subsingleton s ↔ s.Subsingleton := by
  constructor
  · refine' fun h => fun a ha b hb => _
    exact SetCoe.ext_iff.2 (@Subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩)
  · exact fun h => Subsingleton.intro fun a b => SetCoe.ext (h a.property b.property)
#align set.subsingleton_coe Set.subsingleton_coe

theorem Subsingleton.coe_sort {s : Set α} : s.Subsingleton → Subsingleton s :=
  s.subsingleton_coe.2
#align set.subsingleton.coe_sort Set.Subsingleton.coe_sort

/-- The `coe_sort` of a set `s` in a subsingleton type is a subsingleton.
For the corresponding result for `Subtype`, see `subtype.subsingleton`. -/
instance subsingleton_coe_of_subsingleton [Subsingleton α] {s : Set α} : Subsingleton s := by
  rw [s.subsingleton_coe]
  exact subsingleton_of_subsingleton
#align set.subsingleton_coe_of_subsingleton Set.subsingleton_coe_of_subsingleton

end Subsingleton

section Nontrivial

variable {α : Type u} {a : α} {s t : Set α}

@[simp]
theorem not_subsingleton_iff : ¬s.Subsingleton ↔ s.Nontrivial := by
  simp_rw [Set.Subsingleton, Set.Nontrivial, not_forall, exists_prop]
#align set.not_subsingleton_iff Set.not_subsingleton_iff

@[simp]
theorem not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingleton :=
  Iff.not_left not_subsingleton_iff.symm
#align set.not_nontrivial_iff Set.not_nontrivial_iff

alias ⟨_, Subsingleton.not_nontrivial⟩ := not_nontrivial_iff
#align set.subsingleton.not_nontrivial Set.Subsingleton.not_nontrivial

alias ⟨_, Nontrivial.not_subsingleton⟩ := not_subsingleton_iff
#align set.nontrivial.not_subsingleton Set.Nontrivial.not_subsingleton

protected lemma subsingleton_or_nontrivial (s : Set α) : s.Subsingleton ∨ s.Nontrivial := by
  simp [or_iff_not_imp_right]
#align set.subsingleton_or_nontrivial Set.subsingleton_or_nontrivial

lemma eq_singleton_or_nontrivial (ha : a ∈ s) : s = {a} ∨ s.Nontrivial := by
  rw [← subsingleton_iff_singleton ha]; exact s.subsingleton_or_nontrivial
#align set.eq_singleton_or_nontrivial Set.eq_singleton_or_nontrivial

lemma nontrivial_iff_ne_singleton (ha : a ∈ s) : s.Nontrivial ↔ s ≠ {a} :=
  ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩
#align set.nontrivial_iff_ne_singleton Set.nontrivial_iff_ne_singleton

lemma Nonempty.exists_eq_singleton_or_nontrivial : s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial :=
  fun ⟨a, ha⟩ ↦ (eq_singleton_or_nontrivial ha).imp_left <| Exists.intro a
#align set.nonempty.exists_eq_singleton_or_nontrivial Set.Nonempty.exists_eq_singleton_or_nontrivial

theorem univ_eq_true_false : univ = ({True, False} : Set Prop) :=
  Eq.symm <| eq_univ_of_forall fun x => by
    rw [mem_insert_iff, mem_singleton_iff]
    exact Classical.propComplete x
#align set.univ_eq_true_false Set.univ_eq_true_false

end Nontrivial
section Monotonicity

/-! ### Monotonicity on singletons -/

variable {α : Type u} {β : Type v} {a : α} {s : Set α} [Preorder α] [Preorder β] (f : α → β)

protected theorem Subsingleton.monotoneOn (h : s.Subsingleton) : MonotoneOn f s :=
  fun _ ha _ hb _ => (congr_arg _ (h ha hb)).le
#align set.subsingleton.monotone_on Set.Subsingleton.monotoneOn

protected theorem Subsingleton.antitoneOn (h : s.Subsingleton) : AntitoneOn f s :=
  fun _ ha _ hb _ => (congr_arg _ (h hb ha)).le
#align set.subsingleton.antitone_on Set.Subsingleton.antitoneOn

protected theorem Subsingleton.strictMonoOn (h : s.Subsingleton) : StrictMonoOn f s :=
  fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim
#align set.subsingleton.strict_mono_on Set.Subsingleton.strictMonoOn

protected theorem Subsingleton.strictAntiOn (h : s.Subsingleton) : StrictAntiOn f s :=
  fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim
#align set.subsingleton.strict_anti_on Set.Subsingleton.strictAntiOn

@[simp]
theorem monotoneOn_singleton : MonotoneOn f {a} :=
  subsingleton_singleton.monotoneOn f
#align set.monotone_on_singleton Set.monotoneOn_singleton

@[simp]
theorem antitoneOn_singleton : AntitoneOn f {a} :=
  subsingleton_singleton.antitoneOn f
#align set.antitone_on_singleton Set.antitoneOn_singleton

@[simp]
theorem strictMonoOn_singleton : StrictMonoOn f {a} :=
  subsingleton_singleton.strictMonoOn f
#align set.strict_mono_on_singleton Set.strictMonoOn_singleton

@[simp]
theorem strictAntiOn_singleton : StrictAntiOn f {a} :=
  subsingleton_singleton.strictAntiOn f
#align set.strict_anti_on_singleton Set.strictAntiOn_singleton

end Monotonicity

end Set
