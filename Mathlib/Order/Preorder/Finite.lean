/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Minimal

/-!
# Finite preorders and finite sets in a preorder

This file shows that non-empty finite sets in a preorder have minimal/maximal elements, and
contrapositively that non-empty sets without minimal or maximal elements are infinite.
-/

public section

variable {ι α β : Type*}

namespace Finset
section IsTrans
variable [LE α] [IsTrans α LE.le] {s : Finset α} {a : α}

lemma exists_maximalFor (f : ι → α) (s : Finset ι) (hs : s.Nonempty) :
    ∃ i, MaximalFor (· ∈ s) f i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => exact ⟨i, by simp⟩
  | @cons i s hi hs ih =>
    obtain ⟨j, hj⟩ := ih
    by_cases hji : f j ≤ f i
    · refine ⟨i, mem_cons_self .., ?_⟩
      simp only [mem_cons, forall_eq_or_imp, imp_self, true_and]
      exact fun k hk hik ↦ _root_.trans (hj.2 hk <| _root_.trans hji hik) hji
    · exact ⟨j, mem_cons_of_mem hj.1, by simpa [hji] using hj.2⟩

lemma exists_minimalFor (f : ι → α) (s : Finset ι) (hs : s.Nonempty) :
    ∃ i, MinimalFor (· ∈ s) f i := exists_maximalFor (α := αᵒᵈ) f s hs

lemma exists_maximal (hs : s.Nonempty) : ∃ i, Maximal (· ∈ s) i := s.exists_maximalFor id hs
lemma exists_minimal (hs : s.Nonempty) : ∃ i, Minimal (· ∈ s) i := s.exists_minimalFor id hs

end IsTrans

section Preorder
variable [Preorder α] {s : Finset α} {a : α}

lemma exists_le_maximal (s : Finset α) (ha : a ∈ s) : ∃ b, a ≤ b ∧ Maximal (· ∈ s) b := by
  classical
  obtain ⟨b, hb, hab, hbmin⟩ : ∃ b ∈ s, a ≤ b ∧ _ := by
    simpa [Maximal, and_assoc] using {x ∈ s | a ≤ x}.exists_maximal ⟨a, mem_filter.2 ⟨ha, le_rfl⟩⟩
  exact ⟨b, hab, hb, fun c hc hbc ↦ hbmin hc (hab.trans hbc) hbc⟩

lemma exists_le_minimal (s : Finset α) (ha : a ∈ s) : ∃ b ≤ a, Minimal (· ∈ s) b :=
  exists_le_maximal (α := αᵒᵈ) s ha

end Preorder

section LinearOrder
variable [LinearOrder α] [DenselyOrdered α]

theorem exists_between {s t : Finset α}
    (hs : s.Nonempty) (ht : t.Nonempty) (H : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert _root_.exists_between (a₁ := s.max' hs) (a₂ := t.min' ht) (by simp_all) <;> simp

theorem exists_between' (s t : Finset α) [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  by_cases hs : s.Nonempty <;> by_cases ht : t.Nonempty
  · exact s.exists_between hs ht H
  · exact let ⟨p, hp⟩ := exists_gt (s.max' hs); ⟨p, by simp_all⟩
  · exact let ⟨p, hp⟩ := exists_lt (t.min' ht); ⟨p, by simp_all⟩
  · exact Nonempty.elim ‹_› fun p ↦ ⟨p, by simp_all⟩

theorem _root_.Set.Finite.exists_between {s t : Set α}
    (hsf : s.Finite) (hs : s.Nonempty) (htf : t.Finite) (ht : t.Nonempty)
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert Finset.exists_between (s := hsf.toFinset) (t := htf.toFinset)
    (by simpa) (by simpa) (by simpa) using 1; simp

theorem _root_.Set.Finite.exists_between' [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
    {s t : Set α} (hs : s.Finite) (ht : t.Finite)
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert hs.toFinset.exists_between' ht.toFinset (by simpa) using 1; simp

end LinearOrder
end Finset

namespace Set
section IsTrans
variable [LE α] [IsTrans α LE.le] {s : Set α} {a : α}

lemma Finite.exists_maximalFor (f : ι → α) (s : Set ι) (h : s.Finite) (hs : s.Nonempty) :
    ∃ i, MaximalFor (· ∈ s) f i := by
  lift s to Finset ι using h; exact s.exists_maximalFor f hs

lemma Finite.exists_minimalFor (f : ι → α) (s : Set ι) (h : s.Finite) (hs : s.Nonempty) :
    ∃ i, MinimalFor (· ∈ s) f i := Finite.exists_maximalFor (α := αᵒᵈ) f s h hs

lemma Finite.exists_maximal (h : s.Finite) (hs : s.Nonempty) : ∃ i, Maximal (· ∈ s) i :=
  h.exists_maximalFor id _ hs

lemma Finite.exists_minimal (h : s.Finite) (hs : s.Nonempty) : ∃ i, Minimal (· ∈ s) i :=
  h.exists_minimalFor id _ hs

/-- A version of `Finite.exists_maximalFor` with the (weaker) hypothesis that the image of `s`
is finite rather than `s` itself. -/
lemma Finite.exists_maximalFor' (f : ι → α) (s : Set ι) (h : (f '' s).Finite) (hs : s.Nonempty) :
    ∃ i, MaximalFor (· ∈ s) f i := by
  obtain ⟨_, ⟨a, ha, rfl⟩, hmax⟩ := Finite.exists_maximalFor id (f '' s) h (hs.image f)
  exact ⟨a, ha, fun a' ha' hf ↦ hmax (mem_image_of_mem f ha') hf⟩

/-- A version of `Finite.exists_minimalFor` with the (weaker) hypothesis that the image of `s`
is finite rather than `s` itself. -/
lemma Finite.exists_minimalFor' (f : ι → α) (s : Set ι) (h : (f '' s).Finite) (hs : s.Nonempty) :
    ∃ i, MinimalFor (· ∈ s) f i := h.exists_maximalFor' (α := αᵒᵈ) f s hs

end IsTrans

section Preorder
variable [Preorder α] {s : Set α} {a : α}

lemma Finite.exists_le_maximal (hs : s.Finite) (ha : a ∈ s) : ∃ b, a ≤ b ∧ Maximal (· ∈ s) b := by
  lift s to Finset α using hs; exact s.exists_le_maximal ha

lemma Finite.exists_le_minimal (hs : s.Finite) (ha : a ∈ s) : ∃ b, b ≤ a ∧ Minimal (· ∈ s) b := by
  lift s to Finset α using hs; exact s.exists_le_minimal ha

variable [Nonempty α]

lemma infinite_of_forall_exists_gt (h : ∀ a, ∃ b ∈ s, a < b) : s.Infinite := by
  inhabit α
  let f (n : ℕ) : α := Nat.recOn n (h default).choose fun _ a ↦ (h a).choose
  have hf : ∀ n, f n ∈ s := by rintro (_ | _) <;> exact (h _).choose_spec.1
  exact infinite_of_injective_forall_mem
    (strictMono_nat_of_lt_succ fun n => (h _).choose_spec.2).injective hf

lemma infinite_of_forall_exists_lt (h : ∀ a, ∃ b ∈ s, b < a) : s.Infinite :=
  infinite_of_forall_exists_gt (α := αᵒᵈ) h

end Preorder

section PartialOrder
variable (α) [PartialOrder α]

lemma finite_isTop : {a : α | IsTop a}.Finite := (subsingleton_isTop α).finite
lemma finite_isBot : {a : α | IsBot a}.Finite := (subsingleton_isBot α).finite

end PartialOrder

section LinearOrder
variable [LinearOrder α] {s : Set α} {t : Set β} {f : α → β}

lemma Infinite.exists_lt_map_eq_of_mapsTo (hs : s.Infinite) (hf : MapsTo f s t) (ht : t.Finite) :
    ∃ x ∈ s, ∃ y ∈ s, x < y ∧ f x = f y :=
  let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_mapsTo hf ht
  hxy.lt_or_gt.elim (fun hxy => ⟨x, hx, y, hy, hxy, hf⟩) fun hyx => ⟨y, hy, x, hx, hyx, hf.symm⟩

lemma Finite.exists_lt_map_eq_of_forall_mem [Infinite α] (hf : ∀ a, f a ∈ t) (ht : t.Finite) :
    ∃ a b, a < b ∧ f a = f b := by
  rw [← mapsTo_univ_iff] at hf
  obtain ⟨a, -, b, -, h⟩ := infinite_univ.exists_lt_map_eq_of_mapsTo hf ht
  exact ⟨a, b, h⟩

end LinearOrder
end Set

section Preorder
variable [Preorder α] [Finite α] {p : α → Prop} {a : α}

lemma Finite.exists_le_maximal (h : p a) : ∃ b, a ≤ b ∧ Maximal p b :=
  {x | p x}.toFinite.exists_le_maximal h

lemma Finite.exists_le_minimal (h : p a) : ∃ b ≤ a, Minimal p b :=
  {x | p x}.toFinite.exists_le_minimal h

end Preorder
