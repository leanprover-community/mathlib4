/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Daniel Weber
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
public import Mathlib.Data.List.Forall2

/-!
# Big operators on a list in ordered groups with zeros

This file contains the results concerning the interaction of list big operators with ordered
groups with zeros.
-/

public section

namespace List
variable {R : Type*} [CommMonoidWithZero R]

section Preorder
variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R]

lemma prod_nonneg {s : List R} (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_nonneg h.1 (hind h.2)

lemma Forall₂.prod_le_prod₀ {l₁ l₂ : List R} (h : Forall₂ (· ≤ ·) l₁ l₂)
    (h0 : ∀ a ∈ l₁, 0 ≤ a) :
    l₁.prod ≤ l₂.prod := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [prod_cons, forall_mem_cons] at h0 ⊢
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    exact (mul_le_mul_of_nonneg_right hab (prod_nonneg h0.2)).trans
      (mul_le_mul_of_nonneg_left (ih h0.2) (h0.1.trans hab))

lemma Sublist.prod_le_prod₀ {l₁ l₂ : List R} (h : l₁ <+ l₂)
    (h₁ : ∀ a ∈ l₂, (1 : R) ≤ a) : l₁.prod ≤ l₂.prod := by
  have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
  induction h with
  | slnil => rfl
  | cons a _ ih =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact (ih h₁.2).trans
      (le_mul_of_one_le_left (prod_nonneg fun x hx => zero_le_one.trans (h₁.2 x hx)) h₁.1)
  | cons₂ a _ ih =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact mul_le_mul_of_nonneg_left (ih h₁.2) (zero_le_one.trans h₁.1)

lemma SublistForall₂.prod_le_prod₀ {l₁ l₂ : List R}
    (h : SublistForall₂ (· ≤ ·) l₁ l₂) (h0 : ∀ a ∈ l₁, 0 ≤ a)
    (h₁ : ∀ a ∈ l₂, (1 : R) ≤ a) :
    l₁.prod ≤ l₂.prod :=
  let ⟨_, hall, hsub⟩ := sublistForall₂_iff.1 h
  (hall.prod_le_prod₀ h0).trans <| hsub.prod_le_prod₀ h₁

lemma prod_le_prod₀ {ι : Type*} {l : List ι} {f g : ι → R}
    (h0 : ∀ i ∈ l, 0 ≤ f i) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).prod ≤ (l.map g).prod :=
  Forall₂.prod_le_prod₀ (by simpa) (by simpa)

lemma prod_le_pow_card₀ (l : List R) (n : R) (h0 : ∀ x ∈ l, 0 ≤ x) (h : ∀ x ∈ l, x ≤ n) :
    l.prod ≤ n ^ l.length := by
  simpa only [map_id', map_const', prod_replicate] using prod_le_prod₀ h0 h

lemma pow_card_le_prod₀ (l : List R) (n : R) (hn : 0 ≤ n) (h : ∀ x ∈ l, n ≤ x) :
    n ^ l.length ≤ l.prod := by
  simpa only [map_const', prod_replicate, map_id'] using prod_le_prod₀ (fun _ _ => hn) h

lemma one_le_prod₀ {s : List R} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact one_le_mul_of_one_le_of_one_le h.1 (hind h.2)

theorem prod_map_le_prod_map₀ {ι : Type*} {s : List ι} (f : ι → R) (g : ι → R)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    (map f s).prod ≤ (map g s).prod := by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [map_cons, prod_cons]
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    apply mul_le_mul
    · apply h
      simp
    · grind
    · grind [prod_nonneg]
    · apply (h0 _ _).trans (h _ _) <;> simp only [mem_cons, true_or]

theorem prod_map_le_pow_length₀ {ι : Type*} {f : ι → R} {r : R} {t : List ι}
    (hf0 : ∀ x ∈ t, 0 ≤ f x) (hf : ∀ x ∈ t, f x ≤ r) :
    (map f t).prod ≤ r ^ length t := by
  convert prod_map_le_prod_map₀ f (Function.const ι r) hf0 hf
  simp [map_const, prod_replicate]

theorem prod_le_pow_length₀ {r : R} {t : List R} (hf0 : ∀ x ∈ t, 0 ≤ x) (hf : ∀ x ∈ t, x ≤ r) :
    t.prod ≤ r ^ length t := by
  convert prod_map_le_pow_length₀ (f := @id R) hf0 hf
  simp

end Preorder

section PartialOrder
variable [PartialOrder R] [ZeroLEOneClass R] [PosMulStrictMono R] [NeZero (1 : R)]

lemma prod_pos {s : List R} (h : ∀ a ∈ s, 0 < a) : 0 < s.prod := by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_pos h.1 (hind h.2)

lemma prod_lt_prod₀ {ι : Type*} {l : List ι} (f g : ι → R)
    (hf : ∀ i ∈ l, 0 < f i) (h₁ : ∀ i ∈ l, f i ≤ g i) (h₂ : ∃ i ∈ l, f i < g i) :
    (l.map f).prod < (l.map g).prod := by
  induction l with
  | nil => simp at h₂
  | cons i l ihl =>
    simp only [forall_mem_cons, map_cons, prod_cons] at hf h₁ ⊢
    simp only [mem_cons, exists_eq_or_imp] at h₂
    have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
    cases h₂ with
    | inl h =>
      exact mul_lt_mul h (prod_le_prod₀ (fun j hj => (hf.2 j hj).le) h₁.2)
        (prod_pos (by simpa using hf.2)) (hf.1.trans_le h₁.1).le
    | inr h =>
      exact (mul_le_mul_of_nonneg_right h₁.1 (prod_pos (by simpa using hf.2)).le).trans_lt
        (mul_lt_mul_of_pos_left (ihl hf.2 h₁.2 h) (hf.1.trans_le h₁.1))

lemma prod_lt_prod_of_ne_nil₀ {ι : Type*} {l : List ι} (hl : l ≠ []) (f g : ι → R)
    (hf : ∀ i ∈ l, 0 < f i) (hlt : ∀ i ∈ l, f i < g i) :
    (l.map f).prod < (l.map g).prod :=
  prod_lt_prod₀ f g hf (fun i hi => (hlt i hi).le) <|
    (exists_mem_of_ne_nil l hl).imp fun i hi => ⟨hi, hlt i hi⟩

theorem prod_map_lt_prod_map {ι : Type*} {s : List ι} (hs : s ≠ [])
    (f : ι → R) (g : ι → R) (h0 : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i < g i) :
    (map f s).prod < (map g s).prod := by
  match s with
  | [] => contradiction
  | a :: s =>
    simp only [map_cons, prod_cons]
    have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
    apply mul_lt_mul
    · apply h
      simp
    · apply prod_map_le_prod_map₀
      · intro i hi
        apply le_of_lt
        apply h0
        simp [hi]
      · intro i hi
        apply le_of_lt
        apply h
        simp [hi]
    · apply prod_pos
      grind
    · apply le_of_lt ((h0 _ _).trans (h _ _)) <;> simp

end PartialOrder
end List
