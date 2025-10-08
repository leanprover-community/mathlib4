/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Batteries.Data.List.Perm
import Mathlib.Logic.Relation
import Mathlib.Order.RelClasses
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.InsertIdx

/-!
# List Permutations

This file develops theory about the `List.Perm` relation.

## Notation

The notation `~` is used for permutation equivalence.
-/

-- Make sure we don't import algebra
assert_not_exists Monoid

open Nat

namespace List
variable {α β : Type*} {l : List α}

open Perm (swap)

lemma perm_rfl : l ~ l := Perm.refl _

attribute [symm] Perm.symm
attribute [trans] Perm.trans

instance : IsSymm (List α) Perm := ⟨fun _ _ ↦ .symm⟩

theorem Perm.subset_congr_left {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₁ ⊆ l₃ ↔ l₂ ⊆ l₃ :=
  ⟨h.symm.subset.trans, h.subset.trans⟩

theorem Perm.subset_congr_right {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₃ ⊆ l₁ ↔ l₃ ⊆ l₂ :=
  ⟨fun h' => h'.trans h.subset, fun h' => h'.trans h.symm.subset⟩

theorem set_perm_cons_eraseIdx {n : ℕ} (h : n < l.length) (a : α) :
    l.set n a ~ a :: l.eraseIdx n := by
  rw [← insertIdx_eraseIdx_self h.ne]
  apply perm_insertIdx
  rw [length_eraseIdx_of_lt h]
  exact Nat.le_sub_one_of_lt h

theorem getElem_cons_eraseIdx_perm {n : ℕ} (h : n < l.length) :
    l[n] :: l.eraseIdx n ~ l := by
  simpa [h] using (set_perm_cons_eraseIdx h l[n]).symm

theorem perm_insertIdx_iff_of_le {l₁ l₂ : List α} {m n : ℕ} (hm : m ≤ l₁.length)
    (hn : n ≤ l₂.length) (a : α) : l₁.insertIdx m a ~ l₂.insertIdx n a ↔ l₁ ~ l₂ := by
  rw [rel_congr_left (perm_insertIdx _ _ hm), rel_congr_right (perm_insertIdx _ _ hn), perm_cons]

alias ⟨_, Perm.insertIdx_of_le⟩ := perm_insertIdx_iff_of_le

@[simp]
theorem perm_insertIdx_iff {l₁ l₂ : List α} {n : ℕ} {a : α} :
    l₁.insertIdx n a ~ l₂.insertIdx n a ↔ l₁ ~ l₂ := by
  wlog hle : length l₁ ≤ length l₂ generalizing l₁ l₂
  · rw [perm_comm, this (le_of_not_ge hle), perm_comm]
  cases Nat.lt_or_ge (length l₁) n with
  | inl hn₁ =>
    rw [insertIdx_of_length_lt hn₁]
    cases Nat.lt_or_ge (length l₂) n with
    | inl hn₂ => rw [insertIdx_of_length_lt hn₂]
    | inr hn₂ =>
      apply iff_of_false
      · intro h
        rw [h.length_eq] at hn₁
        exact (hn₁.trans_le hn₂).not_ge (length_le_length_insertIdx ..)
      · exact fun h ↦ (hn₁.trans_le hn₂).not_ge h.length_eq.ge
  | inr hn₁ =>
    exact perm_insertIdx_iff_of_le hn₁ (le_trans hn₁ hle) _

@[gcongr]
protected theorem Perm.insertIdx {l₁ l₂ : List α} (h : l₁ ~ l₂) (n : ℕ) (a : α) :
    l₁.insertIdx n a ~ l₂.insertIdx n a :=
  perm_insertIdx_iff.mpr h

theorem perm_eraseIdx_of_getElem?_eq {l₁ l₂ : List α} {m n : ℕ} (h : l₁[m]? = l₂[n]?) :
    eraseIdx l₁ m ~ eraseIdx l₂ n ↔ l₁ ~ l₂ := by
  cases Nat.lt_or_ge m l₁.length with
  | inl hm =>
    rw [getElem?_eq_getElem hm, eq_comm, getElem?_eq_some_iff] at h
    cases h with
    | intro hn hnm =>
      rw [← perm_cons l₁[m], rel_congr_left (getElem_cons_eraseIdx_perm ..), ← hnm,
        rel_congr_right (getElem_cons_eraseIdx_perm ..)]
  | inr hm =>
    rw [getElem?_eq_none hm, eq_comm, getElem?_eq_none_iff] at h
    rw [eraseIdx_of_length_le h, eraseIdx_of_length_le hm]

alias ⟨_, Perm.eraseIdx_of_getElem?_eq⟩ := perm_eraseIdx_of_getElem?_eq

section Rel

open Relator

variable {r : α → β → Prop}

local infixr:80 " ∘r " => Relation.Comp

theorem perm_comp_perm : (Perm ∘r Perm : List α → List α → Prop) = Perm := by
  funext a c; apply propext
  constructor
  · exact fun ⟨b, hab, hba⟩ => Perm.trans hab hba
  · exact fun h => ⟨a, Perm.refl a, h⟩

theorem perm_comp_forall₂ {l u v} (hlu : Perm l u) (huv : Forall₂ r u v) :
    (Forall₂ r ∘r Perm) l v := by
  induction hlu generalizing v with
  | nil => cases huv; exact ⟨[], Forall₂.nil, Perm.nil⟩
  | cons u _hlu ih =>
    obtain - | ⟨hab, huv'⟩ := huv
    rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩
    exact ⟨_ :: l₂, Forall₂.cons hab h₁₂, h₂₃.cons _⟩
  | swap a₁ a₂ h₂₃ =>
    obtain - | ⟨h₁, hr₂₃⟩ := huv
    obtain - | ⟨h₂, h₁₂⟩ := hr₂₃
    exact ⟨_, Forall₂.cons h₂ (Forall₂.cons h₁ h₁₂), Perm.swap _ _ _⟩
  | trans _ _ ih₁ ih₂ =>
    rcases ih₂ huv with ⟨lb₂, hab₂, h₂₃⟩
    rcases ih₁ hab₂ with ⟨lb₁, hab₁, h₁₂⟩
    exact ⟨lb₁, hab₁, Perm.trans h₁₂ h₂₃⟩

theorem forall₂_comp_perm_eq_perm_comp_forall₂ : Forall₂ r ∘r Perm = Perm ∘r Forall₂ r := by
  funext l₁ l₃; apply propext
  constructor
  · intro h
    rcases h with ⟨l₂, h₁₂, h₂₃⟩
    have : Forall₂ (flip r) l₂ l₁ := h₁₂.flip
    rcases perm_comp_forall₂ h₂₃.symm this with ⟨l', h₁, h₂⟩
    exact ⟨l', h₂.symm, h₁.flip⟩
  · exact fun ⟨l₂, h₁₂, h₂₃⟩ => perm_comp_forall₂ h₁₂ h₂₃

theorem eq_map_comp_perm (f : α → β) : (· = map f ·) ∘r (· ~ ·) = (· ~ map f ·) := by
  conv_rhs => rw [← Relation.comp_eq_fun (map f)]
  simp only [← forall₂_eq_eq_eq, forall₂_map_right_iff, forall₂_comp_perm_eq_perm_comp_forall₂]

theorem rel_perm_imp (hr : RightUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· → ·)) Perm Perm :=
  fun a b h₁ c d h₂ h =>
  have : (flip (Forall₂ r) ∘r Perm ∘r Forall₂ r) b d := ⟨a, h₁, c, h, h₂⟩
  have : ((flip (Forall₂ r) ∘r Forall₂ r) ∘r Perm) b d := by
    rwa [← forall₂_comp_perm_eq_perm_comp_forall₂, ← Relation.comp_assoc] at this
  let ⟨b', ⟨_, hbc, hcb⟩, hbd⟩ := this
  have : b' = b := right_unique_forall₂' hr hcb hbc
  this ▸ hbd

theorem rel_perm (hr : BiUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· ↔ ·)) Perm Perm :=
  fun _a _b hab _c _d hcd =>
  Iff.intro (rel_perm_imp hr.2 hab hcd) (rel_perm_imp hr.left.flip hab.flip hcd.flip)

end Rel

lemma count_eq_count_filter_add [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (l : List α) (a : α) :
    count a l = count a (l.filter P) + count a (l.filter (¬ P ·)) := by
  convert countP_eq_countP_filter_add l _ P
  simp only [decide_not]

theorem Perm.foldl_eq {f : β → α → β} {l₁ l₂ : List α} [rcomm : RightCommutative f] (p : l₁ ~ l₂) :
    ∀ b, foldl f b l₁ = foldl f b l₂ :=
  p.foldl_eq' fun x _hx y _hy z => rcomm.right_comm z x y

theorem Perm.foldr_eq {f : α → β → β} {l₁ l₂ : List α} [lcomm : LeftCommutative f] (p : l₁ ~ l₂) :
    ∀ b, foldr f b l₁ = foldr f b l₂ := by
  intro b
  induction p using Perm.recOnSwap' generalizing b with
  | nil => rfl
  | cons _ _ r  => simp [r b]
  | swap' _ _ _ r => simp only [foldr_cons]; rw [lcomm.left_comm, r b]
  | trans _ _ r₁ r₂ => exact Eq.trans (r₁ b) (r₂ b)

section

variable {op : α → α → α} [IA : Std.Associative op] [IC : Std.Commutative op]

local notation a " * " b => op a b

local notation l " <*> " a => foldl op a l

theorem Perm.foldl_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : (l₁ <*> a) = l₂ <*> a :=
  h.foldl_eq _

theorem Perm.foldr_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : l₁.foldr op a = l₂.foldr op a :=
  h.foldr_eq _

end

theorem perm_option_toList {o₁ o₂ : Option α} : o₁.toList ~ o₂.toList ↔ o₁ = o₂ := by
  refine ⟨fun p => ?_, fun e => e ▸ Perm.refl _⟩
  rcases o₁ with - | a <;> rcases o₂ with - | b; · rfl
  · cases p.length_eq
  · cases p.length_eq
  · exact Option.mem_toList.1 (p.symm.subset <| by simp)

theorem perm_replicate_append_replicate
    [DecidableEq α] {l : List α} {a b : α} {m n : ℕ} (h : a ≠ b) :
    l ~ replicate m a ++ replicate n b ↔ count a l = m ∧ count b l = n ∧ l ⊆ [a, b] := by
  rw [perm_iff_count, ← Decidable.and_forall_ne a, ← Decidable.and_forall_ne b]
  suffices l ⊆ [a, b] ↔ ∀ c, c ≠ b → c ≠ a → c ∉ l by
    simp +contextual [count_replicate, h, this, count_eq_zero, Ne.symm]
  trans ∀ c, c ∈ l → c = b ∨ c = a
  · simp [subset_def, or_comm]
  · exact forall_congr' fun _ => by rw [← and_imp, ← not_or, not_imp_not]

theorem map_perm_map_iff {l' : List α} {f : α → β} (hf : f.Injective) :
    map f l ~ map f l' ↔ l ~ l' := calc
  map f l ~ map f l' ↔ Relation.Comp (· = map f ·) (· ~ ·) (map f l) l' := by rw [eq_map_comp_perm]
  _ ↔ l ~ l' := by simp [Relation.Comp, map_inj_right hf]

theorem Perm.flatMap_left (l : List α) {f g : α → List β} (h : ∀ a ∈ l, f a ~ g a) :
    l.flatMap f ~ l.flatMap g :=
  Perm.flatten_congr <| by
    rwa [List.forall₂_map_right_iff, List.forall₂_map_left_iff, List.forall₂_same]

@[gcongr]
protected theorem Perm.flatMap {l₁ l₂ : List α} {f g : α → List β} (h : l₁ ~ l₂)
    (hfg : ∀ a ∈ l₁, f a ~ g a) : l₁.flatMap f ~ l₂.flatMap g :=
  .trans (.flatMap_left _ hfg) (h.flatMap_right _)

theorem flatMap_append_perm (l : List α) (f g : α → List β) :
    l.flatMap f ++ l.flatMap g ~ l.flatMap fun x => f x ++ g x := by
  induction l with | nil => simp | cons a l IH => ?_
  simp only [flatMap_cons, append_assoc]
  refine (Perm.trans ?_ (IH.append_left _)).append_left _
  rw [← append_assoc, ← append_assoc]
  exact perm_append_comm.append_right _

theorem map_append_flatMap_perm (l : List α) (f : α → β) (g : α → List β) :
    l.map f ++ l.flatMap g ~ l.flatMap fun x => f x :: g x := by
  simpa [← map_eq_flatMap] using flatMap_append_perm l (fun x => [f x]) g

theorem Perm.product_right {l₁ l₂ : List α} (t₁ : List β) (p : l₁ ~ l₂) :
    product l₁ t₁ ~ product l₂ t₁ :=
  p.flatMap_right _

theorem Perm.product_left (l : List α) {t₁ t₂ : List β} (p : t₁ ~ t₂) :
    product l t₁ ~ product l t₂ :=
  (Perm.flatMap_left _) fun _ _ => p.map _

@[gcongr]
theorem Perm.product {l₁ l₂ : List α} {t₁ t₂ : List β} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) :
    product l₁ t₁ ~ product l₂ t₂ :=
  (p₁.product_right t₁).trans (p₂.product_left l₂)

end List
