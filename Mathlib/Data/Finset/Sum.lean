/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Sum

/-!
# Disjoint sum of finsets

This file defines the disjoint sum of two finsets as `Finset (α ⊕ β)`. Beware not to confuse with
the `Finset.sum` operation which computes the additive sum.

## Main declarations

* `Finset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
* `Finset.toLeft`: Given a finset of elements `α ⊕ β`, extracts all the elements of the form `α`.
* `Finset.toRight`: Given a finset of elements `α ⊕ β`, extracts all the elements of the form `β`.
-/


open Function Multiset Sum

namespace Finset

variable {α β γ : Type*} (s : Finset α) (t : Finset β)

/-- Disjoint sum of finsets. -/
def disjSum : Finset (α ⊕ β) :=
  ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩

@[simp]
theorem val_disjSum : (s.disjSum t).1 = s.1.disjSum t.1 :=
  rfl

@[simp]
theorem empty_disjSum : (∅ : Finset α).disjSum t = t.map Embedding.inr :=
  val_inj.1 <| Multiset.zero_disjSum _

@[simp]
theorem disjSum_empty : s.disjSum (∅ : Finset β) = s.map Embedding.inl :=
  val_inj.1 <| Multiset.disjSum_zero _

@[simp]
theorem card_disjSum : (s.disjSum t).card = s.card + t.card :=
  Multiset.card_disjSum _ _

theorem disjoint_map_inl_map_inr : Disjoint (s.map Embedding.inl) (t.map Embedding.inr) := by
  simp_rw [disjoint_left, mem_map]
  rintro x ⟨a, _, rfl⟩ ⟨b, _, ⟨⟩⟩

@[simp]
theorem map_inl_disjUnion_map_inr :
    (s.map Embedding.inl).disjUnion (t.map Embedding.inr) (disjoint_map_inl_map_inr _ _) =
      s.disjSum t :=
  rfl

variable {s t} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} {a : α} {b : β} {x : α ⊕ β}

theorem mem_disjSum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
  Multiset.mem_disjSum

@[simp]
theorem inl_mem_disjSum : inl a ∈ s.disjSum t ↔ a ∈ s :=
  Multiset.inl_mem_disjSum

@[simp]
theorem inr_mem_disjSum : inr b ∈ s.disjSum t ↔ b ∈ t :=
  Multiset.inr_mem_disjSum

@[simp]
theorem disjSum_eq_empty : s.disjSum t = ∅ ↔ s = ∅ ∧ t = ∅ := by simp [Finset.ext_iff]

theorem disjSum_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁.disjSum t₁ ⊆ s₂.disjSum t₂ :=
  val_le_iff.1 <| Multiset.disjSum_mono (val_le_iff.2 hs) (val_le_iff.2 ht)

theorem disjSum_mono_left (t : Finset β) : Monotone fun s : Finset α => s.disjSum t :=
  fun _ _ hs => disjSum_mono hs Subset.rfl

theorem disjSum_mono_right (s : Finset α) : Monotone (s.disjSum : Finset β → Finset (α ⊕ β)) :=
  fun _ _ => disjSum_mono Subset.rfl

theorem disjSum_ssubset_disjSum_of_ssubset_of_subset (hs : s₁ ⊂ s₂) (ht : t₁ ⊆ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disjSum_lt_disjSum_of_lt_of_le (val_lt_iff.2 hs) (val_le_iff.2 ht)

theorem disjSum_ssubset_disjSum_of_subset_of_ssubset (hs : s₁ ⊆ s₂) (ht : t₁ ⊂ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disjSum_lt_disjSum_of_le_of_lt (val_le_iff.2 hs) (val_lt_iff.2 ht)

theorem disjSum_strictMono_left (t : Finset β) : StrictMono fun s : Finset α => s.disjSum t :=
  fun _ _ hs => disjSum_ssubset_disjSum_of_ssubset_of_subset hs Subset.rfl

theorem disjSum_strictMono_right (s : Finset α) :
    StrictMono (s.disjSum : Finset β → Finset (α ⊕ β)) := fun _ _ =>
  disjSum_ssubset_disjSum_of_subset_of_ssubset Subset.rfl

@[deprecated (since := "2025-06-11")]
alias disj_sum_strictMono_right := disjSum_strictMono_right

@[simp] lemma disjSum_inj {α β : Type*} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} :
    s₁.disjSum t₁ = s₂.disjSum t₂ ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp [Finset.ext_iff]

lemma Injective2_disjSum {α β : Type*} : Function.Injective2 (@disjSum α β) :=
  fun _ _ _ _ => by simp [Finset.ext_iff]

/--
Given a finset of elements `α ⊕ β`, extract all the elements of the form `α`. This
forms a quasi-inverse to `disjSum`, in that it recovers its left input.

See also `List.partitionMap`.
-/
def toLeft (u : Finset (α ⊕ β)) : Finset α :=
  u.filterMap (Sum.elim some fun _ => none) (by clear x; aesop)

/--
Given a finset of elements `α ⊕ β`, extract all the elements of the form `β`. This
forms a quasi-inverse to `disjSum`, in that it recovers its right input.

See also `List.partitionMap`.
-/
def toRight (u : Finset (α ⊕ β)) : Finset β :=
  u.filterMap (Sum.elim (fun _ => none) some) (by clear x; aesop)

variable {u v : Finset (α ⊕ β)} {a : α} {b : β}

@[simp] lemma mem_toLeft : a ∈ u.toLeft ↔ .inl a ∈ u := by simp [toLeft]
@[simp] lemma mem_toRight : b ∈ u.toRight ↔ .inr b ∈ u := by simp [toRight]

@[gcongr]
lemma toLeft_subset_toLeft : u ⊆ v → u.toLeft ⊆ v.toLeft :=
  fun h _ => by simpa only [mem_toLeft] using @h _

@[gcongr]
lemma toRight_subset_toRight : u ⊆ v → u.toRight ⊆ v.toRight :=
  fun h _ => by simpa only [mem_toRight] using @h _

lemma toLeft_monotone : Monotone (@toLeft α β) := fun _ _ => toLeft_subset_toLeft
lemma toRight_monotone : Monotone (@toRight α β) := fun _ _ => toRight_subset_toRight

lemma toLeft_disjSum_toRight : u.toLeft.disjSum u.toRight = u := by
  ext (x | x) <;> simp

lemma card_toLeft_add_card_toRight : #u.toLeft + #u.toRight = #u := by
  rw [← card_disjSum, toLeft_disjSum_toRight]

lemma card_toLeft_le : #u.toLeft ≤ #u :=
  (Nat.le_add_right _ _).trans_eq card_toLeft_add_card_toRight

lemma card_toRight_le : #u.toRight ≤ #u :=
  (Nat.le_add_left _ _).trans_eq card_toLeft_add_card_toRight

@[simp] lemma toLeft_disjSum : (s.disjSum t).toLeft = s := by ext x; simp

@[simp] lemma toRight_disjSum : (s.disjSum t).toRight = t := by ext x; simp

lemma disjSum_eq_iff : s.disjSum t = u ↔ s = u.toLeft ∧ t = u.toRight :=
  ⟨fun h => by simp [← h], fun h => by simp [h, toLeft_disjSum_toRight]⟩

lemma eq_disjSum_iff : u = s.disjSum t ↔ u.toLeft = s ∧ u.toRight = t :=
  ⟨fun h => by simp [h], fun h => by simp [← h, toLeft_disjSum_toRight]⟩

lemma disjSum_subset : s.disjSum t ⊆ u ↔ s ⊆ u.toLeft ∧ t ⊆ u.toRight := by simp [subset_iff]
lemma subset_disjSum : u ⊆ s.disjSum t ↔ u.toLeft ⊆ s ∧ u.toRight ⊆ t := by simp [subset_iff]

lemma subset_map_inl : u ⊆ s.map .inl ↔ u.toLeft ⊆ s ∧ u.toRight = ∅ := by
  simp [← disjSum_empty, subset_disjSum]

lemma subset_map_inr : u ⊆ t.map .inr ↔ u.toLeft = ∅ ∧ u.toRight ⊆ t := by
  simp [← empty_disjSum, subset_disjSum]

lemma map_inl_subset_iff_subset_toLeft : s.map .inl ⊆ u ↔ s ⊆ u.toLeft := by
  simp [← disjSum_empty, disjSum_subset]

lemma map_inr_subset_iff_subset_toRight : t.map .inr ⊆ u ↔ t ⊆ u.toRight := by
  simp [← empty_disjSum, disjSum_subset]

lemma gc_map_inl_toLeft : GaloisConnection (·.map (.inl : α ↪ α ⊕ β)) toLeft :=
  fun _ _ ↦ map_inl_subset_iff_subset_toLeft

lemma gc_map_inr_toRight : GaloisConnection (·.map (.inr : β ↪ α ⊕ β)) toRight :=
  fun _ _ ↦ map_inr_subset_iff_subset_toRight

@[simp] lemma toLeft_map_sumComm : (u.map (Equiv.sumComm _ _).toEmbedding).toLeft = u.toRight := by
  ext x; simp

@[simp] lemma toRight_map_sumComm : (u.map (Equiv.sumComm _ _).toEmbedding).toRight = u.toLeft := by
  ext x; simp

@[simp] lemma toLeft_cons_inl (ha) :
    (cons (inl a) u ha).toLeft = cons a u.toLeft (by simpa) := by ext y; simp
@[simp] lemma toLeft_cons_inr (hb) :
    (cons (inr b) u hb).toLeft = u.toLeft := by ext y; simp
@[simp] lemma toRight_cons_inl (ha) :
    (cons (inl a) u ha).toRight = u.toRight := by ext y; simp
@[simp] lemma toRight_cons_inr (hb) :
    (cons (inr b) u hb).toRight = cons b u.toRight (by simpa) := by ext y; simp

section
variable [DecidableEq α] [DecidableEq β]

lemma toLeft_image_swap : (u.image Sum.swap).toLeft = u.toRight := by
  ext x; simp

lemma toRight_image_swap : (u.image Sum.swap).toRight = u.toLeft := by
  ext x; simp

@[simp] lemma toLeft_insert_inl : (insert (inl a) u).toLeft = insert a u.toLeft := by ext y; simp
@[simp] lemma toLeft_insert_inr : (insert (inr b) u).toLeft = u.toLeft := by ext y; simp
@[simp] lemma toRight_insert_inl : (insert (inl a) u).toRight = u.toRight := by ext y; simp
@[simp] lemma toRight_insert_inr : (insert (inr b) u).toRight = insert b u.toRight := by ext y; simp

lemma toLeft_inter : (u ∩ v).toLeft = u.toLeft ∩ v.toLeft := by ext x; simp
lemma toRight_inter : (u ∩ v).toRight = u.toRight ∩ v.toRight := by ext x; simp

lemma toLeft_union : (u ∪ v).toLeft = u.toLeft ∪ v.toLeft := by ext x; simp
lemma toRight_union : (u ∪ v).toRight = u.toRight ∪ v.toRight := by ext x; simp

lemma toLeft_sdiff : (u \ v).toLeft = u.toLeft \ v.toLeft := by ext x; simp
lemma toRight_sdiff : (u \ v).toRight = u.toRight \ v.toRight := by ext x; simp

end

/-- Finsets on sum types are equivalent to pairs of finsets on each summand. -/
@[simps apply_fst apply_snd]
def sumEquiv {α β : Type*} : Finset (α ⊕ β) ≃o Finset α × Finset β where
  toFun s := (s.toLeft, s.toRight)
  invFun s := disjSum s.1 s.2
  left_inv s := toLeft_disjSum_toRight
  right_inv s := by simp
  map_rel_iff' := by simp [← Finset.coe_subset, Set.subset_def]

@[simp]
lemma sumEquiv_symm_apply {α β : Type*} (s : Finset α × Finset β) :
    sumEquiv.symm s = disjSum s.1 s.2 := rfl

theorem map_disjSum (f : α ⊕ β ↪ γ) :
    (s.disjSum t).map f =
      (s.map (.trans .inl f)).disjUnion (t.map (.trans .inr f)) (by
        as_aux_lemma =>
          simpa only [← map_map]
            using (Finset.disjoint_map f).2 (disjoint_map_inl_map_inr _ _)) :=
  val_injective <| Multiset.map_disjSum _

lemma fold_disjSum (s : Finset α) (t : Finset β) (f : α ⊕ β → γ) (b₁ b₂ : γ) (op : γ → γ → γ)
    [Std.Commutative op] [Std.Associative op] :
    (s.disjSum t).fold op (op b₁ b₂) f =
      op (s.fold op b₁ (f <| .inl ·)) (t.fold op b₂ (f <| .inr ·)) := by
  simp_rw [fold, disjSum, Multiset.map_disjSum, fold_add]

end Finset
