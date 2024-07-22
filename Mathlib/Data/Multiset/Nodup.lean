/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Range
import Mathlib.Data.Multiset.Range

/-!
# The `Nodup` predicate for multisets without duplicate elements.
-/


namespace Multiset

open Function List

variable {α β γ : Type*} {r : α → α → Prop} {s t : Multiset α} {a : α}

-- nodup
/-- `Nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1. -/
def Nodup (s : Multiset α) : Prop :=
  Quot.liftOn s List.Nodup fun _ _ p => propext p.nodup_iff

@[simp]
theorem coe_nodup {l : List α} : @Nodup α l ↔ l.Nodup :=
  Iff.rfl

@[simp]
theorem nodup_zero : @Nodup α 0 :=
  Pairwise.nil

@[simp]
theorem nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ s) ↔ a ∉ s ∧ Nodup s :=
  Quot.induction_on s fun _ => List.nodup_cons

theorem Nodup.cons (m : a ∉ s) (n : Nodup s) : Nodup (a ::ₘ s) :=
  nodup_cons.2 ⟨m, n⟩

@[simp]
theorem nodup_singleton : ∀ a : α, Nodup ({a} : Multiset α) :=
  List.nodup_singleton

theorem Nodup.of_cons (h : Nodup (a ::ₘ s)) : Nodup s :=
  (nodup_cons.1 h).2

theorem Nodup.not_mem (h : Nodup (a ::ₘ s)) : a ∉ s :=
  (nodup_cons.1 h).1

theorem nodup_of_le {s t : Multiset α} (h : s ≤ t) : Nodup t → Nodup s :=
  Multiset.leInductionOn h fun {_ _} => Nodup.sublist

theorem not_nodup_pair : ∀ a : α, ¬Nodup (a ::ₘ a ::ₘ 0) :=
  List.not_nodup_pair

theorem nodup_iff_le {s : Multiset α} : Nodup s ↔ ∀ a : α, ¬a ::ₘ a ::ₘ 0 ≤ s :=
  Quot.induction_on s fun _ =>
    nodup_iff_sublist.trans <| forall_congr' fun a => not_congr (@replicate_le_coe _ a 2 _).symm

theorem nodup_iff_ne_cons_cons {s : Multiset α} : s.Nodup ↔ ∀ a t, s ≠ a ::ₘ a ::ₘ t :=
  nodup_iff_le.trans
    ⟨fun h a t s_eq => h a (s_eq.symm ▸ cons_le_cons a (cons_le_cons a (zero_le _))), fun h a le =>
      let ⟨t, s_eq⟩ := le_iff_exists_add.mp le
      h a t (by rwa [cons_add, cons_add, zero_add] at s_eq)⟩

theorem nodup_iff_count_le_one [DecidableEq α] {s : Multiset α} : Nodup s ↔ ∀ a, count a s ≤ 1 :=
  Quot.induction_on s fun _l => by
    simp only [quot_mk_to_coe'', coe_nodup, mem_coe, coe_count]
    exact List.nodup_iff_count_le_one

theorem nodup_iff_count_eq_one [DecidableEq α] : Nodup s ↔ ∀ a ∈ s, count a s = 1 :=
  Quot.induction_on s fun _l => by simpa using List.nodup_iff_count_eq_one

@[simp]
theorem count_eq_one_of_mem [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) (h : a ∈ s) :
    count a s = 1 :=
  nodup_iff_count_eq_one.mp d a h

theorem count_eq_of_nodup [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) :
    count a s = if a ∈ s then 1 else 0 := by
  split_ifs with h
  · exact count_eq_one_of_mem d h
  · exact count_eq_zero_of_not_mem h

theorem nodup_iff_pairwise {α} {s : Multiset α} : Nodup s ↔ Pairwise (· ≠ ·) s :=
  Quotient.inductionOn s fun _ => (pairwise_coe_iff_pairwise fun _ _ => Ne.symm).symm

protected theorem Nodup.pairwise : (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) → Nodup s → Pairwise r s :=
  Quotient.inductionOn s fun l h hl => ⟨l, rfl, hl.imp_of_mem fun {a b} ha hb => h a ha b hb⟩

theorem Pairwise.forall (H : Symmetric r) (hs : Pairwise r s) :
    ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → r a b :=
  let ⟨_, hl₁, hl₂⟩ := hs
  hl₁.symm ▸ hl₂.forall H

theorem nodup_add {s t : Multiset α} : Nodup (s + t) ↔ Nodup s ∧ Nodup t ∧ Disjoint s t :=
  Quotient.inductionOn₂ s t fun _ _ => nodup_append

theorem disjoint_of_nodup_add {s t : Multiset α} (d : Nodup (s + t)) : Disjoint s t :=
  (nodup_add.1 d).2.2

theorem Nodup.add_iff (d₁ : Nodup s) (d₂ : Nodup t) : Nodup (s + t) ↔ Disjoint s t := by
  simp [nodup_add, d₁, d₂]

theorem Nodup.of_map (f : α → β) : Nodup (map f s) → Nodup s :=
  Quot.induction_on s fun _ => List.Nodup.of_map f

theorem Nodup.map_on {f : α → β} :
    (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) → Nodup s → Nodup (map f s) :=
  Quot.induction_on s fun _ => List.Nodup.map_on

theorem Nodup.map {f : α → β} {s : Multiset α} (hf : Injective f) : Nodup s → Nodup (map f s) :=
  Nodup.map_on fun _ _ _ _ h => hf h

theorem nodup_map_iff_of_inj_on {f : α → β} (d : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) :
    Nodup (map f s) ↔ Nodup s :=
  ⟨Nodup.of_map _, fun h => h.map_on d⟩

theorem nodup_map_iff_of_injective {f : α → β} (d : Function.Injective f) :
    Nodup (map f s) ↔ Nodup s :=
  ⟨Nodup.of_map _, fun h => h.map d⟩

theorem inj_on_of_nodup_map {f : α → β} {s : Multiset α} :
    Nodup (map f s) → ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  Quot.induction_on s fun _ => List.inj_on_of_nodup_map

theorem nodup_map_iff_inj_on {f : α → β} {s : Multiset α} (d : Nodup s) :
    Nodup (map f s) ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩

theorem Nodup.filter (p : α → Prop) [DecidablePred p] {s} : Nodup s → Nodup (filter p s) :=
  Quot.induction_on s fun _ => List.Nodup.filter (p ·)

@[simp]
theorem nodup_attach {s : Multiset α} : Nodup (attach s) ↔ Nodup s :=
  Quot.induction_on s fun _ => List.nodup_attach

protected alias ⟨_, Nodup.attach⟩ := nodup_attach

theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {s : Multiset α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) : Nodup s → Nodup (pmap f s H) :=
  Quot.induction_on s (fun _ _ => List.Nodup.pmap hf) H

instance nodupDecidable [DecidableEq α] (s : Multiset α) : Decidable (Nodup s) :=
  Quotient.recOnSubsingleton s fun l => l.nodupDecidable

theorem Nodup.erase_eq_filter [DecidableEq α] (a : α) {s} :
    Nodup s → s.erase a = Multiset.filter (· ≠ a) s :=
  Quot.induction_on s fun _ d =>
    congr_arg ((↑) : List α → Multiset α) <| List.Nodup.erase_eq_filter d a

theorem Nodup.erase [DecidableEq α] (a : α) {l} : Nodup l → Nodup (l.erase a) :=
  nodup_of_le (erase_le _ _)

theorem Nodup.mem_erase_iff [DecidableEq α] {a b : α} {l} (d : Nodup l) :
    a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [d.erase_eq_filter b, mem_filter, and_comm]

theorem Nodup.not_mem_erase [DecidableEq α] {a : α} {s} (h : Nodup s) : a ∉ s.erase a := fun ha =>
  (h.mem_erase_iff.1 ha).1 rfl

protected theorem Nodup.filterMap (f : α → Option β) (H : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    Nodup s → Nodup (filterMap f s) :=
  Quot.induction_on s fun _ => List.Nodup.filterMap H

theorem nodup_range (n : ℕ) : Nodup (range n) :=
  List.nodup_range _

theorem Nodup.inter_left [DecidableEq α] (t) : Nodup s → Nodup (s ∩ t) :=
  nodup_of_le <| inter_le_left _ _

theorem Nodup.inter_right [DecidableEq α] (s) : Nodup t → Nodup (s ∩ t) :=
  nodup_of_le <| inter_le_right _ _

@[simp]
theorem nodup_union [DecidableEq α] {s t : Multiset α} : Nodup (s ∪ t) ↔ Nodup s ∧ Nodup t :=
  ⟨fun h => ⟨nodup_of_le (le_union_left _ _) h, nodup_of_le (le_union_right _ _) h⟩, fun ⟨h₁, h₂⟩ =>
    nodup_iff_count_le_one.2 fun a => by
      rw [count_union]
      exact max_le (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩

theorem Nodup.ext {s t : Multiset α} : Nodup s → Nodup t → (s = t ↔ ∀ a, a ∈ s ↔ a ∈ t) :=
  Quotient.inductionOn₂ s t fun _ _ d₁ d₂ => Quotient.eq.trans <| perm_ext_iff_of_nodup d₁ d₂

theorem le_iff_subset {s t : Multiset α} : Nodup s → (s ≤ t ↔ s ⊆ t) :=
  Quotient.inductionOn₂ s t fun _ _ d => ⟨subset_of_le, d.subperm⟩

theorem range_le {m n : ℕ} : range m ≤ range n ↔ m ≤ n :=
  (le_iff_subset (nodup_range _)).trans range_subset

theorem mem_sub_of_nodup [DecidableEq α] {a : α} {s t : Multiset α} (d : Nodup s) :
    a ∈ s - t ↔ a ∈ s ∧ a ∉ t :=
  ⟨fun h =>
    ⟨mem_of_le tsub_le_self h, fun h' => by
      refine count_eq_zero.1 ?_ h
      rw [count_sub a s t, Nat.sub_eq_zero_iff_le]
      exact le_trans (nodup_iff_count_le_one.1 d _) (count_pos.2 h')⟩,
    fun ⟨h₁, h₂⟩ => Or.resolve_right (mem_add.1 <| mem_of_le le_tsub_add h₁) h₂⟩

theorem map_eq_map_of_bij_of_nodup (f : α → γ) (g : β → γ) {s : Multiset α} {t : Multiset β}
    (hs : s.Nodup) (ht : t.Nodup) (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) (h : ∀ a ha, f a = g (i a ha)) : s.map f = t.map g := by
  have : t = s.attach.map fun x => i x.1 x.2 := by
    rw [ht.ext]
    · aesop
    · exact hs.attach.map fun x y hxy ↦ Subtype.ext <| i_inj _ x.2 _ y.2 hxy
  calc
    s.map f = s.pmap (fun x _ => f x) fun _ => id := by rw [pmap_eq_map]
    _ = s.attach.map fun x => f x.1 := by rw [pmap_eq_map_attach]
    _ = t.map g := by rw [this, Multiset.map_map]; exact map_congr rfl fun x _ => h _ _

end Multiset
