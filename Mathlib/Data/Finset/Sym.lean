/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Multiset.Sym

/-!
# Symmetric powers of a finset

This file defines the symmetric powers of a finset as `Finset (Sym α n)` and `Finset (Sym2 α)`.

## Main declarations

* `Finset.sym`: The symmetric power of a finset. `s.sym n` is all the multisets of cardinality `n`
  whose elements are in `s`.
* `Finset.sym2`: The symmetric square of a finset. `s.sym2` is all the pairs whose elements are in
  `s`.
* A `Fintype (Sym2 α)` instance that does not require `DecidableEq α`.

## TODO

`Finset.sym` forms a Galois connection between `Finset α` and `Finset (Sym α n)`. Similar for
`Finset.sym2`.
-/

namespace Finset

variable {α β : Type*}

/-- `s.sym2` is the finset of all unordered pairs of elements from `s`.
It is the image of `s ×ˢ s` under the quotient `α × α → Sym2 α`. -/
@[simps]
protected def sym2 (s : Finset α) : Finset (Sym2 α) := ⟨s.1.sym2, s.2.sym2⟩

section
variable {s t : Finset α} {a b : α}

theorem mk_mem_sym2_iff : s(a, b) ∈ s.sym2 ↔ a ∈ s ∧ b ∈ s := by
  rw [mem_mk, sym2_val, Multiset.mk_mem_sym2_iff, mem_mk, mem_mk]

@[simp]
theorem mem_sym2_iff {m : Sym2 α} : m ∈ s.sym2 ↔ ∀ a ∈ m, a ∈ s := by
  rw [mem_mk, sym2_val, Multiset.mem_sym2_iff]
  simp only [mem_val]

theorem sym2_cons (a : α) (s : Finset α) (ha : a ∉ s) :
    (s.cons a ha).sym2 = ((s.cons a ha).map <| Sym2.mkEmbedding a).disjUnion s.sym2 (by
      simp [Finset.disjoint_left, ha]) :=
  val_injective <| Multiset.sym2_cons _ _

theorem sym2_insert [DecidableEq α] (a : α) (s : Finset α) :
    (insert a s).sym2 = ((insert a s).image fun b => s(a, b)) ∪ s.sym2 := by
  obtain ha | ha := Decidable.em (a ∈ s)
  · simp only [insert_eq_of_mem ha, right_eq_union, image_subset_iff]
    aesop
  · simpa [map_eq_image] using sym2_cons a s ha

theorem sym2_map (f : α ↪ β) (s : Finset α) : (s.map f).sym2 = s.sym2.map (.sym2Map f) :=
  val_injective <| s.val.sym2_map _

theorem sym2_image [DecidableEq β] (f : α → β) (s : Finset α) :
    (s.image f).sym2 = s.sym2.image (Sym2.map f) := by
  apply val_injective
  dsimp [Finset.sym2]
  rw [← Multiset.dedup_sym2, Multiset.sym2_map]

instance _root_.Sym2.instFintype [Fintype α] : Fintype (Sym2 α) where
  elems := Finset.univ.sym2
  complete := fun x ↦ by rw [mem_sym2_iff]; exact (fun a _ ↦ mem_univ a)

-- Note(kmill): Using a default argument to make this simp lemma more general.
@[simp]
theorem sym2_univ [Fintype α] (inst : Fintype (Sym2 α) := Sym2.instFintype) :
    (univ : Finset α).sym2 = univ := by
  ext
  simp only [mem_sym2_iff, mem_univ, implies_true]

@[simp, mono]
theorem sym2_mono (h : s ⊆ t) : s.sym2 ⊆ t.sym2 := by
  rw [← val_le_iff, sym2_val, sym2_val]
  apply Multiset.sym2_mono
  rwa [val_le_iff]

theorem monotone_sym2 : Monotone (Finset.sym2 : Finset α → _) := fun _ _ => sym2_mono

theorem injective_sym2 : Function.Injective (Finset.sym2 : Finset α → _) := by
  intro s t h
  ext x
  simpa using congr(s(x, x) ∈ $h)

theorem strictMono_sym2 : StrictMono (Finset.sym2 : Finset α → _) :=
  monotone_sym2.strictMono_of_injective injective_sym2

theorem sym2_toFinset [DecidableEq α] (m : Multiset α) :
    m.toFinset.sym2 = m.sym2.toFinset := by
  ext z
  refine z.ind fun x y ↦ ?_
  simp only [mk_mem_sym2_iff, Multiset.mem_toFinset, Multiset.mk_mem_sym2_iff]

@[simp]
theorem sym2_empty : (∅ : Finset α).sym2 = ∅ := rfl

@[simp]
theorem sym2_eq_empty : s.sym2 = ∅ ↔ s = ∅ := by
  rw [← val_eq_zero, sym2_val, Multiset.sym2_eq_zero_iff, val_eq_zero]

@[simp]
theorem sym2_nonempty : s.sym2.Nonempty ↔ s.Nonempty := by
  rw [← not_iff_not]
  simp_rw [not_nonempty_iff_eq_empty, sym2_eq_empty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.sym2⟩ := sym2_nonempty

@[simp]
theorem sym2_singleton (a : α) : ({a} : Finset α).sym2 = {Sym2.diag a} := rfl

/-- Finset **stars and bars** for the case `n = 2`. -/
theorem card_sym2 (s : Finset α) : s.sym2.card = Nat.choose (s.card + 1) 2 := by
  rw [card_def, sym2_val, Multiset.card_sym2, ← card_def]

end

variable {s t : Finset α} {a b : α}

section
variable [DecidableEq α]

theorem sym2_eq_image : s.sym2 = (s ×ˢ s).image Sym2.mk := by
  ext z
  refine z.ind fun x y ↦ ?_
  rw [mk_mem_sym2_iff, mem_image]
  constructor
  · intro h
    use (x, y)
    simp only [mem_product, h, and_self, true_and]
  · rintro ⟨⟨a, b⟩, h⟩
    simp only [mem_product, Sym2.eq_iff] at h
    obtain ⟨h, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := h
      <;> simp [h]

theorem isDiag_mk_of_mem_diag {a : α × α} (h : a ∈ s.diag) : (Sym2.mk a).IsDiag :=
  (Sym2.isDiag_iff_proj_eq _).2 (mem_diag.1 h).2

theorem not_isDiag_mk_of_mem_offDiag {a : α × α} (h : a ∈ s.offDiag) :
    ¬ (Sym2.mk a).IsDiag := by
  rw [Sym2.isDiag_iff_proj_eq]
  exact (mem_offDiag.1 h).2.2

end

section Sym2

variable {m : Sym2 α}

@[simp]
theorem diag_mem_sym2_mem_iff : (∀ b, b ∈ Sym2.diag a → b ∈ s) ↔ a ∈ s := by
  rw [← mem_sym2_iff]
  exact mk_mem_sym2_iff.trans <| and_self_iff

theorem diag_mem_sym2_iff : Sym2.diag a ∈ s.sym2 ↔ a ∈ s := by simp [diag_mem_sym2_mem_iff]

theorem image_diag_union_image_offDiag [DecidableEq α] :
    s.diag.image Sym2.mk ∪ s.offDiag.image Sym2.mk = s.sym2 := by
  rw [← image_union, diag_union_offDiag, sym2_eq_image]

end Sym2

section Sym

variable [DecidableEq α] {n : ℕ}

/-- Lifts a finset to `Sym α n`. `s.sym n` is the finset of all unordered tuples of cardinality `n`
with elements in `s`. -/
protected def sym (s : Finset α) : ∀ n, Finset (Sym α n)
  | 0 => {∅}
  | n + 1 => s.sup fun a ↦ Finset.image (Sym.cons a) (s.sym n)

@[simp]
theorem sym_zero : s.sym 0 = {∅} := rfl

@[simp]
theorem sym_succ : s.sym (n + 1) = s.sup fun a ↦ (s.sym n).image <| Sym.cons a := rfl

@[simp]
theorem mem_sym_iff {m : Sym α n} : m ∈ s.sym n ↔ ∀ a ∈ m, a ∈ s := by
  induction' n with n ih
  · refine mem_singleton.trans ⟨?_, fun _ ↦ Sym.eq_nil_of_card_zero _⟩
    rintro rfl
    exact fun a ha ↦ (Finset.notMem_empty _ ha).elim
  refine mem_sup.trans ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨a, ha, he⟩ b hb
    rw [mem_image] at he
    obtain ⟨m, he, rfl⟩ := he
    rw [Sym.mem_cons] at hb
    obtain rfl | hb := hb
    · exact ha
    · exact ih.1 he _ hb
  · obtain ⟨a, m, rfl⟩ := m.exists_eq_cons_of_succ
    exact
      ⟨a, h _ <| Sym.mem_cons_self _ _,
        mem_image_of_mem _ <| ih.2 fun b hb ↦ h _ <| Sym.mem_cons_of_mem hb⟩

@[simp]
theorem sym_empty (n : ℕ) : (∅ : Finset α).sym (n + 1) = ∅ := rfl

theorem replicate_mem_sym (ha : a ∈ s) (n : ℕ) : Sym.replicate n a ∈ s.sym n :=
  mem_sym_iff.2 fun b hb ↦ by rwa [(Sym.mem_replicate.1 hb).2]

protected theorem Nonempty.sym (h : s.Nonempty) (n : ℕ) : (s.sym n).Nonempty :=
  let ⟨_a, ha⟩ := h
  ⟨_, replicate_mem_sym ha n⟩

@[simp]
theorem sym_singleton (a : α) (n : ℕ) : ({a} : Finset α).sym n = {Sym.replicate n a} :=
  eq_singleton_iff_unique_mem.2
    ⟨replicate_mem_sym (mem_singleton.2 rfl) _, fun _s hs ↦
      Sym.eq_replicate_iff.2 fun _b hb ↦ eq_of_mem_singleton <| mem_sym_iff.1 hs _ hb⟩

theorem eq_empty_of_sym_eq_empty (h : s.sym n = ∅) : s = ∅ := by
  rw [← not_nonempty_iff_eq_empty] at h ⊢
  exact fun hs ↦ h (hs.sym _)

@[simp]
theorem sym_eq_empty : s.sym n = ∅ ↔ n ≠ 0 ∧ s = ∅ := by
  cases n
  · exact iff_of_false (singleton_ne_empty _) fun h ↦ (h.1 rfl).elim
  · refine ⟨fun h ↦ ⟨Nat.succ_ne_zero _, eq_empty_of_sym_eq_empty h⟩, ?_⟩
    rintro ⟨_, rfl⟩
    exact sym_empty _

@[simp]
theorem sym_nonempty : (s.sym n).Nonempty ↔ n = 0 ∨ s.Nonempty := by
  simp only [nonempty_iff_ne_empty, ne_eq, sym_eq_empty, not_and_or, not_ne_iff]

@[simp]
theorem sym_univ [Fintype α] (n : ℕ) : (univ : Finset α).sym n = univ :=
  eq_univ_iff_forall.2 fun _s ↦ mem_sym_iff.2 fun _a _ ↦ mem_univ _

@[simp]
theorem sym_mono (h : s ⊆ t) (n : ℕ) : s.sym n ⊆ t.sym n := fun _m hm ↦
  mem_sym_iff.2 fun _a ha ↦ h <| mem_sym_iff.1 hm _ ha

@[simp]
theorem sym_inter (s t : Finset α) (n : ℕ) : (s ∩ t).sym n = s.sym n ∩ t.sym n := by
  ext m
  simp only [mem_inter, mem_sym_iff, imp_and, forall_and]

@[simp]
theorem sym_union (s t : Finset α) (n : ℕ) : s.sym n ∪ t.sym n ⊆ (s ∪ t).sym n :=
  union_subset (sym_mono subset_union_left n) (sym_mono subset_union_right n)

theorem sym_fill_mem (a : α) {i : Fin (n + 1)} {m : Sym α (n - i)} (h : m ∈ s.sym (n - i)) :
    m.fill a i ∈ (insert a s).sym n :=
  mem_sym_iff.2 fun b hb ↦
    mem_insert.2 <| (Sym.mem_fill_iff.1 hb).imp And.right <| mem_sym_iff.1 h b

theorem sym_filterNe_mem {m : Sym α n} (a : α) (h : m ∈ s.sym n) :
    (m.filterNe a).2 ∈ (Finset.erase s a).sym (n - (m.filterNe a).1) :=
  mem_sym_iff.2 fun b H ↦
    mem_erase.2 <| (Multiset.mem_filter.1 H).symm.imp Ne.symm <| mem_sym_iff.1 h b

/-- If `a` does not belong to the finset `s`, then the `n`th symmetric power of `{a} ∪ s` is
  in 1-1 correspondence with the disjoint union of the `n - i`th symmetric powers of `s`,
  for `0 ≤ i ≤ n`. -/
@[simps]
def symInsertEquiv (h : a ∉ s) : (insert a s).sym n ≃ Σi : Fin (n + 1), s.sym (n - i) where
  toFun m := ⟨_, (m.1.filterNe a).2, by convert sym_filterNe_mem a m.2; rw [erase_insert h]⟩
  invFun m := ⟨m.2.1.fill a m.1, sym_fill_mem a m.2.2⟩
  left_inv m := Subtype.ext <| m.1.fill_filterNe a
  right_inv := fun ⟨i, m, hm⟩ ↦ by
    refine Function.Injective.sigma_map (β₂ := ?_) (f₂ := ?_)
        (Function.injective_id) (fun i ↦ ?_) ?_
    · exact fun i ↦ Sym α (n - i)
    swap
    · exact Subtype.coe_injective
    refine Eq.trans ?_ (Sym.filter_ne_fill a _ ?_)
    exacts [rfl, h ∘ mem_sym_iff.1 hm a]

end Sym

end Finset
