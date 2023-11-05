/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

[`data.finset.sym`@`98e83c3d541c77cdb7da20d79611a780ff8e7d90`..`02ba8949f486ebecf93fe7460f1ed0564b5e442c`](https://leanprover-community.github.io/mathlib-port-status/file/data/finset/sym?range=98e83c3d541c77cdb7da20d79611a780ff8e7d90..02ba8949f486ebecf93fe7460f1ed0564b5e442c)
-/
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Sym.Sym2

#align_import data.finset.sym from "leanprover-community/mathlib"@"02ba8949f486ebecf93fe7460f1ed0564b5e442c"

/-!
# Symmetric powers of a finset

This file defines the symmetric powers of a finset as `Finset (Sym α n)` and `Finset (Sym2 α)`.

## Main declarations

* `Finset.sym`: The symmetric power of a finset. `s.sym n` is all the multisets of cardinality `n`
  whose elements are in `s`.
* `Finset.sym2`: The symmetric square of a finset. `s.sym2` is all the pairs whose elements are in
  `s`.
* A `Finset (Sym2 α)` instance that does not require `DecidableEq α`.

## TODO

`Finset.sym` forms a Galois connection between `Finset α` and `Finset (Sym α n)`. Similar for
`Finset.sym2`.
-/

namespace List

variable {α : Type*}

/-- `xs.sym2` is a list of all unordered pairs of elements from `xs`.
If `xs` has no duplicates then neither does `xs.sym2`. -/
protected def sym2 : List α → List (Sym2 α)
  | [] => []
  | x::xs => ((x::xs).map fun y => Quotient.mk _ (x, y)) ++ xs.sym2

theorem left_mem_of_mem_sym2 {xs : List α} {a b : α}
    (h : Quotient.mk _ (a, b) ∈ xs.sym2) : a ∈ xs := by
  induction xs generalizing a b with
  | nil => exact (not_mem_nil _ h).elim
  | cons x xs ih =>
    rw [mem_cons]
    simp only [List.sym2, map_cons, cons_append, mem_cons, mem_append, mem_map] at h
    obtain (h | h) := h
    · rw [Sym2.eq_iff, ← and_or_left] at h
      left; exact h.1
    · obtain (⟨c, hc, h⟩ | h) := h
      · rw [Sym2.eq_iff] at h
        obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := h
        · left; rfl
        · right; exact hc
      · right; exact ih h

theorem right_mem_of_mem_sym2 {xs : List α} {a b : α}
    (h : Quotient.mk _ (a, b) ∈ xs.sym2) : b ∈ xs := by
  rw [Sym2.eq_swap] at h
  exact left_mem_of_mem_sym2 h

theorem mem_sym2 {xs : List α} {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) :
    Quotient.mk _ (a, b) ∈ xs.sym2 := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.sym2, List.map_cons]
    rw [mem_cons] at ha hb
    obtain (rfl | ha) := ha <;> obtain (rfl | hb) := hb
    · apply List.mem_append_left
      apply List.mem_cons_self
    · apply List.mem_append_left
      apply List.mem_cons_of_mem
      rw [List.mem_map]
      use b
    · apply List.mem_append_left
      apply List.mem_cons_of_mem
      rw [Sym2.eq_swap, List.mem_map]
      use a
    · apply List.mem_append_right
      exact ih ha hb

theorem mk_mem_sym2_iff {xs : List α} {a b : α} :
    Quotient.mk _ (a, b) ∈ xs.sym2 ↔ a ∈ xs ∧ b ∈ xs := by
  constructor
  · intro h
    exact ⟨left_mem_of_mem_sym2 h, right_mem_of_mem_sym2 h⟩
  · rintro ⟨ha, hb⟩
    exact mem_sym2 ha hb

protected theorem Nodup.sym2 {xs : List α} (h : xs.Nodup) : xs.sym2.Nodup := by
  induction xs with
  | nil => simp [List.sym2]
  | cons x xs ih =>
    rw [List.sym2, List.map]
    have := ih (Nodup.of_cons h)
    rw [nodup_cons] at h
    apply Nodup.append _ this
    · intro z hz hz'
      simp only [mem_cons, mem_map] at hz
      obtain (rfl | ⟨_, _, rfl⟩) := hz
        <;> simp [left_mem_of_mem_sym2 hz'] at h
    apply Nodup.cons
    · intro h'
      simp only [mem_map, Sym2.eq_iff, true_and, or_self, exists_eq_right] at h'
      simp [h'] at h
    apply Nodup.map
    · intro a b
      simp only [Sym2.eq_iff, true_and]
      rintro (rfl | ⟨rfl, rfl⟩) <;> rfl
    · exact h.2

protected theorem Perm.sym2 {xs ys : List α} (h : xs ~ ys) :
    xs.sym2 ~ ys.sym2 := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    simp only [List.sym2, map_cons, cons_append, perm_cons]
    exact (h.map _).append ih
  | swap x y xs =>
    simp only [List.sym2, map_cons, cons_append]
    refine Perm.trans (Perm.swap ..) (Perm.trans ?_ (Perm.swap ..))
    rw [Sym2.eq_swap]
    apply Perm.cons
    simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe,
      ← Multiset.coe_add, ← Multiset.singleton_add]
    simp only [add_assoc, add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

@[simp]
theorem sym2_eq_nil {xs : List α} : xs.sym2 = [] ↔ xs = [] := by
  cases xs <;> simp [List.sym2]

end List

namespace Multiset

variable {α : Type*}

/-- `m.sym2` is the multiset of all unordered pairs of elements from `m`, with multiplicity.
If `m` has no duplicates then neither does `m.sym2`. -/
protected def sym2 (m : Multiset α) : Multiset (Sym2 α) :=
  m.liftOn (fun xs => xs.sym2) fun _ _ h => by rw [coe_eq_coe]; exact h.sym2

@[simp] theorem sym2_coe (xs : List α) : (xs : Multiset α).sym2 = xs.sym2 := rfl

theorem mk_mem_sym2_iff {m : Multiset α} {a b : α} :
    Quotient.mk _ (a, b) ∈ m.sym2 ↔ a ∈ m ∧ b ∈ m :=
  m.recOnSubsingleton fun xs => by simp [List.mk_mem_sym2_iff]

protected theorem Nodup.sym2 {m : Multiset α} (h : m.Nodup) : m.sym2.Nodup :=
  Quotient.recOnSubsingleton m (fun _ h => List.Nodup.sym2 h) h

@[simp]
theorem sym2_eq_zero {m : Multiset α} : m.sym2 = 0 ↔ m = 0 :=
  m.recOnSubsingleton fun xs => by simp

end Multiset

namespace Finset

variable {α : Type*}

/-- `s.sym2` is the finset of all unordered pairs of elements from `s`.
It is image of `s ×ˢ s` under the quotient `α × α → Sym2 α`. -/
@[simps]
protected def sym2 (s : Finset α) : Finset (Sym2 α) := ⟨s.1.sym2, s.2.sym2⟩
#align finset.sym2 Finset.sym2

section
variable {s t : Finset α} {a b : α}

theorem mk_mem_sym2_iff : ⟦(a, b)⟧ ∈ s.sym2 ↔ a ∈ s ∧ b ∈ s := by
  rw [Finset.sym2, ← Finset.mem_coe]
  simp only [mem_coe, mem_mk, Multiset.mk_mem_sym2_iff, mem_val]
#align finset.mk_mem_sym2_iff Finset.mk_mem_sym2_iff

@[simp]
theorem mem_sym2_iff {m : Sym2 α} : m ∈ s.sym2 ↔ ∀ a ∈ m, a ∈ s := by
  refine Quotient.recOnSubsingleton m ?_
  rintro ⟨x, y⟩
  rw [mk_mem_sym2_iff]
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
#align finset.mem_sym2_iff Finset.mem_sym2_iff

instance instFintypeSym2 [Fintype α] : Fintype (Sym2 α) where
  elems := Finset.univ.sym2
  complete := by simp

theorem sym2_toFinset [DecidableEq α] (m : Multiset α) :
    m.toFinset.sym2 = m.sym2.toFinset := by
  ext z
  refine z.recOnSubsingleton ?_
  rintro ⟨x, y⟩
  simp only [mk_mem_sym2_iff, Multiset.mem_toFinset, Multiset.mk_mem_sym2_iff]

@[simp]
theorem sym2_empty : (∅ : Finset α).sym2 = ∅ := rfl
#align finset.sym2_empty Finset.sym2_empty

@[simp]
theorem sym2_eq_empty : s.sym2 = ∅ ↔ s = ∅ := by
  classical
  rw [← Finset.val_toFinset s, sym2_toFinset]
  simp
#align finset.sym2_eq_empty Finset.sym2_eq_empty

@[simp]
theorem sym2_nonempty : s.sym2.Nonempty ↔ s.Nonempty := by
  rw [← not_iff_not]
  simp only [not_nonempty_iff_eq_empty, sym2_eq_empty]
#align finset.sym2_nonempty Finset.sym2_nonempty

alias ⟨_, Nonempty.sym2⟩ := sym2_nonempty
#align finset.nonempty.sym2 Finset.Nonempty.sym2

-- Porting note: attribute does not exist
-- attribute [protected] Nonempty.sym2

-- Note(kmill): Using a default argument to make this simp lemma more general.
@[simp]
theorem sym2_univ [Fintype α] (inst : Fintype (Sym2 α) := instFintypeSym2) :
    (univ : Finset α).sym2 = univ := by
  ext
  simp only [mem_sym2_iff, mem_univ, implies_true]
#align finset.sym2_univ Finset.sym2_univ

@[simp]
theorem sym2_singleton (a : α) : ({a} : Finset α).sym2 = {Sym2.diag a} := rfl
#align finset.sym2_singleton Finset.sym2_singleton

@[simp]
theorem sym2_mono (h : s ⊆ t) : s.sym2 ⊆ t.sym2 := fun _m he ↦
  mem_sym2_iff.2 fun _a ha ↦ h <| mem_sym2_iff.1 he _ ha
#align finset.sym2_mono Finset.sym2_mono

end

variable [DecidableEq α] {s t : Finset α} {a b : α}

theorem sym2_eq_image : s.sym2 = (s ×ˢ s).image (Quotient.mk _) := by
  ext z
  refine Quotient.recOnSubsingleton z ?_
  rintro ⟨x, y⟩
  rw [mk_mem_sym2_iff, mem_image]
  constructor
  · intro h
    use (x, y)
    simp only [mem_product, h, and_self, true_and]
  · rintro ⟨⟨a, b⟩, h⟩
    simp only [mem_product, Sym2.eq_iff] at h
    obtain ⟨h, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := h
      <;> simp [h]

theorem isDiag_mk_of_mem_diag {a : α × α} (h : a ∈ s.diag) : Sym2.IsDiag ⟦a⟧ :=
  (Sym2.isDiag_iff_proj_eq _).2 (mem_diag.1 h).2
#align finset.is_diag_mk_of_mem_diag Finset.isDiag_mk_of_mem_diag

theorem not_isDiag_mk_of_mem_offDiag {a : α × α} (h : a ∈ s.offDiag) : ¬Sym2.IsDiag ⟦a⟧ := by
  rw [Sym2.isDiag_iff_proj_eq]
  exact (mem_offDiag.1 h).2.2
#align finset.not_is_diag_mk_of_mem_off_diag Finset.not_isDiag_mk_of_mem_offDiag

section Sym2

variable {m : Sym2 α}

-- Porting note: add this lemma and remove simp in the next lemma since simpNF lint
-- warns that its LHS is not in normal form
@[simp]
theorem diag_mem_sym2_mem_iff : (∀ b, b ∈ Sym2.diag a → b ∈ s) ↔ a ∈ s := by
  rw [← mem_sym2_iff]
  exact mk_mem_sym2_iff.trans <| and_self_iff

theorem diag_mem_sym2_iff : Sym2.diag a ∈ s.sym2 ↔ a ∈ s := by simp [diag_mem_sym2_mem_iff]
#align finset.diag_mem_sym2_iff Finset.diag_mem_sym2_iff

theorem image_diag_union_image_offDiag :
    s.diag.image (Quotient.mk _) ∪ s.offDiag.image (Quotient.mk _) = s.sym2 := by
  rw [← image_union, diag_union_offDiag, sym2_eq_image]
#align finset.image_diag_union_image_off_diag Finset.image_diag_union_image_offDiag

end Sym2

section Sym

variable {n : ℕ} {m : Sym α n}

-- Porting note: instance needed
instance : DecidableEq (Sym α n) := Subtype.instDecidableEqSubtype

/-- Lifts a finset to `Sym α n`. `s.sym n` is the finset of all unordered tuples of cardinality `n`
with elements in `s`. -/
protected def sym (s : Finset α) : ∀ n, Finset (Sym α n)
  | 0 => {∅}
  | n + 1 => s.sup fun a ↦ Finset.image (Sym.cons a) (s.sym n)
#align finset.sym Finset.sym

@[simp]
theorem sym_zero : s.sym 0 = {∅} := rfl
#align finset.sym_zero Finset.sym_zero

@[simp]
theorem sym_succ : s.sym (n + 1) = s.sup fun a ↦ (s.sym n).image <| Sym.cons a := rfl
#align finset.sym_succ Finset.sym_succ

@[simp]
theorem mem_sym_iff : m ∈ s.sym n ↔ ∀ a ∈ m, a ∈ s := by
  induction' n with n ih
  · refine' mem_singleton.trans ⟨_, fun _ ↦ Sym.eq_nil_of_card_zero _⟩
    rintro rfl
    exact fun a ha ↦ (Finset.not_mem_empty _ ha).elim
  refine' mem_sup.trans ⟨_, fun h ↦ _⟩
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
#align finset.mem_sym_iff Finset.mem_sym_iff

@[simp]
theorem sym_empty (n : ℕ) : (∅ : Finset α).sym (n + 1) = ∅ := rfl
#align finset.sym_empty Finset.sym_empty

theorem replicate_mem_sym (ha : a ∈ s) (n : ℕ) : Sym.replicate n a ∈ s.sym n :=
  mem_sym_iff.2 fun b hb ↦ by rwa [(Sym.mem_replicate.1 hb).2]
#align finset.replicate_mem_sym Finset.replicate_mem_sym

protected theorem Nonempty.sym (h : s.Nonempty) (n : ℕ) : (s.sym n).Nonempty :=
  let ⟨_a, ha⟩ := h
  ⟨_, replicate_mem_sym ha n⟩
#align finset.nonempty.sym Finset.Nonempty.sym

@[simp]
theorem sym_singleton (a : α) (n : ℕ) : ({a} : Finset α).sym n = {Sym.replicate n a} :=
  eq_singleton_iff_unique_mem.2
    ⟨replicate_mem_sym (mem_singleton.2 rfl) _, fun _s hs ↦
      Sym.eq_replicate_iff.2 fun _b hb ↦ eq_of_mem_singleton <| mem_sym_iff.1 hs _ hb⟩
#align finset.sym_singleton Finset.sym_singleton

theorem eq_empty_of_sym_eq_empty (h : s.sym n = ∅) : s = ∅ := by
  rw [← not_nonempty_iff_eq_empty] at h ⊢
  exact fun hs ↦ h (hs.sym _)
#align finset.eq_empty_of_sym_eq_empty Finset.eq_empty_of_sym_eq_empty

@[simp]
theorem sym_eq_empty : s.sym n = ∅ ↔ n ≠ 0 ∧ s = ∅ := by
  cases n
  · exact iff_of_false (singleton_ne_empty _) fun h ↦ (h.1 rfl).elim
  · refine ⟨fun h ↦ ⟨Nat.succ_ne_zero _, eq_empty_of_sym_eq_empty h⟩, ?_⟩
    rintro ⟨_, rfl⟩
    exact sym_empty _
#align finset.sym_eq_empty Finset.sym_eq_empty

@[simp]
theorem sym_nonempty : (s.sym n).Nonempty ↔ n = 0 ∨ s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, Ne.def]
-- Porting note: using simp_rw does not work here, it does nothing...
  rwa [sym_eq_empty, not_and_or, not_ne_iff]
#align finset.sym_nonempty Finset.sym_nonempty

@[simp]
theorem sym_univ [Fintype α] (n : ℕ) : (univ : Finset α).sym n = univ :=
  eq_univ_iff_forall.2 fun _s ↦ mem_sym_iff.2 fun _a _ ↦ mem_univ _
#align finset.sym_univ Finset.sym_univ

@[simp]
theorem sym_mono (h : s ⊆ t) (n : ℕ) : s.sym n ⊆ t.sym n := fun _m hm ↦
  mem_sym_iff.2 fun _a ha ↦ h <| mem_sym_iff.1 hm _ ha
#align finset.sym_mono Finset.sym_mono

@[simp]
theorem sym_inter (s t : Finset α) (n : ℕ) : (s ∩ t).sym n = s.sym n ∩ t.sym n := by
  ext m
  simp only [mem_inter, mem_sym_iff, imp_and, forall_and]
#align finset.sym_inter Finset.sym_inter

@[simp]
theorem sym_union (s t : Finset α) (n : ℕ) : s.sym n ∪ t.sym n ⊆ (s ∪ t).sym n :=
  union_subset (sym_mono (subset_union_left s t) n) (sym_mono (subset_union_right s t) n)
#align finset.sym_union Finset.sym_union

theorem sym_fill_mem (a : α) {i : Fin (n + 1)} {m : Sym α (n - i)} (h : m ∈ s.sym (n - i)) :
    m.fill a i ∈ (insert a s).sym n :=
  mem_sym_iff.2 fun b hb ↦
    mem_insert.2 <| (Sym.mem_fill_iff.1 hb).imp And.right <| mem_sym_iff.1 h b
#align finset.sym_fill_mem Finset.sym_fill_mem

theorem sym_filterNe_mem (a : α) (h : m ∈ s.sym n) :
    (m.filterNe a).2 ∈ (Finset.erase s a).sym (n - (m.filterNe a).1) :=
  mem_sym_iff.2 fun b H ↦
    mem_erase.2 <| (Multiset.mem_filter.1 H).symm.imp Ne.symm <| mem_sym_iff.1 h b
#align finset.sym_filter_ne_mem Finset.sym_filterNe_mem

/-- If `a` does not belong to the finset `s`, then the `n`th symmetric power of `{a} ∪ s` is
  in 1-1 correspondence with the disjoint union of the `n - i`th symmetric powers of `s`,
  for `0 ≤ i ≤ n`. -/
@[simps]
def symInsertEquiv (h : a ∉ s) : (insert a s).sym n ≃ Σi : Fin (n + 1), s.sym (n - i)
    where
  toFun m := ⟨_, (m.1.filterNe a).2, by convert sym_filterNe_mem a m.2; rw [erase_insert h]⟩
  invFun m := ⟨m.2.1.fill a m.1, sym_fill_mem a m.2.2⟩
  left_inv m := Subtype.ext <| m.1.fill_filterNe a
  right_inv := fun ⟨i, m, hm⟩ ↦ by
    refine' Function.Injective.sigma_map (Function.injective_id) (fun i ↦ _) _
    exact fun i ↦ Sym α (n - i)
    swap; exact Subtype.coe_injective
    refine Eq.trans ?_ (Sym.filter_ne_fill a _ ?_)
    exacts [rfl, h ∘ mem_sym_iff.1 hm a]
#align finset.sym_insert_equiv Finset.symInsertEquiv

end Sym

end Finset
