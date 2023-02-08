/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finset.sym
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Lattice
import Mathbin.Data.Fintype.Prod
import Mathbin.Data.Fintype.Vector
import Mathbin.Data.Sym.Sym2

/-!
# Symmetric powers of a finset

This file defines the symmetric powers of a finset as `finset (sym α n)` and `finset (sym2 α)`.

## Main declarations

* `finset.sym`: The symmetric power of a finset. `s.sym n` is all the multisets of cardinality `n`
  whose elements are in `s`.
* `finset.sym2`: The symmetric square of a finset. `s.sym2` is all the pairs whose elements are in
  `s`.

## TODO

`finset.sym` forms a Galois connection between `finset α` and `finset (sym α n)`. Similar for
`finset.sym2`.
-/


namespace Finset

variable {α : Type _} [DecidableEq α] {s t : Finset α} {a b : α}

theorem isDiag_mk'_of_mem_diag {a : α × α} (h : a ∈ s.diag) : Sym2.IsDiag ⟦a⟧ :=
  (Sym2.isDiag_iff_proj_eq _).2 (mem_diag.1 h).2
#align finset.is_diag_mk_of_mem_diag Finset.isDiag_mk'_of_mem_diag

theorem not_isDiag_mk'_of_mem_offDiag {a : α × α} (h : a ∈ s.offDiag) : ¬Sym2.IsDiag ⟦a⟧ :=
  by
  rw [Sym2.isDiag_iff_proj_eq]
  exact (mem_off_diag.1 h).2.2
#align finset.not_is_diag_mk_of_mem_off_diag Finset.not_isDiag_mk'_of_mem_offDiag

section Sym2

variable {m : Sym2 α}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Lifts a finset to `sym2 α`. `s.sym2` is the finset of all pairs with elements in `s`. -/
protected def sym2 (s : Finset α) : Finset (Sym2 α) :=
  (s ×ˢ s).image Quotient.mk'
#align finset.sym2 Finset.sym2

@[simp]
theorem mem_sym2_iff : m ∈ s.Sym2 ↔ ∀ a ∈ m, a ∈ s :=
  by
  refine'
    mem_image.trans
      ⟨_, fun h => ⟨m.out, mem_product.2 ⟨h _ m.out_fst_mem, h _ m.out_snd_mem⟩, m.out_eq⟩⟩
  rintro ⟨⟨a, b⟩, h, rfl⟩
  rw [Sym2.ball]
  rwa [mem_product] at h
#align finset.mem_sym2_iff Finset.mem_sym2_iff

theorem mk'_mem_sym2_iff : ⟦(a, b)⟧ ∈ s.Sym2 ↔ a ∈ s ∧ b ∈ s := by rw [mem_sym2_iff, Sym2.ball]
#align finset.mk_mem_sym2_iff Finset.mk'_mem_sym2_iff

@[simp]
theorem sym2_empty : (∅ : Finset α).Sym2 = ∅ :=
  rfl
#align finset.sym2_empty Finset.sym2_empty

@[simp]
theorem sym2_eq_empty : s.Sym2 = ∅ ↔ s = ∅ := by
  rw [Finset.sym2, image_eq_empty, product_eq_empty, or_self_iff]
#align finset.sym2_eq_empty Finset.sym2_eq_empty

@[simp]
theorem sym2_nonempty : s.Sym2.Nonempty ↔ s.Nonempty := by
  rw [Finset.sym2, nonempty.image_iff, nonempty_product, and_self_iff]
#align finset.sym2_nonempty Finset.sym2_nonempty

alias sym2_nonempty ↔ _ nonempty.sym2
#align finset.nonempty.sym2 Finset.Nonempty.sym2

attribute [protected] nonempty.sym2

@[simp]
theorem sym2_univ [Fintype α] : (univ : Finset α).Sym2 = univ :=
  rfl
#align finset.sym2_univ Finset.sym2_univ

@[simp]
theorem sym2_singleton (a : α) : ({a} : Finset α).Sym2 = {Sym2.diag a} := by
  rw [Finset.sym2, singleton_product_singleton, image_singleton, Sym2.diag]
#align finset.sym2_singleton Finset.sym2_singleton

@[simp]
theorem diag_mem_sym2_iff : Sym2.diag a ∈ s.Sym2 ↔ a ∈ s :=
  mk'_mem_sym2_iff.trans <| and_self_iff _
#align finset.diag_mem_sym2_iff Finset.diag_mem_sym2_iff

@[simp]
theorem sym2_mono (h : s ⊆ t) : s.Sym2 ⊆ t.Sym2 := fun m he =>
  mem_sym2_iff.2 fun a ha => h <| mem_sym2_iff.1 he _ ha
#align finset.sym2_mono Finset.sym2_mono

theorem image_diag_union_image_offDiag :
    s.diag.image Quotient.mk' ∪ s.offDiag.image Quotient.mk' = s.Sym2 :=
  by
  rw [← image_union, diag_union_off_diag]
  rfl
#align finset.image_diag_union_image_off_diag Finset.image_diag_union_image_offDiag

end Sym2

section Sym

variable {n : ℕ} {m : Sym α n}

/-- Lifts a finset to `sym α n`. `s.sym n` is the finset of all unordered tuples of cardinality `n`
with elements in `s`. -/
protected def sym (s : Finset α) : ∀ n, Finset (Sym α n)
  | 0 => {∅}
  | n + 1 => s.sup fun a => (Sym n).image <| Sym.cons a
#align finset.sym Finset.sym

@[simp]
theorem sym_zero : s.Sym 0 = {∅} :=
  rfl
#align finset.sym_zero Finset.sym_zero

@[simp]
theorem sym_succ : s.Sym (n + 1) = s.sup fun a => (s.Sym n).image <| Sym.cons a :=
  rfl
#align finset.sym_succ Finset.sym_succ

@[simp]
theorem mem_sym_iff : m ∈ s.Sym n ↔ ∀ a ∈ m, a ∈ s :=
  by
  induction' n with n ih
  · refine' mem_singleton.trans ⟨_, fun _ => Sym.eq_nil_of_card_zero _⟩
    rintro rfl
    exact fun a ha => ha.elim
  refine' mem_sup.trans ⟨_, fun h => _⟩
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
        mem_image_of_mem _ <| ih.2 fun b hb => h _ <| Sym.mem_cons_of_mem hb⟩
#align finset.mem_sym_iff Finset.mem_sym_iff

@[simp]
theorem sym_empty (n : ℕ) : (∅ : Finset α).Sym (n + 1) = ∅ :=
  rfl
#align finset.sym_empty Finset.sym_empty

theorem replicate_mem_sym (ha : a ∈ s) (n : ℕ) : Sym.replicate n a ∈ s.Sym n :=
  mem_sym_iff.2 fun b hb => by rwa [(Sym.mem_replicate.1 hb).2]
#align finset.replicate_mem_sym Finset.replicate_mem_sym

protected theorem Nonempty.sym (h : s.Nonempty) (n : ℕ) : (s.Sym n).Nonempty :=
  let ⟨a, ha⟩ := h
  ⟨_, replicate_mem_sym ha n⟩
#align finset.nonempty.sym Finset.Nonempty.sym

@[simp]
theorem sym_singleton (a : α) (n : ℕ) : ({a} : Finset α).Sym n = {Sym.replicate n a} :=
  eq_singleton_iff_unique_mem.2
    ⟨replicate_mem_sym (mem_singleton.2 rfl) _, fun s hs =>
      Sym.eq_replicate_iff.2 fun b hb => eq_of_mem_singleton <| mem_sym_iff.1 hs _ hb⟩
#align finset.sym_singleton Finset.sym_singleton

theorem eq_empty_of_sym_eq_empty (h : s.Sym n = ∅) : s = ∅ :=
  by
  rw [← not_nonempty_iff_eq_empty] at h⊢
  exact fun hs => h (hs.Sym _)
#align finset.eq_empty_of_sym_eq_empty Finset.eq_empty_of_sym_eq_empty

@[simp]
theorem sym_eq_empty : s.Sym n = ∅ ↔ n ≠ 0 ∧ s = ∅ :=
  by
  cases n
  · exact iff_of_false (singleton_ne_empty _) fun h => (h.1 rfl).elim
  · refine' ⟨fun h => ⟨n.succ_ne_zero, eq_empty_of_sym_eq_empty h⟩, _⟩
    rintro ⟨_, rfl⟩
    exact sym_empty _
#align finset.sym_eq_empty Finset.sym_eq_empty

@[simp]
theorem sym_nonempty : (s.Sym n).Nonempty ↔ n = 0 ∨ s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, Ne.def, sym_eq_empty, not_and_or, not_ne_iff]
#align finset.sym_nonempty Finset.sym_nonempty

alias sym2_nonempty ↔ _ nonempty.sym2
#align finset.nonempty.sym2 Finset.Nonempty.sym2

attribute [protected] nonempty.sym2

@[simp]
theorem sym_univ [Fintype α] (n : ℕ) : (univ : Finset α).Sym n = univ :=
  eq_univ_iff_forall.2 fun s => mem_sym_iff.2 fun a _ => mem_univ _
#align finset.sym_univ Finset.sym_univ

@[simp]
theorem sym_mono (h : s ⊆ t) (n : ℕ) : s.Sym n ⊆ t.Sym n := fun m hm =>
  mem_sym_iff.2 fun a ha => h <| mem_sym_iff.1 hm _ ha
#align finset.sym_mono Finset.sym_mono

@[simp]
theorem sym_inter (s t : Finset α) (n : ℕ) : (s ∩ t).Sym n = s.Sym n ∩ t.Sym n :=
  by
  ext m
  simp only [mem_inter, mem_sym_iff, imp_and, forall_and]
#align finset.sym_inter Finset.sym_inter

@[simp]
theorem sym_union (s t : Finset α) (n : ℕ) : s.Sym n ∪ t.Sym n ⊆ (s ∪ t).Sym n :=
  union_subset (sym_mono (subset_union_left s t) n) (sym_mono (subset_union_right s t) n)
#align finset.sym_union Finset.sym_union

theorem sym_fill_mem (a : α) {i : Fin (n + 1)} {m : Sym α (n - i)} (h : m ∈ s.Sym (n - i)) :
    m.fill a i ∈ (insert a s).Sym n :=
  mem_sym_iff.2 fun b hb =>
    mem_insert.2 <| (Sym.mem_fill_iff.1 hb).imp And.right <| mem_sym_iff.1 h b
#align finset.sym_fill_mem Finset.sym_fill_mem

theorem sym_filterNe_mem (a : α) (h : m ∈ s.Sym n) :
    (m.filter_ne a).2 ∈ (s.eraseₓ a).Sym (n - (m.filter_ne a).1) :=
  mem_sym_iff.2 fun b H =>
    mem_erase.2 <| (Multiset.mem_filter.1 H).symm.imp Ne.symm <| mem_sym_iff.1 h b
#align finset.sym_filter_ne_mem Finset.sym_filterNe_mem

/-- If `a` does not belong to the finset `s`, then the `n`th symmetric power of `{a} ∪ s` is
  in 1-1 correspondence with the disjoint union of the `n - i`th symmetric powers of `s`,
  for `0 ≤ i ≤ n`. -/
@[simps]
def symInsertEquiv (h : a ∉ s) : (insert a s).Sym n ≃ Σi : Fin (n + 1), s.Sym (n - i)
    where
  toFun m := ⟨_, (m.1.filter_ne a).2, by convert sym_filter_ne_mem a m.2 <;> rw [erase_insert h]⟩
  invFun m := ⟨m.2.1.fill a m.1, sym_fill_mem a m.2.2⟩
  left_inv m := Subtype.ext <| m.1.fill_filterNe a
  right_inv := fun ⟨i, m, hm⟩ =>
    by
    refine' (_ : id.injective).sigma_map (fun i => _) _
    · exact fun i => Sym α (n - i)
    swap; · exact fun _ _ => id
    swap; · exact Subtype.coe_injective
    refine' Eq.trans _ (Sym.filter_ne_fill a _ _)
    exacts[rfl, h ∘ mem_sym_iff.1 hm a]
#align finset.sym_insert_equiv Finset.symInsertEquiv

end Sym

end Finset

