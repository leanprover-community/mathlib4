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

## TODO

`Finset.sym` forms a Galois connection between `Finset α` and `Finset (Sym α n)`. Similar for
`Finset.sym2`.
-/

namespace Finset

variable {α : Type*} [DecidableEq α] {s t : Finset α} {a b : α}

theorem isDiag_mk'_of_mem_diag {a : α × α} (h : a ∈ s.diag) : Sym2.IsDiag ⟦a⟧ :=
  (Sym2.isDiag_iff_proj_eq _).2 (mem_diag.1 h).2
#align finset.is_diag_mk_of_mem_diag Finset.isDiag_mk'_of_mem_diag

theorem not_isDiag_mk'_of_mem_offDiag {a : α × α} (h : a ∈ s.offDiag) : ¬Sym2.IsDiag ⟦a⟧ := by
  rw [Sym2.isDiag_iff_proj_eq]
  -- ⊢ ¬a.fst = a.snd
  exact (mem_offDiag.1 h).2.2
  -- 🎉 no goals
#align finset.not_is_diag_mk_of_mem_off_diag Finset.not_isDiag_mk'_of_mem_offDiag

section Sym2

variable {m : Sym2 α}

/-- Lifts a finset to `Sym2 α`. `s.sym2` is the finset of all pairs with elements in `s`. -/
protected def sym2 (s : Finset α) : Finset (Sym2 α) := (s ×ˢ s).image Quotient.mk'
#align finset.sym2 Finset.sym2

@[simp]
theorem mem_sym2_iff : m ∈ s.sym2 ↔ ∀ a ∈ m, a ∈ s := by
  refine
    mem_image.trans
      ⟨?_, fun h ↦ ⟨m.out, mem_product.2 ⟨h _ m.out_fst_mem, h _ m.out_snd_mem⟩, m.out_eq⟩⟩
  rintro ⟨⟨a, b⟩, h, rfl⟩
  -- ⊢ ∀ (a_1 : α), a_1 ∈ Quotient.mk' (a, b) → a_1 ∈ s
  rw [Quotient.mk', @Sym2.ball _ (fun x ↦ x ∈ s)]
  -- ⊢ a ∈ s ∧ b ∈ s
  rwa [mem_product] at h
  -- 🎉 no goals
#align finset.mem_sym2_iff Finset.mem_sym2_iff

theorem mk'_mem_sym2_iff : ⟦(a, b)⟧ ∈ s.sym2 ↔ a ∈ s ∧ b ∈ s := by rw [mem_sym2_iff, Sym2.ball]
                                                                   -- 🎉 no goals
#align finset.mk_mem_sym2_iff Finset.mk'_mem_sym2_iff

@[simp]
theorem sym2_empty : (∅ : Finset α).sym2 = ∅ := rfl
#align finset.sym2_empty Finset.sym2_empty

@[simp]
theorem sym2_eq_empty : s.sym2 = ∅ ↔ s = ∅ := by
  rw [Finset.sym2, image_eq_empty, product_eq_empty, or_self_iff]
  -- 🎉 no goals
#align finset.sym2_eq_empty Finset.sym2_eq_empty

@[simp]
theorem sym2_nonempty : s.sym2.Nonempty ↔ s.Nonempty := by
  rw [Finset.sym2, Nonempty.image_iff, nonempty_product, and_self_iff]
  -- 🎉 no goals
#align finset.sym2_nonempty Finset.sym2_nonempty

alias ⟨_, nonempty.sym2⟩ := sym2_nonempty
#align finset.nonempty.sym2 Finset.nonempty.sym2

-- Porting note: attribute does not exist
-- attribute [protected] nonempty.sym2

@[simp]
theorem sym2_univ [Fintype α] : (univ : Finset α).sym2 = univ := by
  ext
  -- ⊢ a✝ ∈ Finset.sym2 univ ↔ a✝ ∈ univ
  simp only [mem_sym2_iff, mem_univ, implies_true]
  -- 🎉 no goals
#align finset.sym2_univ Finset.sym2_univ

@[simp]
theorem sym2_singleton (a : α) : ({a} : Finset α).sym2 = {Sym2.diag a} := by
  rw [Finset.sym2, singleton_product_singleton, image_singleton, Sym2.diag, Quotient.mk']
  -- 🎉 no goals
#align finset.sym2_singleton Finset.sym2_singleton

-- Porting note: add this lemma and remove simp in the next lemma since simpNF lint
-- warns that its LHS is not in normal form
@[simp]
theorem diag_mem_sym2_mem_iff : (∀ b, b ∈ Sym2.diag a → b ∈ s) ↔ a ∈ s := by
  rw [← mem_sym2_iff]
  -- ⊢ Sym2.diag a ∈ Finset.sym2 s ↔ a ∈ s
  exact mk'_mem_sym2_iff.trans <| and_self_iff _
  -- 🎉 no goals

theorem diag_mem_sym2_iff : Sym2.diag a ∈ s.sym2 ↔ a ∈ s := by simp [diag_mem_sym2_mem_iff]
                                                               -- 🎉 no goals
#align finset.diag_mem_sym2_iff Finset.diag_mem_sym2_iff

@[simp]
theorem sym2_mono (h : s ⊆ t) : s.sym2 ⊆ t.sym2 := fun _m he ↦
  mem_sym2_iff.2 fun _a ha ↦ h <| mem_sym2_iff.1 he _ ha
#align finset.sym2_mono Finset.sym2_mono

theorem image_diag_union_image_offDiag :
    s.diag.image Quotient.mk' ∪ s.offDiag.image Quotient.mk' = s.sym2 := by
  rw [← image_union, diag_union_offDiag]
  -- ⊢ image Quotient.mk' (s ×ˢ s) = Finset.sym2 s
  rfl
  -- 🎉 no goals
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
  -- ⊢ m ∈ Finset.sym s Nat.zero ↔ ∀ (a : α), a ∈ m → a ∈ s
  · refine' mem_singleton.trans ⟨_, fun _ ↦ Sym.eq_nil_of_card_zero _⟩
    -- ⊢ m = ∅ → ∀ (a : α), a ∈ m → a ∈ s
    rintro rfl
    -- ⊢ ∀ (a : α), a ∈ ∅ → a ∈ s
    exact fun a ha ↦ (Finset.not_mem_empty _ ha).elim
    -- 🎉 no goals
  refine' mem_sup.trans ⟨_, fun h ↦ _⟩
  -- ⊢ (∃ v, v ∈ s ∧ m ∈ image (Sym.cons v) (Finset.sym s n)) → ∀ (a : α), a ∈ m →  …
  · rintro ⟨a, ha, he⟩ b hb
    -- ⊢ b ∈ s
    rw [mem_image] at he
    -- ⊢ b ∈ s
    obtain ⟨m, he, rfl⟩ := he
    -- ⊢ b ∈ s
    rw [Sym.mem_cons] at hb
    -- ⊢ b ∈ s
    obtain rfl | hb := hb
    -- ⊢ b ∈ s
    · exact ha
      -- 🎉 no goals
    · exact ih.1 he _ hb
      -- 🎉 no goals
  · obtain ⟨a, m, rfl⟩ := m.exists_eq_cons_of_succ
    -- ⊢ ∃ v, v ∈ s ∧ a ::ₛ m ∈ image (Sym.cons v) (Finset.sym s n)
    exact
      ⟨a, h _ <| Sym.mem_cons_self _ _,
        mem_image_of_mem _ <| ih.2 fun b hb ↦ h _ <| Sym.mem_cons_of_mem hb⟩
#align finset.mem_sym_iff Finset.mem_sym_iff

@[simp]
theorem sym_empty (n : ℕ) : (∅ : Finset α).sym (n + 1) = ∅ := rfl
#align finset.sym_empty Finset.sym_empty

theorem replicate_mem_sym (ha : a ∈ s) (n : ℕ) : Sym.replicate n a ∈ s.sym n :=
  mem_sym_iff.2 fun b hb ↦ by rwa [(Sym.mem_replicate.1 hb).2]
                              -- 🎉 no goals
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
  -- ⊢ ¬Finset.Nonempty s
  exact fun hs ↦ h (hs.sym _)
  -- 🎉 no goals
#align finset.eq_empty_of_sym_eq_empty Finset.eq_empty_of_sym_eq_empty

@[simp]
theorem sym_eq_empty : s.sym n = ∅ ↔ n ≠ 0 ∧ s = ∅ := by
  cases n
  -- ⊢ Finset.sym s Nat.zero = ∅ ↔ Nat.zero ≠ 0 ∧ s = ∅
  · exact iff_of_false (singleton_ne_empty _) fun h ↦ (h.1 rfl).elim
    -- 🎉 no goals
  · refine ⟨fun h ↦ ⟨Nat.succ_ne_zero _, eq_empty_of_sym_eq_empty h⟩, ?_⟩
    -- ⊢ Nat.succ n✝ ≠ 0 ∧ s = ∅ → Finset.sym s (Nat.succ n✝) = ∅
    rintro ⟨_, rfl⟩
    -- ⊢ Finset.sym ∅ (Nat.succ n✝) = ∅
    exact sym_empty _
    -- 🎉 no goals
#align finset.sym_eq_empty Finset.sym_eq_empty

@[simp]
theorem sym_nonempty : (s.sym n).Nonempty ↔ n = 0 ∨ s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, Ne.def]
  -- ⊢ ¬Finset.sym s n = ∅ ↔ n = 0 ∨ ¬s = ∅
-- Porting note: using simp_rw does not work here, it does nothing...
  rwa [sym_eq_empty, not_and_or, not_ne_iff]
  -- 🎉 no goals
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
  -- ⊢ m ∈ Finset.sym (s ∩ t) n ↔ m ∈ Finset.sym s n ∩ Finset.sym t n
  simp only [mem_inter, mem_sym_iff, imp_and, forall_and]
  -- 🎉 no goals
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
                                        -- ⊢ s = erase (insert a s) a
                                                                        -- 🎉 no goals
  invFun m := ⟨m.2.1.fill a m.1, sym_fill_mem a m.2.2⟩
  left_inv m := Subtype.ext <| m.1.fill_filterNe a
  right_inv := fun ⟨i, m, hm⟩ ↦ by
    refine' Function.Injective.sigma_map (Function.injective_id) (fun i ↦ _) _
    exact fun i ↦ Sym α (n - i)
    swap; exact Subtype.coe_injective
          -- ⊢ Sigma.map id (fun i a => ↑a) ((fun m => { fst := (Sym.filterNe a ↑m).fst, sn …
    refine Eq.trans ?_ (Sym.filter_ne_fill a _ ?_)
    -- ⊢ Sigma.map id (fun i a => ↑a) ((fun m => { fst := (Sym.filterNe a ↑m).fst, sn …
    exacts [rfl, h ∘ mem_sym_iff.1 hm a]
    -- 🎉 no goals
#align finset.sym_insert_equiv Finset.symInsertEquiv

end Sym

end Finset
