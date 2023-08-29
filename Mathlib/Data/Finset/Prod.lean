/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Oliver Nash
-/
import Mathlib.Data.Finset.Card

#align_import data.finset.prod from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Finsets in product types

This file defines finset constructions on the product type `α × β`. Beware not to confuse with the
`Finset.prod` operation which computes the multiplicative product.

## Main declarations

* `Finset.product`: Turns `s : Finset α`, `t : Finset β` into their product in `Finset (α × β)`.
* `Finset.diag`: For `s : Finset α`, `s.diag` is the `Finset (α × α)` of pairs `(a, a)` with
  `a ∈ s`.
* `Finset.offDiag`: For `s : Finset α`, `s.offDiag` is the `Finset (α × α)` of pairs `(a, b)` with
  `a, b ∈ s` and `a ≠ b`.
-/


open Multiset

variable {α β γ : Type*}

namespace Finset

/-! ### prod -/


section Prod

variable {s s' : Finset α} {t t' : Finset β} {a : α} {b : β}

/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
protected def product (s : Finset α) (t : Finset β) : Finset (α × β) :=
  ⟨_, s.nodup.product t.nodup⟩
#align finset.product Finset.product

instance instSProd : SProd (Finset α) (Finset β) (Finset (α × β)) where
  sprod := Finset.product

@[simp]
theorem product_val : (s ×ˢ t).1 = s.1 ×ˢ t.1 :=
  rfl
#align finset.product_val Finset.product_val

@[simp]
theorem mem_product {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Multiset.mem_product
#align finset.mem_product Finset.mem_product

theorem mk_mem_product (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t :=
  mem_product.2 ⟨ha, hb⟩
#align finset.mk_mem_product Finset.mk_mem_product

@[simp, norm_cast]
theorem coe_product (s : Finset α) (t : Finset β) :
    (↑(s ×ˢ t) : Set (α × β)) = (s : Set α) ×ˢ t :=
  Set.ext fun _ => Finset.mem_product
#align finset.coe_product Finset.coe_product

theorem subset_product_image_fst [DecidableEq α] : (s ×ˢ t).image Prod.fst ⊆ s := fun i => by
  simp (config := { contextual := true }) [mem_image]
  -- 🎉 no goals
#align finset.subset_product_image_fst Finset.subset_product_image_fst

theorem subset_product_image_snd [DecidableEq β] : (s ×ˢ t).image Prod.snd ⊆ t := fun i => by
  simp (config := { contextual := true }) [mem_image]
  -- 🎉 no goals
#align finset.subset_product_image_snd Finset.subset_product_image_snd

theorem product_image_fst [DecidableEq α] (ht : t.Nonempty) : (s ×ˢ t).image Prod.fst = s := by
  ext i
  -- ⊢ i ∈ image Prod.fst (s ×ˢ t) ↔ i ∈ s
  simp [mem_image, ht.bex]
  -- 🎉 no goals
#align finset.product_image_fst Finset.product_image_fst

theorem product_image_snd [DecidableEq β] (ht : s.Nonempty) : (s ×ˢ t).image Prod.snd = t := by
  ext i
  -- ⊢ i ∈ image Prod.snd (s ×ˢ t) ↔ i ∈ t
  simp [mem_image, ht.bex]
  -- 🎉 no goals
#align finset.product_image_snd Finset.product_image_snd

theorem subset_product [DecidableEq α] [DecidableEq β] {s : Finset (α × β)} :
    s ⊆ s.image Prod.fst ×ˢ s.image Prod.snd := fun _ hp =>
  mem_product.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩
#align finset.subset_product Finset.subset_product

theorem product_subset_product (hs : s ⊆ s') (ht : t ⊆ t') : s ×ˢ t ⊆ s' ×ˢ t' := fun ⟨_, _⟩ h =>
  mem_product.2 ⟨hs (mem_product.1 h).1, ht (mem_product.1 h).2⟩
#align finset.product_subset_product Finset.product_subset_product

theorem product_subset_product_left (hs : s ⊆ s') : s ×ˢ t ⊆ s' ×ˢ t :=
  product_subset_product hs (Subset.refl _)
#align finset.product_subset_product_left Finset.product_subset_product_left

theorem product_subset_product_right (ht : t ⊆ t') : s ×ˢ t ⊆ s ×ˢ t' :=
  product_subset_product (Subset.refl _) ht
#align finset.product_subset_product_right Finset.product_subset_product_right

theorem map_swap_product (s : Finset α) (t : Finset β) :
    (t ×ˢ s).map ⟨Prod.swap, Prod.swap_injective⟩ = s ×ˢ t :=
  coe_injective <| by
    push_cast
    -- ⊢ (fun a => ↑{ toFun := Prod.swap, inj' := (_ : Function.Injective Prod.swap)  …
    exact Set.image_swap_prod _ _
    -- 🎉 no goals
#align finset.map_swap_product Finset.map_swap_product

@[simp]
theorem image_swap_product [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    (t ×ˢ s).image Prod.swap = s ×ˢ t :=
  coe_injective <| by
    push_cast
    -- ⊢ Prod.swap '' ↑t ×ˢ ↑s = ↑s ×ˢ ↑t
    exact Set.image_swap_prod _ _
    -- 🎉 no goals
#align finset.image_swap_product Finset.image_swap_product

theorem product_eq_biUnion [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    s ×ˢ t = s.biUnion fun a => t.image fun b => (a, b) :=
  ext fun ⟨x, y⟩ => by
    simp only [mem_product, mem_biUnion, mem_image, exists_prop, Prod.mk.inj_iff, and_left_comm,
      exists_and_left, exists_eq_right, exists_eq_left]
#align finset.product_eq_bUnion Finset.product_eq_biUnion

theorem product_eq_biUnion_right [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    s ×ˢ t = t.biUnion fun b => s.image fun a => (a, b) :=
  ext fun ⟨x, y⟩ => by
    simp only [mem_product, mem_biUnion, mem_image, exists_prop, Prod.mk.inj_iff, and_left_comm,
      exists_and_left, exists_eq_right, exists_eq_left]
#align finset.product_eq_bUnion_right Finset.product_eq_biUnion_right

/-- See also `Finset.sup_product_left`. -/
@[simp]
theorem product_biUnion [DecidableEq γ] (s : Finset α) (t : Finset β) (f : α × β → Finset γ) :
    (s ×ˢ t).biUnion f = s.biUnion fun a => t.biUnion fun b => f (a, b) := by
  classical simp_rw [product_eq_biUnion, biUnion_biUnion, image_biUnion]
  -- 🎉 no goals
#align finset.product_bUnion Finset.product_biUnion

@[simp]
theorem card_product (s : Finset α) (t : Finset β) : card (s ×ˢ t) = card s * card t :=
  Multiset.card_product _ _
#align finset.card_product Finset.card_product

theorem filter_product (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => p x.1 ∧ q x.2) = s.filter p ×ˢ t.filter q := by
  ext ⟨a, b⟩
  -- ⊢ (a, b) ∈ filter (fun x => p x.fst ∧ q x.snd) (s ×ˢ t) ↔ (a, b) ∈ filter p s  …
  simp [mem_filter, mem_product, decide_eq_true_eq, and_comm, and_left_comm, and_assoc]
  -- 🎉 no goals
#align finset.filter_product Finset.filter_product

theorem filter_product_left (p : α → Prop) [DecidablePred p] :
    ((s ×ˢ t).filter fun x : α × β => p x.1) = s.filter p ×ˢ t := by
  simpa using filter_product p fun _ => true
  -- 🎉 no goals
#align finset.filter_product_left Finset.filter_product_left

theorem filter_product_right (q : β → Prop) [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => q x.2) = s ×ˢ t.filter q := by
  simpa using filter_product (fun _ : α => true) q
  -- 🎉 no goals
#align finset.filter_product_right Finset.filter_product_right

theorem filter_product_card (s : Finset α) (t : Finset β) (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => (p x.1) = (q x.2)).card =
      (s.filter p).card * (t.filter q).card +
        (s.filter (¬ p ·)).card * (t.filter (¬ q ·)).card := by
  classical
    rw [← card_product, ← card_product, ← filter_product, ← filter_product, ← card_union_eq]
    · apply congr_arg
      ext ⟨a, b⟩
      simp only [filter_union_right, mem_filter, mem_product]
      constructor <;> intro h <;> use h.1
      · simp only [h.2, Function.comp_apply, Decidable.em, and_self]
      · revert h
        simp only [Function.comp_apply, and_imp]
        rintro _ _ (_|_) <;> simp [*]
    · apply Finset.disjoint_filter_filter'
      exact (disjoint_compl_right.inf_left _).inf_right _
#align finset.filter_product_card Finset.filter_product_card

theorem empty_product (t : Finset β) : (∅ : Finset α) ×ˢ t = ∅ :=
  rfl
#align finset.empty_product Finset.empty_product

theorem product_empty (s : Finset α) : s ×ˢ (∅ : Finset β) = ∅ :=
  eq_empty_of_forall_not_mem fun _ h => not_mem_empty _ (Finset.mem_product.1 h).2
#align finset.product_empty Finset.product_empty

theorem Nonempty.product (hs : s.Nonempty) (ht : t.Nonempty) : (s ×ˢ t).Nonempty :=
  let ⟨x, hx⟩ := hs
  let ⟨y, hy⟩ := ht
  ⟨(x, y), mem_product.2 ⟨hx, hy⟩⟩
#align finset.nonempty.product Finset.Nonempty.product

theorem Nonempty.fst (h : (s ×ˢ t).Nonempty) : s.Nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.1, (mem_product.1 hxy).1⟩
#align finset.nonempty.fst Finset.Nonempty.fst

theorem Nonempty.snd (h : (s ×ˢ t).Nonempty) : t.Nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.2, (mem_product.1 hxy).2⟩
#align finset.nonempty.snd Finset.Nonempty.snd

@[simp]
theorem nonempty_product : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.product h.2⟩
#align finset.nonempty_product Finset.nonempty_product

@[simp]
theorem product_eq_empty {s : Finset α} {t : Finset β} : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  rw [← not_nonempty_iff_eq_empty, nonempty_product, not_and_or, not_nonempty_iff_eq_empty,
    not_nonempty_iff_eq_empty]
#align finset.product_eq_empty Finset.product_eq_empty

@[simp]
theorem singleton_product {a : α} :
    ({a} : Finset α) ×ˢ t = t.map ⟨Prod.mk a, Prod.mk.inj_left _⟩ := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ {a} ×ˢ t ↔ (x, y) ∈ map { toFun := Prod.mk a, inj' := (_ : Function …
  simp [and_left_comm, eq_comm]
  -- 🎉 no goals
#align finset.singleton_product Finset.singleton_product

@[simp]
theorem product_singleton {b : β} : s ×ˢ {b} = s.map ⟨fun i => (i, b), Prod.mk.inj_right _⟩ := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ s ×ˢ {b} ↔ (x, y) ∈ map { toFun := fun i => (i, b), inj' := (_ : Fu …
  simp [and_left_comm, eq_comm]
  -- 🎉 no goals
#align finset.product_singleton Finset.product_singleton

theorem singleton_product_singleton {a : α} {b : β} :
    ({a} ×ˢ {b} : Finset _) = {(a, b)} := by
  simp only [product_singleton, Function.Embedding.coeFn_mk, map_singleton]
  -- 🎉 no goals
#align finset.singleton_product_singleton Finset.singleton_product_singleton

@[simp]
theorem union_product [DecidableEq α] [DecidableEq β] : (s ∪ s') ×ˢ t = s ×ˢ t ∪ s' ×ˢ t := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ (s ∪ s') ×ˢ t ↔ (x, y) ∈ s ×ˢ t ∪ s' ×ˢ t
  simp only [or_and_right, mem_union, mem_product]
  -- 🎉 no goals
#align finset.union_product Finset.union_product

@[simp]
theorem product_union [DecidableEq α] [DecidableEq β] : s ×ˢ (t ∪ t') = s ×ˢ t ∪ s ×ˢ t' := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ s ×ˢ (t ∪ t') ↔ (x, y) ∈ s ×ˢ t ∪ s ×ˢ t'
  simp only [and_or_left, mem_union, mem_product]
  -- 🎉 no goals
#align finset.product_union Finset.product_union

theorem inter_product [DecidableEq α] [DecidableEq β] : (s ∩ s') ×ˢ t = s ×ˢ t ∩ s' ×ˢ t := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ (s ∩ s') ×ˢ t ↔ (x, y) ∈ s ×ˢ t ∩ s' ×ˢ t
  simp only [← and_and_right, mem_inter, mem_product]
  -- 🎉 no goals
#align finset.inter_product Finset.inter_product

theorem product_inter [DecidableEq α] [DecidableEq β] : s ×ˢ (t ∩ t') = s ×ˢ t ∩ s ×ˢ t' := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ s ×ˢ (t ∩ t') ↔ (x, y) ∈ s ×ˢ t ∩ s ×ˢ t'
  simp only [← and_and_left, mem_inter, mem_product]
  -- 🎉 no goals
#align finset.product_inter Finset.product_inter

theorem product_inter_product [DecidableEq α] [DecidableEq β] :
    s ×ˢ t ∩ s' ×ˢ t' = (s ∩ s') ×ˢ (t ∩ t') := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ s ×ˢ t ∩ s' ×ˢ t' ↔ (x, y) ∈ (s ∩ s') ×ˢ (t ∩ t')
  simp only [and_assoc, and_left_comm, mem_inter, mem_product]
  -- 🎉 no goals
#align finset.product_inter_product Finset.product_inter_product

theorem disjoint_product : Disjoint (s ×ˢ t) (s' ×ˢ t') ↔ Disjoint s s' ∨ Disjoint t t' := by
  simp_rw [← disjoint_coe, coe_product, Set.disjoint_prod]
  -- 🎉 no goals
#align finset.disjoint_product Finset.disjoint_product

@[simp]
theorem disjUnion_product (hs : Disjoint s s') :
    s.disjUnion s' hs ×ˢ t = (s ×ˢ t).disjUnion (s' ×ˢ t) (disjoint_product.mpr <| Or.inl hs) :=
  eq_of_veq <| Multiset.add_product _ _ _
#align finset.disj_union_product Finset.disjUnion_product

@[simp]
theorem product_disjUnion (ht : Disjoint t t') :
    s ×ˢ t.disjUnion t' ht = (s ×ˢ t).disjUnion (s ×ˢ t') (disjoint_product.mpr <| Or.inr ht) :=
  eq_of_veq <| Multiset.product_add _ _ _
#align finset.product_disj_union Finset.product_disjUnion

end Prod

section Diag

variable [DecidableEq α] (s t : Finset α)

/-- Given a finite set `s`, the diagonal, `s.diag` is the set of pairs of the form `(a, a)` for
`a ∈ s`. -/
def diag :=
  (s ×ˢ s).filter fun a : α × α => a.fst = a.snd
#align finset.diag Finset.diag

/-- Given a finite set `s`, the off-diagonal, `s.offDiag` is the set of pairs `(a, b)` with `a ≠ b`
for `a, b ∈ s`. -/
def offDiag :=
  (s ×ˢ s).filter fun a : α × α => a.fst ≠ a.snd
#align finset.off_diag Finset.offDiag

variable {s} {x : α × α}

@[simp]
theorem mem_diag : x ∈ s.diag ↔ x.1 ∈ s ∧ x.1 = x.2 := by
  simp (config := { contextual := true }) [diag]
  -- 🎉 no goals
#align finset.mem_diag Finset.mem_diag

@[simp]
theorem mem_offDiag : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 := by
  simp [offDiag, and_assoc]
  -- 🎉 no goals
#align finset.mem_off_diag Finset.mem_offDiag

variable (s)

@[simp, norm_cast]
theorem coe_offDiag : (s.offDiag : Set (α × α)) = (s : Set α).offDiag :=
  Set.ext fun _ => mem_offDiag
#align finset.coe_off_diag Finset.coe_offDiag

@[simp]
theorem diag_card : (diag s).card = s.card := by
  suffices diag s = s.image fun a => (a, a) by
    rw [this]
    apply card_image_of_injOn
    exact fun x1 _ x2 _ h3 => (Prod.mk.inj h3).1
  ext ⟨a₁, a₂⟩
  -- ⊢ (a₁, a₂) ∈ diag s ↔ (a₁, a₂) ∈ image (fun a => (a, a)) s
  rw [mem_diag]
  -- ⊢ (a₁, a₂).fst ∈ s ∧ (a₁, a₂).fst = (a₁, a₂).snd ↔ (a₁, a₂) ∈ image (fun a =>  …
  constructor <;> intro h <;> rw [Finset.mem_image] at *
  -- ⊢ (a₁, a₂).fst ∈ s ∧ (a₁, a₂).fst = (a₁, a₂).snd → (a₁, a₂) ∈ image (fun a =>  …
                  -- ⊢ (a₁, a₂) ∈ image (fun a => (a, a)) s
                  -- ⊢ (a₁, a₂).fst ∈ s ∧ (a₁, a₂).fst = (a₁, a₂).snd
                              -- ⊢ ∃ a, a ∈ s ∧ (a, a) = (a₁, a₂)
                              -- ⊢ (a₁, a₂).fst ∈ s ∧ (a₁, a₂).fst = (a₁, a₂).snd
  · use a₁
    -- ⊢ a₁ ∈ s ∧ (a₁, a₁) = (a₁, a₂)
    simpa using h
    -- 🎉 no goals
  · rcases h with ⟨a, h1, h2⟩
    -- ⊢ (a₁, a₂).fst ∈ s ∧ (a₁, a₂).fst = (a₁, a₂).snd
    have h := Prod.mk.inj h2
    -- ⊢ (a₁, a₂).fst ∈ s ∧ (a₁, a₂).fst = (a₁, a₂).snd
    rw [← h.1, ← h.2]
    -- ⊢ (a, a).fst ∈ s ∧ (a, a).fst = (a, a).snd
    use h1
    -- 🎉 no goals
#align finset.diag_card Finset.diag_card

@[simp]
theorem offDiag_card : (offDiag s).card = s.card * s.card - s.card :=
  suffices (diag s).card + (offDiag s).card = s.card * s.card by
    conv_rhs => { rw [← s.diag_card] }
    -- ⊢ card (offDiag s) = card (diag s) * card (diag s) - card (diag s)
    simp only [diag_card] at *
    -- ⊢ card (offDiag s) = card s * card s - card s
    rw [tsub_eq_of_eq_add_rev]
     -- ⊢ card (filter (fun a => a.fst = a.snd) (s ×ˢ s)) + card (filter (fun a => a.f …
    -- ⊢ card s * card s = card s + card (offDiag s)
     -- 🎉 no goals
    rw [this]
    -- 🎉 no goals
  by rw [← card_product, diag, offDiag]
     conv_rhs => rw [← filter_card_add_filter_neg_card_eq_card (fun a => a.1 = a.2)]
#align finset.off_diag_card Finset.offDiag_card

@[mono]
theorem diag_mono : Monotone (diag : Finset α → Finset (α × α)) := fun _ _ h _ hx =>
  mem_diag.2 <| And.imp_left (@h _) <| mem_diag.1 hx
#align finset.diag_mono Finset.diag_mono

@[mono]
theorem offDiag_mono : Monotone (offDiag : Finset α → Finset (α × α)) := fun _ _ h _ hx =>
  mem_offDiag.2 <| And.imp (@h _) (And.imp_left <| @h _) <| mem_offDiag.1 hx
#align finset.off_diag_mono Finset.offDiag_mono

@[simp]
theorem diag_empty : (∅ : Finset α).diag = ∅ :=
  rfl
#align finset.diag_empty Finset.diag_empty

@[simp]
theorem offDiag_empty : (∅ : Finset α).offDiag = ∅ :=
  rfl
#align finset.off_diag_empty Finset.offDiag_empty

@[simp]
theorem diag_union_offDiag : s.diag ∪ s.offDiag = s ×ˢ s := by
  conv_rhs => rw [← filter_union_filter_neg_eq (fun a => a.1 = a.2) (s ×ˢ s)]
  -- 🎉 no goals
#align finset.diag_union_off_diag Finset.diag_union_offDiag

@[simp]
theorem disjoint_diag_offDiag : Disjoint s.diag s.offDiag :=
  disjoint_filter_filter_neg (s ×ˢ s) (s ×ˢ s) (fun a => a.1 = a.2)
#align finset.disjoint_diag_off_diag Finset.disjoint_diag_offDiag

theorem product_sdiff_diag : s ×ˢ s \ s.diag = s.offDiag := by
  rw [← diag_union_offDiag, union_comm, union_sdiff_self,
    sdiff_eq_self_of_disjoint (disjoint_diag_offDiag _).symm]
#align finset.product_sdiff_diag Finset.product_sdiff_diag

theorem product_sdiff_offDiag : s ×ˢ s \ s.offDiag = s.diag := by
  rw [← diag_union_offDiag, union_sdiff_self, sdiff_eq_self_of_disjoint (disjoint_diag_offDiag _)]
  -- 🎉 no goals
#align finset.product_sdiff_off_diag Finset.product_sdiff_offDiag

theorem diag_inter : (s ∩ t).diag = s.diag ∩ t.diag :=
  ext fun x => by simpa only [mem_diag, mem_inter] using and_and_right
                  -- 🎉 no goals
#align finset.diag_inter Finset.diag_inter

theorem offDiag_inter : (s ∩ t).offDiag = s.offDiag ∩ t.offDiag :=
  coe_injective <| by
    push_cast
    -- ⊢ Set.offDiag (↑s ∩ ↑t) = Set.offDiag ↑s ∩ Set.offDiag ↑t
    exact Set.offDiag_inter _ _
    -- 🎉 no goals
#align finset.off_diag_inter Finset.offDiag_inter

theorem diag_union : (s ∪ t).diag = s.diag ∪ t.diag := by
  ext ⟨i, j⟩
  -- ⊢ (i, j) ∈ diag (s ∪ t) ↔ (i, j) ∈ diag s ∪ diag t
  simp only [mem_diag, mem_union, or_and_right]
  -- 🎉 no goals
#align finset.diag_union Finset.diag_union

variable {s t}

theorem offDiag_union (h : Disjoint s t) :
    (s ∪ t).offDiag = s.offDiag ∪ t.offDiag ∪ s ×ˢ t ∪ t ×ˢ s :=
  coe_injective <| by
    push_cast
    -- ⊢ Set.offDiag (↑s ∪ ↑t) = Set.offDiag ↑s ∪ Set.offDiag ↑t ∪ ↑s ×ˢ ↑t ∪ ↑t ×ˢ ↑s
    exact Set.offDiag_union (disjoint_coe.2 h)
    -- 🎉 no goals
#align finset.off_diag_union Finset.offDiag_union

variable (a : α)

@[simp]
theorem offDiag_singleton : ({a} : Finset α).offDiag = ∅ := by simp [← Finset.card_eq_zero]
                                                               -- 🎉 no goals
#align finset.off_diag_singleton Finset.offDiag_singleton

theorem diag_singleton : ({a} : Finset α).diag = {(a, a)} := by
  rw [← product_sdiff_offDiag, offDiag_singleton, sdiff_empty, singleton_product_singleton]
  -- 🎉 no goals
#align finset.diag_singleton Finset.diag_singleton

theorem diag_insert : (insert a s).diag = insert (a, a) s.diag := by
  rw [insert_eq, insert_eq, diag_union, diag_singleton]
  -- 🎉 no goals
#align finset.diag_insert Finset.diag_insert

theorem offDiag_insert (has : a ∉ s) : (insert a s).offDiag = s.offDiag ∪ {a} ×ˢ s ∪ s ×ˢ {a} := by
  rw [insert_eq, union_comm, offDiag_union (disjoint_singleton_right.2 has), offDiag_singleton,
    union_empty, union_right_comm]
#align finset.off_diag_insert Finset.offDiag_insert

end Diag

end Finset
