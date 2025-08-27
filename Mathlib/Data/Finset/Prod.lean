/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Oliver Nash
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

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

assert_not_exists MonoidWithZero

open Multiset

variable {α β γ : Type*}

namespace Finset

/-! ### prod -/


section Prod

variable {s s' : Finset α} {t t' : Finset β} {a : α} {b : β}

/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
protected def product (s : Finset α) (t : Finset β) : Finset (α × β) :=
  ⟨_, s.nodup.product t.nodup⟩

instance instSProd : SProd (Finset α) (Finset β) (Finset (α × β)) where
  sprod := Finset.product

@[simp]
theorem product_eq_sprod : Finset.product s t = s ×ˢ t :=
  rfl

@[simp]
theorem product_val : (s ×ˢ t).1 = s.1 ×ˢ t.1 :=
  rfl

@[simp, grind =]
theorem mem_product {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Multiset.mem_product

theorem mk_mem_product (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t :=
  mem_product.2 ⟨ha, hb⟩

@[simp, norm_cast]
theorem coe_product (s : Finset α) (t : Finset β) :
    (↑(s ×ˢ t) : Set (α × β)) = (s : Set α) ×ˢ t :=
  Set.ext fun _ => Finset.mem_product

theorem subset_product_image_fst [DecidableEq α] : (s ×ˢ t).image Prod.fst ⊆ s := fun i => by
  simp +contextual [mem_image]

theorem subset_product_image_snd [DecidableEq β] : (s ×ˢ t).image Prod.snd ⊆ t := fun i => by
  simp +contextual [mem_image]

theorem product_image_fst [DecidableEq α] (ht : t.Nonempty) : (s ×ˢ t).image Prod.fst = s := by
  ext i
  simp [mem_image, ht.exists_mem]

theorem product_image_snd [DecidableEq β] (ht : s.Nonempty) : (s ×ˢ t).image Prod.snd = t := by
  ext i
  simp [mem_image, ht.exists_mem]

theorem subset_product [DecidableEq α] [DecidableEq β] {s : Finset (α × β)} :
    s ⊆ s.image Prod.fst ×ˢ s.image Prod.snd := by grind

@[gcongr]
theorem product_subset_product (hs : s ⊆ s') (ht : t ⊆ t') : s ×ˢ t ⊆ s' ×ˢ t' := fun ⟨_, _⟩ h =>
  mem_product.2 ⟨hs (mem_product.1 h).1, ht (mem_product.1 h).2⟩

theorem product_subset_product_left (hs : s ⊆ s') : s ×ˢ t ⊆ s' ×ˢ t :=
  product_subset_product hs (Subset.refl _)

theorem product_subset_product_right (ht : t ⊆ t') : s ×ˢ t ⊆ s ×ˢ t' :=
  product_subset_product (Subset.refl _) ht

theorem prodMap_image_product {δ : Type*} [DecidableEq β] [DecidableEq δ]
    (f : α → β) (g : γ → δ) (s : Finset α) (t : Finset γ) :
    (s ×ˢ t).image (Prod.map f g) = s.image f ×ˢ t.image g :=
  mod_cast Set.prodMap_image_prod f g s t

theorem prodMap_map_product {δ : Type*} (f : α ↪ β) (g : γ ↪ δ) (s : Finset α) (t : Finset γ) :
    (s ×ˢ t).map (f.prodMap g) = s.map f ×ˢ t.map g := by
  simpa [← coe_inj] using Set.prodMap_image_prod f g s t

theorem map_swap_product (s : Finset α) (t : Finset β) :
    (t ×ˢ s).map ⟨Prod.swap, Prod.swap_injective⟩ = s ×ˢ t :=
  coe_injective <| by
    push_cast
    exact Set.image_swap_prod _ _

@[simp]
theorem image_swap_product [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    (t ×ˢ s).image Prod.swap = s ×ˢ t :=
  coe_injective <| by
    push_cast
    exact Set.image_swap_prod _ _

theorem product_eq_biUnion [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    s ×ˢ t = s.biUnion fun a => t.image fun b => (a, b) := by grind

theorem product_eq_biUnion_right [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    s ×ˢ t = t.biUnion fun b => s.image fun a => (a, b) := by grind

/-- See also `Finset.sup_product_left`. -/
@[simp]
theorem product_biUnion [DecidableEq γ] (s : Finset α) (t : Finset β) (f : α × β → Finset γ) :
    (s ×ˢ t).biUnion f = s.biUnion fun a => t.biUnion fun b => f (a, b) := by grind

@[simp]
theorem card_product (s : Finset α) (t : Finset β) : card (s ×ˢ t) = card s * card t :=
  Multiset.card_product _ _

/-- The product of two Finsets is nontrivial iff both are nonempty
  at least one of them is nontrivial. -/
lemma nontrivial_prod_iff : (s ×ˢ t).Nontrivial ↔
    s.Nonempty ∧ t.Nonempty ∧ (s.Nontrivial ∨ t.Nontrivial) := by
  simp_rw [← card_pos, ← one_lt_card_iff_nontrivial, card_product]; apply Nat.one_lt_mul_iff

theorem filter_product (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => p x.1 ∧ q x.2) = s.filter p ×ˢ t.filter q := by grind

theorem filter_product_left (p : α → Prop) [DecidablePred p] :
    ((s ×ˢ t).filter fun x : α × β => p x.1) = s.filter p ×ˢ t := by
  simpa using filter_product p fun _ => true

theorem filter_product_right (q : β → Prop) [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => q x.2) = s ×ˢ t.filter q := by
  simpa using filter_product (fun _ : α => true) q

theorem filter_product_card (s : Finset α) (t : Finset β) (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => (p x.1) = (q x.2)).card =
      (s.filter p).card * (t.filter q).card +
        (s.filter (¬ p ·)).card * (t.filter (¬ q ·)).card := by
  classical
  rw [← card_product, ← card_product, ← filter_product, ← filter_product, ← card_union_of_disjoint]
  · apply congr_arg
    ext ⟨a, b⟩
    simp only [filter_union_right, mem_filter, mem_product]
    constructor <;> intro h <;> use h.1
    · simp only [h.2, Decidable.em, and_self]
    · revert h
      simp only [and_imp]
      rintro _ _ (_ | _) <;> simp [*]
  · apply Finset.disjoint_filter_filter'
    exact (disjoint_compl_right.inf_left _).inf_right _

@[simp]
theorem empty_product (t : Finset β) : (∅ : Finset α) ×ˢ t = ∅ :=
  rfl

@[simp]
theorem product_empty (s : Finset α) : s ×ˢ (∅ : Finset β) = ∅ :=
  eq_empty_of_forall_notMem fun _ h => notMem_empty _ (Finset.mem_product.1 h).2

@[aesop safe apply (rule_sets := [finsetNonempty])]
theorem Nonempty.product (hs : s.Nonempty) (ht : t.Nonempty) : (s ×ˢ t).Nonempty :=
  let ⟨x, hx⟩ := hs
  let ⟨y, hy⟩ := ht
  ⟨(x, y), mem_product.2 ⟨hx, hy⟩⟩

theorem Nonempty.fst (h : (s ×ˢ t).Nonempty) : s.Nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.1, (mem_product.1 hxy).1⟩

theorem Nonempty.snd (h : (s ×ˢ t).Nonempty) : t.Nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.2, (mem_product.1 hxy).2⟩

@[simp]
theorem nonempty_product : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.product h.2⟩

@[simp]
theorem product_eq_empty {s : Finset α} {t : Finset β} : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  rw [← not_nonempty_iff_eq_empty, nonempty_product, not_and_or, not_nonempty_iff_eq_empty,
    not_nonempty_iff_eq_empty]

@[simp]
theorem singleton_product {a : α} :
    ({a} : Finset α) ×ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩ := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]
lemma product_singleton : s ×ˢ {b} = s.map ⟨fun i => (i, b), Prod.mk_left_injective _⟩ := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

theorem singleton_product_singleton {a : α} {b : β} :
    ({a} ×ˢ {b} : Finset _) = {(a, b)} := by
  simp only [product_singleton, Function.Embedding.coeFn_mk, map_singleton]

@[simp]
theorem union_product [DecidableEq α] [DecidableEq β] : (s ∪ s') ×ˢ t = s ×ˢ t ∪ s' ×ˢ t := by grind

@[simp]
theorem product_union [DecidableEq α] [DecidableEq β] : s ×ˢ (t ∪ t') = s ×ˢ t ∪ s ×ˢ t' := by grind

theorem inter_product [DecidableEq α] [DecidableEq β] : (s ∩ s') ×ˢ t = s ×ˢ t ∩ s' ×ˢ t := by grind

theorem product_inter [DecidableEq α] [DecidableEq β] : s ×ˢ (t ∩ t') = s ×ˢ t ∩ s ×ˢ t' := by grind

theorem product_inter_product [DecidableEq α] [DecidableEq β] :
    s ×ˢ t ∩ s' ×ˢ t' = (s ∩ s') ×ˢ (t ∩ t') := by grind

theorem disjoint_product : Disjoint (s ×ˢ t) (s' ×ˢ t') ↔ Disjoint s s' ∨ Disjoint t t' := by
  simp_rw [← disjoint_coe, coe_product, Set.disjoint_prod]

@[simp]
theorem disjUnion_product (hs : Disjoint s s') :
    s.disjUnion s' hs ×ˢ t = (s ×ˢ t).disjUnion (s' ×ˢ t) (disjoint_product.mpr <| Or.inl hs) :=
  eq_of_veq <| Multiset.add_product _ _ _

@[simp]
theorem product_disjUnion (ht : Disjoint t t') :
    s ×ˢ t.disjUnion t' ht = (s ×ˢ t).disjUnion (s ×ˢ t') (disjoint_product.mpr <| Or.inr ht) :=
  eq_of_veq <| Multiset.product_add _ _ _

end Prod

section Diag

variable [DecidableEq α] (s t : Finset α)

/-- Given a finite set `s`, the diagonal, `s.diag` is the set of pairs of the form `(a, a)` for
`a ∈ s`. -/
def diag :=
  (s ×ˢ s).filter fun a : α × α => a.fst = a.snd

/-- Given a finite set `s`, the off-diagonal, `s.offDiag` is the set of pairs `(a, b)` with `a ≠ b`
for `a, b ∈ s`. -/
def offDiag :=
  (s ×ˢ s).filter fun a : α × α => a.fst ≠ a.snd

variable {s} {x : α × α}

@[simp, grind =]
theorem mem_diag : x ∈ s.diag ↔ x.1 ∈ s ∧ x.1 = x.2 := by
  simp +contextual [diag]

@[simp, grind =]
theorem mem_offDiag : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 := by
  simp [offDiag, and_assoc]

-- TODO rename nonempty_diag
@[simp, grind =]
theorem diag_nonempty : s.diag.Nonempty ↔ s.Nonempty := by
  simp [Finset.Nonempty]

@[simp, grind =]
theorem diag_eq_empty : s.diag = ∅ ↔ s = ∅ := by
  have := (diag_nonempty (s := s)).not
  rwa [not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty] at this

variable (s)

@[simp]
theorem image_diag [DecidableEq β] (f : α × α → β) (s : Finset α) :
    s.diag.image f = s.image fun x ↦ f (x, x) := by
  ext y
  aesop

@[simp, norm_cast]
theorem coe_offDiag : (s.offDiag : Set (α × α)) = (s : Set α).offDiag :=
  Set.ext fun _ => mem_offDiag

@[simp]
theorem diag_card : (diag s).card = s.card := by
  suffices diag s = s.image fun a => (a, a) by
    rw [this]
    apply card_image_of_injOn
    exact fun x1 _ x2 _ h3 => (Prod.mk.inj h3).1
  grind

@[simp]
theorem offDiag_card : (offDiag s).card = s.card * s.card - s.card :=
  suffices (diag s).card + (offDiag s).card = s.card * s.card by rw [s.diag_card] at this; omega
  by rw [← card_product, diag, offDiag]
     conv_rhs => rw [← filter_card_add_filter_neg_card_eq_card (fun a => a.1 = a.2)]

@[mono]
theorem diag_mono : Monotone (diag : Finset α → Finset (α × α)) := fun _ _ h _ hx =>
  mem_diag.2 <| And.imp_left (@h _) <| mem_diag.1 hx

@[mono]
theorem offDiag_mono : Monotone (offDiag : Finset α → Finset (α × α)) := fun _ _ h _ hx =>
  mem_offDiag.2 <| And.imp (@h _) (And.imp_left <| @h _) <| mem_offDiag.1 hx

@[simp]
theorem diag_empty : (∅ : Finset α).diag = ∅ :=
  rfl

@[simp]
theorem offDiag_empty : (∅ : Finset α).offDiag = ∅ :=
  rfl

@[simp]
theorem diag_union_offDiag : s.diag ∪ s.offDiag = s ×ˢ s := by
  conv_rhs => rw [← filter_union_filter_neg_eq (fun a => a.1 = a.2) (s ×ˢ s)]
  rfl

@[simp]
theorem disjoint_diag_offDiag : Disjoint s.diag s.offDiag :=
  disjoint_filter_filter_neg (s ×ˢ s) (s ×ˢ s) (fun a => a.1 = a.2)

theorem product_sdiff_diag : s ×ˢ s \ s.diag = s.offDiag := by grind

theorem product_sdiff_offDiag : s ×ˢ s \ s.offDiag = s.diag := by grind

theorem diag_inter : (s ∩ t).diag = s.diag ∩ t.diag := by grind

theorem offDiag_inter : (s ∩ t).offDiag = s.offDiag ∩ t.offDiag :=
  coe_injective <| by
    push_cast
    exact Set.offDiag_inter _ _

theorem diag_union : (s ∪ t).diag = s.diag ∪ t.diag := by grind

variable {s t}

theorem offDiag_union (h : Disjoint s t) :
    (s ∪ t).offDiag = s.offDiag ∪ t.offDiag ∪ s ×ˢ t ∪ t ×ˢ s :=
  coe_injective <| by
    push_cast
    exact Set.offDiag_union (disjoint_coe.2 h)

variable (a : α)

@[simp]
theorem offDiag_singleton : ({a} : Finset α).offDiag = ∅ := by simp [← Finset.card_eq_zero]

theorem diag_singleton : ({a} : Finset α).diag = {(a, a)} := by grind

theorem diag_insert : (insert a s).diag = insert (a, a) s.diag := by grind

theorem offDiag_insert (has : a ∉ s) : (insert a s).offDiag = s.offDiag ∪ {a} ×ˢ s ∪ s ×ˢ {a} := by
  grind

theorem offDiag_filter_lt_eq_filter_le {ι} [PartialOrder ι]
    [DecidableEq ι] [DecidableLE ι] [DecidableLT ι] (s : Finset ι) :
    s.offDiag.filter (fun i => i.1 < i.2) = s.offDiag.filter (fun i => i.1 ≤ i.2) := by
  rw [Finset.filter_inj']
  rintro ⟨i, j⟩
  simp_rw [mem_offDiag, and_imp]
  rintro _ _ h
  rw [Ne.le_iff_lt h]

end Diag

end Finset
