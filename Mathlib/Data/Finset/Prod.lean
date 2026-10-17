/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Oliver Nash
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.List.OffDiag
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Finsets in product types

This file defines finset constructions on the product type `α × β`. Beware not to confuse with the
`Finset.prod` operation which computes the multiplicative product.

## Main declarations

* `Finset.product`: Turns `s : Finset α`, `t : Finset β` into their product in `Finset (α × β)`.
* `Finset.diagonal`: For `s : Finset α`, `s.diagonal` is the `Finset (α × α)` of pairs `(a, a)` with
  `a ∈ s`.
* `Finset.offDiagonal`: For `s : Finset α`, `s.offDiagonal` is the `Finset (α × α)` of pairs
  `(a, b)` with `a, b ∈ s` and `a ≠ b`.
-/

@[expose] public section

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

/-- The product `s ×ˢ t` of two finsets, viewed as a subtype, is equivalent to the product of the
subtypes `s × t`. The `Finset` analogue of `Equiv.Set.prod`. -/
def _root_.Equiv.Finset.prod (s : Finset α) (t : Finset β) : ↥(s ×ˢ t) ≃ s × t where
  toFun x := ⟨⟨x.1.1, (mem_product.mp x.2).1⟩, ⟨x.1.2, (mem_product.mp x.2).2⟩⟩
  invFun x := ⟨⟨x.1.1, x.2.1⟩, mem_product.mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

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
    grind
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
  contrapose!; exact nonempty_product

@[simp]
theorem singleton_product {a : α} : ({a} : Finset α) ×ˢ t = t.map (.sectR a _) := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]
lemma product_singleton : s ×ˢ {b} = s.map (.sectL _ b) := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

theorem singleton_product_singleton {a : α} {b : β} : ({a} ×ˢ {b} : Finset _) = {(a, b)} := rfl

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

section Diagonal

variable (s t : Finset α)

/-- Given a finite set `s`, the diagonal, `s.diagonal` is the set of pairs of the form `(a, a)` for
`a ∈ s`. -/
def diagonal : Finset (α × α) := s.map ⟨Prod.diagonal, Prod.diagonal_injective⟩

@[deprecated (since := "2026-09-06")] alias diag := diagonal

-- TODO: define `Multiset.offDiagonal`, provide basic API, use it here
/-- Given a finite set `s`, the off-diagonal, `s.offDiagonal` is the set of pairs `(a, b)` with
`a ≠ b` for `a, b ∈ s`. -/
def offDiagonal : Finset (α × α) :=
  .mk (Quotient.map List.offDiagonal (fun _ _ ↦ List.Perm.offDiagonal) s.1) <| by
    rcases s with ⟨⟨s⟩, hs⟩
    exact hs.offDiagonal

@[deprecated (since := "2026-09-06")] alias offDiag := offDiagonal

variable {s} {x : α × α}

@[simp, grind =]
theorem mem_diagonal : x ∈ s.diagonal ↔ x.1 ∈ s ∧ x.1 = x.2 := by
  aesop (add simp diagonal)

@[deprecated (since := "2026-09-06")] alias mem_diag := mem_diagonal

@[simp, grind =]
theorem mem_offDiagonal : x ∈ s.offDiagonal ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 := by
  rcases s with ⟨⟨s⟩, hs⟩
  exact hs.mem_offDiagonal

@[deprecated (since := "2026-09-06")] alias mem_offDiag := mem_offDiagonal

@[simp, grind =]
theorem diagonal_nonempty : s.diagonal.Nonempty ↔ s.Nonempty := by
  simp [diagonal]

@[deprecated (since := "2026-09-06")] alias diag_nonempty := diagonal_nonempty

@[simp, grind =]
theorem diagonal_eq_empty : s.diagonal = ∅ ↔ s = ∅ := by
  simp [diagonal]

@[deprecated (since := "2026-09-06")] alias diag_eq_empty := diagonal_eq_empty

theorem diagonal_eq_filter [DecidableEq α] :
    s.diagonal = (s ×ˢ s).filter fun a : α × α => a.fst = a.snd := by
  ext; simp +contextual

@[deprecated (since := "2026-09-06")] alias diag_eq_filter := diagonal_eq_filter

variable (s)

@[simp]
theorem image_diagonal [DecidableEq β] (f : α × α → β) (s : Finset α) :
    s.diagonal.image f = s.image fun x ↦ f (x, x) := by
  grind

@[deprecated (since := "2026-09-06")] alias image_diag := image_diagonal

@[simp, norm_cast]
theorem coe_offDiagonal : (s.offDiagonal : Set (α × α)) = (s : Set α).offDiagonal :=
  Set.ext fun _ => mem_offDiagonal

@[deprecated (since := "2026-09-06")] alias coe_offDiag := coe_offDiagonal

@[simp]
theorem diagonal_card : (diagonal s).card = s.card := by
  simp [diagonal]

@[deprecated (since := "2026-09-06")] alias diag_card := diagonal_card

@[simp]
theorem offDiagonal_card : (offDiagonal s).card = s.card * s.card - s.card := by
  rw [← sq]
  rcases s with ⟨⟨s⟩, hs⟩
  apply List.length_offDiagonal

@[deprecated (since := "2026-09-06")] alias offDiag_card := offDiagonal_card

@[gcongr, mono]
theorem diagonal_mono : Monotone (diagonal : Finset α → Finset (α × α)) :=
  fun _ _ ↦ by simp [diagonal]

@[deprecated (since := "2026-09-06")] alias diag_mono := diagonal_mono

@[gcongr, mono]
theorem offDiagonal_mono : Monotone (offDiagonal : Finset α → Finset (α × α)) := fun _ _ h _ hx =>
  mem_offDiagonal.2 <| And.imp (@h _) (And.imp_left <| @h _) <| mem_offDiagonal.1 hx

@[deprecated (since := "2026-09-06")] alias offDiag_mono := offDiagonal_mono

@[simp]
theorem diagonal_empty : (∅ : Finset α).diagonal = ∅ :=
  rfl

@[deprecated (since := "2026-09-06")] alias diag_empty := diagonal_empty

@[simp]
theorem offDiagonal_empty : (∅ : Finset α).offDiagonal = ∅ :=
  rfl

@[deprecated (since := "2026-09-06")] alias offDiag_empty := offDiagonal_empty

@[simp]
theorem diagonal_union_offDiagonal [DecidableEq α] : s.diagonal ∪ s.offDiagonal = s ×ˢ s := by
  grind

@[deprecated (since := "2026-09-06")] alias diag_union_offDiag := diagonal_union_offDiagonal

@[simp]
theorem disjoint_diagonal_offDiagonal : Disjoint s.diagonal s.offDiagonal := by simp [disjoint_left]

@[deprecated (since := "2026-09-06")] alias disjoint_diag_offDiag := disjoint_diagonal_offDiagonal

theorem product_sdiff_diagonal [DecidableEq α] : s ×ˢ s \ s.diagonal = s.offDiagonal := by grind

@[deprecated (since := "2026-09-06")] alias product_sdiff_diag := product_sdiff_diagonal

theorem product_sdiff_offDiagonal [DecidableEq α] : s ×ˢ s \ s.offDiagonal = s.diagonal := by grind

@[deprecated (since := "2026-09-06")] alias product_sdiff_offDiag := product_sdiff_offDiagonal

theorem diagonal_inter [DecidableEq α] : (s ∩ t).diagonal = s.diagonal ∩ t.diagonal := by
  grind

@[deprecated (since := "2026-09-06")] alias diag_inter := diagonal_inter

theorem offDiagonal_inter [DecidableEq α] : (s ∩ t).offDiagonal = s.offDiagonal ∩ t.offDiagonal :=
  coe_injective <| by
    push_cast
    exact Set.offDiagonal_inter _ _

@[deprecated (since := "2026-09-06")] alias offDiag_inter := offDiagonal_inter

theorem diagonal_union [DecidableEq α] : (s ∪ t).diagonal = s.diagonal ∪ t.diagonal := by
  grind

@[deprecated (since := "2026-09-06")] alias diag_union := diagonal_union

variable {s t}

theorem offDiagonal_union [DecidableEq α] (h : Disjoint s t) :
    (s ∪ t).offDiagonal = s.offDiagonal ∪ t.offDiagonal ∪ s ×ˢ t ∪ t ×ˢ s :=
  coe_injective <| by
    push_cast
    exact Set.offDiagonal_union (disjoint_coe.2 h)

@[deprecated (since := "2026-09-06")] alias offDiag_union := offDiagonal_union

@[simp]
theorem offDiagonal_singleton (a : α) : ({a} : Finset α).offDiagonal = ∅ := by
  simp [← Finset.card_eq_zero]

@[deprecated (since := "2026-09-06")] alias offDiag_singleton := offDiagonal_singleton

theorem diagonal_singleton (a : α) : ({a} : Finset α).diagonal = {(a, a)} := by grind

@[deprecated (since := "2026-09-06")] alias diag_singleton := diagonal_singleton

theorem diagonal_insert [DecidableEq α] (a : α) :
    (insert a s).diagonal = insert (a, a) s.diagonal := by grind

@[deprecated (since := "2026-09-06")] alias diag_insert := diagonal_insert

theorem offDiagonal_insert [DecidableEq α] {a : α} (has : a ∉ s) :
    (insert a s).offDiagonal = s.offDiagonal ∪ {a} ×ˢ s ∪ s ×ˢ {a} := by
  grind

@[deprecated (since := "2026-09-06")] alias offDiag_insert := offDiagonal_insert

theorem offDiagonal_filter_lt_eq_filter_le {ι} [PartialOrder ι] [DecidableLE ι] [DecidableLT ι]
    (s : Finset ι) :
    s.offDiagonal.filter (fun i => i.1 < i.2) = s.offDiagonal.filter (fun i => i.1 ≤ i.2) := by
  ext
  simpa using fun _ _ a ↦ (Ne.le_iff_lt a).symm

@[deprecated (since := "2026-09-06")]
alias offDiag_filter_lt_eq_filter_le := offDiagonal_filter_lt_eq_filter_le

/-- The number of strictly ordered pairs `(a, b)` with `a, b ∈ s` is `(#s).choose 2`. -/
lemma card_product_filter_lt [LinearOrder α] :
    #{x ∈ s ×ˢ s | x.1 < x.2} = (#s).choose 2 := by
  set u : Finset (α × α) := {x ∈ s ×ˢ s | x.1 < x.2}
  set v : Finset (α × α) := {x ∈ s ×ˢ s | x.2 < x.1}
  have disj : Disjoint u v := by grind [disjoint_left]
  have union : u.disjUnion v disj = s.offDiagonal := by grind
  have swap : #u = #v := Finset.card_equiv (Equiv.prodComm α α) (by grind)
  grind [Nat.mul_sub_one, offDiagonal_card, Nat.choose_two_right]

end Diagonal

end Finset
