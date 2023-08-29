/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Huỳnh Trần Khanh, Stuart Presnell
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Sum

#align_import data.sym.card from "leanprover-community/mathlib"@"0bd2ea37bcba5769e14866170f251c9bc64e35d7"

/-!
# Stars and bars

In this file, we prove (in `Sym.card_sym_eq_multichoose`) that the function `multichoose n k`
defined in `Data/Nat/Choose/Basic` counts the number of multisets of cardinality `k` over an
alphabet of cardinality `n`. In conjunction with `Nat.multichoose_eq` proved in
`Data/Nat/Choose/Basic`, which shows that `multichoose n k = choose (n + k - 1) k`,
this is central to the "stars and bars" technique in combinatorics, where we switch between
counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
("stars") separated by `n-1` dividers ("bars").

## Informal statement

Many problems in mathematics are of the form of (or can be reduced to) putting `k` indistinguishable
objects into `n` distinguishable boxes; for example, the problem of finding natural numbers
`x1, ..., xn` whose sum is `k`. This is equivalent to forming a multiset of cardinality `k` from
an alphabet of cardinality `n` -- for each box `i ∈ [1, n]` the multiset contains as many copies
of `i` as there are items in the `i`th box.

The "stars and bars" technique arises from another way of presenting the same problem. Instead of
putting `k` items into `n` boxes, we take a row of `k` items (the "stars") and separate them by
inserting `n-1` dividers (the "bars").  For example, the pattern `*|||**|*|` exhibits 4 items
distributed into 6 boxes -- note that any box, including the first and last, may be empty.
Such arrangements of `k` stars and `n-1` bars are in 1-1 correspondence with multisets of size `k`
over an alphabet of size `n`, and are counted by `choose (n + k - 1) k`.

Note that this problem is one component of Gian-Carlo Rota's "Twelvefold Way"
https://en.wikipedia.org/wiki/Twelvefold_way

## Formal statement

Here we generalise the alphabet to an arbitrary fintype `α`, and we use `Sym α k` as the type of
multisets of size `k` over `α`. Thus the statement that these are counted by `multichoose` is:
`Sym.card_sym_eq_multichoose : card (Sym α k) = multichoose (card α) k`
while the "stars and bars" technique gives
`Sym.card_sym_eq_choose : card (Sym α k) = choose (card α + k - 1) k`


## Tags

stars and bars, multichoose
-/


open Finset Fintype Function Sum Nat

variable {α β : Type*}

namespace Sym

section Sym

variable (α) (n : ℕ)

/-- Over `Fin (n + 1)`, the multisets of size `k + 1` containing `0` are equivalent to those of size
`k`, as demonstrated by respectively erasing or appending `0`. -/
protected def e1 {n k : ℕ} : { s : Sym (Fin (n + 1)) (k + 1) // ↑0 ∈ s } ≃ Sym (Fin n.succ) k where
  toFun s := s.1.erase 0 s.2
  invFun s := ⟨cons 0 s, mem_cons_self 0 s⟩
  left_inv s := by simp
                   -- 🎉 no goals
  right_inv s := by simp
                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align sym.E1 Sym.e1

/-- The multisets of size `k` over `Fin n+2` not containing `0`
are equivalent to those of size `k` over `Fin n+1`,
as demonstrated by respectively decrementing or incrementing every element of the multiset.
-/
protected def e2 {n k : ℕ} : { s : Sym (Fin n.succ.succ) k // ↑0 ∉ s } ≃ Sym (Fin n.succ) k where
  toFun s := map (Fin.predAbove 0) s.1
  invFun s :=
    ⟨map (Fin.succAbove 0) s,
      (mt mem_map.1) (not_exists.2 fun t => not_and.2 fun _ => Fin.succAbove_ne _ t)⟩
  left_inv s := by
    ext1
    -- ⊢ ↑((fun s => { val := map (Fin.succAbove 0) s, property := (_ : ¬0 ∈ map (Fin …
    simp only [map_map]
    -- ⊢ map (Fin.succAbove 0 ∘ Fin.predAbove 0) ↑s = ↑s
    refine (Sym.map_congr fun v hv ↦ ?_).trans (map_id' _)
    -- ⊢ (Fin.succAbove 0 ∘ Fin.predAbove 0) v = v
    exact Fin.succAbove_predAbove (ne_of_mem_of_not_mem hv s.2)
    -- 🎉 no goals
  right_inv s := by
    simp only [map_map, comp_apply, ← Fin.castSucc_zero, Fin.predAbove_succAbove, map_id']
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align sym.E2 Sym.e2

-- porting note: use eqn compiler instead of `pincerRecursion` to make cases more readable
theorem card_sym_fin_eq_multichoose : ∀ n k : ℕ, card (Sym (Fin n) k) = multichoose n k
  | n, 0 => by simp
               -- 🎉 no goals
  | 0, k + 1 => by rw [multichoose_zero_succ]; exact card_eq_zero
                   -- ⊢ Fintype.card (Sym (Fin 0) (k + 1)) = 0
                                               -- 🎉 no goals
  | 1, k + 1 => by simp
                   -- 🎉 no goals
  | n + 2, k + 1 => by
    rw [multichoose_succ_succ, ← card_sym_fin_eq_multichoose (n + 1) (k + 1),
      ← card_sym_fin_eq_multichoose (n + 2) k, add_comm (Fintype.card _), ← card_sum]
    refine Fintype.card_congr (Equiv.symm ?_)
    -- ⊢ Sym (Fin (n + 2)) k ⊕ Sym (Fin (n + 1)) (k + 1) ≃ Sym (Fin (n + 2)) (k + 1)
    apply (Sym.e1.symm.sumCongr Sym.e2.symm).trans
    -- ⊢ { s // 0 ∈ s } ⊕ { s // ¬0 ∈ s } ≃ Sym (Fin (n + 2)) (k + 1)
    apply Equiv.sumCompl
    -- 🎉 no goals
  termination_by card_sym_fin_eq_multichoose n k => n + k
#align sym.card_sym_fin_eq_multichoose Sym.card_sym_fin_eq_multichoose

/-- For any fintype `α` of cardinality `n`, `card (Sym α k) = multichoose (card α) k`. -/
theorem card_sym_eq_multichoose (α : Type*) (k : ℕ) [Fintype α] [Fintype (Sym α k)] :
    card (Sym α k) = multichoose (card α) k := by
  rw [← card_sym_fin_eq_multichoose]
  -- ⊢ Fintype.card (Sym α k) = Fintype.card (Sym (Fin (Fintype.card α)) k)
  exact card_congr (equivCongr (equivFin α))
  -- 🎉 no goals
#align sym.card_sym_eq_multichoose Sym.card_sym_eq_multichoose

/-- The *stars and bars* lemma: the cardinality of `Sym α k` is equal to
`Nat.choose (card α + k - 1) k`. -/
theorem card_sym_eq_choose {α : Type*} [Fintype α] (k : ℕ) [Fintype (Sym α k)] :
    card (Sym α k) = (card α + k - 1).choose k := by
  rw [card_sym_eq_multichoose, Nat.multichoose_eq]
  -- 🎉 no goals
#align sym.card_sym_eq_choose Sym.card_sym_eq_choose

end Sym

end Sym

namespace Sym2

variable [DecidableEq α]

/-- The `diag` of `s : Finset α` is sent on a finset of `Sym2 α` of card `s.card`. -/
theorem card_image_diag (s : Finset α) : (s.diag.image Quotient.mk').card = s.card := by
  rw [card_image_of_injOn, diag_card]
  -- ⊢ Set.InjOn Quotient.mk' ↑(Finset.diag s)
  rintro ⟨x₀, x₁⟩ hx _ _ h
  -- ⊢ (x₀, x₁) = x₂✝
  cases Quotient.eq'.1 h
  -- ⊢ (x₀, x₁) = (x₀, x₁)
  · rfl
    -- 🎉 no goals
  · simp only [mem_coe, mem_diag] at hx
    -- ⊢ (x₀, x₁) = (x₁, x₀)
    rw [hx.2]
    -- 🎉 no goals
#align sym2.card_image_diag Sym2.card_image_diag

theorem two_mul_card_image_offDiag (s : Finset α) :
    2 * (s.offDiag.image Quotient.mk').card = s.offDiag.card := by
  rw [card_eq_sum_card_image (Quotient.mk' : α × α → _), sum_const_nat (Quotient.ind' _), mul_comm]
  -- ⊢ ∀ (a : α × α), Quotient.mk'' a ∈ image Quotient.mk' (offDiag s) → Finset.car …
  rintro ⟨x, y⟩ hxy
  -- ⊢ Finset.card (filter (fun x_1 => Quotient.mk' x_1 = Quotient.mk'' (x, y)) (of …
  simp_rw [mem_image, mem_offDiag] at hxy
  -- ⊢ Finset.card (filter (fun x_1 => Quotient.mk' x_1 = Quotient.mk'' (x, y)) (of …
  obtain ⟨a, ⟨ha₁, ha₂, ha⟩, h⟩ := hxy
  -- ⊢ Finset.card (filter (fun x_1 => Quotient.mk' x_1 = Quotient.mk'' (x, y)) (of …
  replace h := Quotient.eq.1 h
  -- ⊢ Finset.card (filter (fun x_1 => Quotient.mk' x_1 = Quotient.mk'' (x, y)) (of …
  obtain ⟨hx, hy, hxy⟩ : x ∈ s ∧ y ∈ s ∧ x ≠ y := by
    cases h <;> refine' ⟨‹_›, ‹_›, _⟩ <;> [exact ha; exact ha.symm]
  have hxy' : y ≠ x := hxy.symm
  -- ⊢ Finset.card (filter (fun x_1 => Quotient.mk' x_1 = Quotient.mk'' (x, y)) (of …
  have : (s.offDiag.filter fun z => ⟦z⟧ = ⟦(x, y)⟧) = ({(x, y), (y, x)} : Finset _) := by
    ext ⟨x₁, y₁⟩
    rw [mem_filter, mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.inj_iff, Prod.mk.inj_iff,
      and_iff_right_iff_imp]
    -- `hxy'` is used in `exact`
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rw [mem_offDiag] <;> exact ⟨‹_›, ‹_›, ‹_›⟩
  dsimp [Quotient.mk', Quotient.mk''_eq_mk] -- Porting note: Added `dsimp`
  -- ⊢ Finset.card (filter (fun x_1 => Quotient.mk (Rel.setoid α) x_1 = Quotient.mk …
  rw [this, card_insert_of_not_mem, card_singleton]
  -- ⊢ ¬(x, y) ∈ {(y, x)}
  simp only [not_and, Prod.mk.inj_iff, mem_singleton]
  -- ⊢ x = y → ¬y = x
  exact fun _ => hxy'
  -- 🎉 no goals
#align sym2.two_mul_card_image_off_diag Sym2.two_mul_card_image_offDiag

/-- The `offDiag` of `s : Finset α` is sent on a finset of `Sym2 α` of card `s.offDiag.card / 2`.
This is because every element `⟦(x, y)⟧` of `Sym2 α` not on the diagonal comes from exactly two
pairs: `(x, y)` and `(y, x)`. -/
theorem card_image_offDiag (s : Finset α) :
    (s.offDiag.image Quotient.mk').card = s.card.choose 2 := by
  rw [Nat.choose_two_right, mul_tsub, mul_one, ← offDiag_card,
    Nat.div_eq_of_eq_mul_right zero_lt_two (two_mul_card_image_offDiag s).symm]
#align sym2.card_image_off_diag Sym2.card_image_offDiag

theorem card_subtype_diag [Fintype α] : card { a : Sym2 α // a.IsDiag } = card α := by
  convert card_image_diag (univ : Finset α)
  -- ⊢ Fintype.card { a // IsDiag a } = Finset.card (image Quotient.mk' (Finset.dia …
  simp_rw [Quotient.mk', ← Quotient.mk''_eq_mk] -- Porting note: Added `simp_rw`
  -- ⊢ Fintype.card { a // IsDiag a } = Finset.card (image (fun a => Quotient.mk''  …
  rw [Fintype.card_of_subtype, ← filter_image_quotient_mk''_isDiag]
  -- ⊢ ∀ (x : Sym2 α), x ∈ filter IsDiag (image Quotient.mk'' (univ ×ˢ univ)) ↔ IsD …
  rintro x
  -- ⊢ x ∈ filter IsDiag (image Quotient.mk'' (univ ×ˢ univ)) ↔ IsDiag x
  rw [mem_filter, univ_product_univ, mem_image]
  -- ⊢ (∃ a, a ∈ univ ∧ Quotient.mk'' a = x) ∧ IsDiag x ↔ IsDiag x
  obtain ⟨a, ha⟩ := Quotient.exists_rep x
  -- ⊢ (∃ a, a ∈ univ ∧ Quotient.mk'' a = x) ∧ IsDiag x ↔ IsDiag x
  exact and_iff_right ⟨a, mem_univ _, ha⟩
  -- 🎉 no goals
#align sym2.card_subtype_diag Sym2.card_subtype_diag

theorem card_subtype_not_diag [Fintype α] :
    card { a : Sym2 α // ¬a.IsDiag } = (card α).choose 2 := by
  convert card_image_offDiag (univ : Finset α)
  -- ⊢ Fintype.card { a // ¬IsDiag a } = Finset.card (image Quotient.mk' (offDiag u …
  simp_rw [Quotient.mk', ← Quotient.mk''_eq_mk] -- Porting note: Added `simp_rw`
  -- ⊢ Fintype.card { a // ¬IsDiag a } = Finset.card (image (fun a => Quotient.mk'' …
  rw [Fintype.card_of_subtype, ← filter_image_quotient_mk''_not_isDiag]
  -- ⊢ ∀ (x : Sym2 α), x ∈ filter (fun a => ¬IsDiag a) (image Quotient.mk'' (univ × …
  rintro x
  -- ⊢ x ∈ filter (fun a => ¬IsDiag a) (image Quotient.mk'' (univ ×ˢ univ)) ↔ ¬IsDi …
  rw [mem_filter, univ_product_univ, mem_image]
  -- ⊢ (∃ a, a ∈ univ ∧ Quotient.mk'' a = x) ∧ ¬IsDiag x ↔ ¬IsDiag x
  obtain ⟨a, ha⟩ := Quotient.exists_rep x
  -- ⊢ (∃ a, a ∈ univ ∧ Quotient.mk'' a = x) ∧ ¬IsDiag x ↔ ¬IsDiag x
  exact and_iff_right ⟨a, mem_univ _, ha⟩
  -- 🎉 no goals
#align sym2.card_subtype_not_diag Sym2.card_subtype_not_diag

/-- Finset **stars and bars** for the case `n = 2`. -/
theorem _root_.Finset.card_sym2 (s : Finset α) : s.sym2.card = s.card * (s.card + 1) / 2 := by
  rw [← image_diag_union_image_offDiag, card_union_eq, Sym2.card_image_diag,
    Sym2.card_image_offDiag, Nat.choose_two_right, add_comm, ← Nat.triangle_succ, Nat.succ_sub_one,
    mul_comm]
  rw [disjoint_left]
  -- ⊢ ∀ ⦃a : Quotient (Rel.setoid α)⦄, a ∈ image Quotient.mk' (Finset.diag s) → ¬a …
  rintro m ha hb
  -- ⊢ False
  rw [mem_image] at ha hb
  -- ⊢ False
  obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩ := ha, hb
  -- ⊢ False
  refine' not_isDiag_mk'_of_mem_offDiag hb _
  -- ⊢ IsDiag (Quotient.mk (Rel.setoid α) b)
  dsimp [Quotient.mk'] at hab -- Porting note: Added `dsimp`
  -- ⊢ IsDiag (Quotient.mk (Rel.setoid α) b)
  rw [hab]
  -- ⊢ IsDiag (Quotient.mk (Rel.setoid α) a)
  exact isDiag_mk'_of_mem_diag ha
  -- 🎉 no goals
#align finset.card_sym2 Finset.card_sym2

/-- Type **stars and bars** for the case `n = 2`. -/
protected theorem card [Fintype α] : card (Sym2 α) = card α * (card α + 1) / 2 :=
  Finset.card_sym2 _
#align sym2.card Sym2.card

end Sym2
