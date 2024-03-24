import Mathlib.Data.Finset.Prod
import Mathlib.Data.Sym2.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Prod

open Finset

namespace Sym2

variable {α : Type*} [DecidableEq α]

theorem filter_image_mk_isDiag (s : Finset α) :
    ((s ×ˢ s).image Sym2.mk).filter IsDiag = s.diag.image Sym2.mk := by
  simp_rw [Finset.filter_image, isDiag_iff_proj_eq, Finset.filter_eq_product_eq_diag]
#align sym2.filter_image_quotient_mk_is_diag Sym2.filter_image_mk_isDiag

theorem filter_image_mk_not_isDiag (s : Finset α) :
    (((s ×ˢ s).image Sym2.mk).filter fun a : Sym2 α => ¬a.IsDiag) =
      s.offDiag.image Sym2.mk := by
  simp_rw [Finset.filter_image, isDiag_iff_proj_eq, Finset.offDiag]
#align sym2.filter_image_quotient_mk_not_is_diag Sym2.filter_image_mk_not_isDiag

/-- The `diag` of `s : Finset α` is sent on a finset of `Sym2 α` of card `s.card`. -/
theorem card_image_diag (s : Finset α) : (s.diag.image Sym2.mk).card = s.card := by
  rw [card_image_of_injOn, card_diag]
  rintro ⟨x₀, x₁⟩ hx _ _ h
  cases Sym2.eq.1 h
  · rfl
  · simp only [mem_coe, mem_diag] at hx
    rw [hx.2]
#align sym2.card_image_diag Sym2.card_image_diag

theorem two_mul_card_image_offDiag (s : Finset α) :
    2 * (s.offDiag.image Sym2.mk).card = s.offDiag.card := by
  rw [card_eq_sum_card_image (Sym2.mk : α × α → _), sum_const_nat (Sym2.ind _), mul_comm]
  rintro x y hxy
  simp_rw [mem_image, mem_offDiag] at hxy
  obtain ⟨a, ⟨ha₁, ha₂, ha⟩, h⟩ := hxy
  replace h := Sym2.eq.1 h
  obtain ⟨hx, hy, hxy⟩ : x ∈ s ∧ y ∈ s ∧ x ≠ y := by
    cases h <;> refine' ⟨‹_›, ‹_›, _⟩ <;> [exact ha; exact ha.symm]
  have hxy' : y ≠ x := hxy.symm
  have : (s.offDiag.filter fun z => Sym2.mk z = s(x, y)) = ({(x, y), (y, x)} : Finset _) := by
    ext ⟨x₁, y₁⟩
    rw [mem_filter, mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.inj_iff, Prod.mk.inj_iff,
      and_iff_right_iff_imp]
    -- `hxy'` is used in `exact`
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rw [mem_offDiag] <;> exact ⟨‹_›, ‹_›, ‹_›⟩
  rw [this, card_insert_of_not_mem, card_singleton]
  simp only [not_and, Prod.mk.inj_iff, mem_singleton]
  exact fun _ => hxy'
#align sym2.two_mul_card_image_off_diag Sym2.two_mul_card_image_offDiag

/-- The `offDiag` of `s : Finset α` is sent on a finset of `Sym2 α` of card `s.offDiag.card / 2`.
This is because every element `s(x, y)` of `Sym2 α` not on the diagonal comes from exactly two
pairs: `(x, y)` and `(y, x)`. -/
theorem card_image_offDiag (s : Finset α) :
    (s.offDiag.image Sym2.mk).card = s.card.choose 2 := by
  rw [Nat.choose_two_right, mul_tsub, mul_one, ← card_offDiag,
    Nat.div_eq_of_eq_mul_right zero_lt_two (two_mul_card_image_offDiag s).symm]
#align sym2.card_image_off_diag Sym2.card_image_offDiag

theorem card_subtype_diag [Fintype α] : Fintype.card { a : Sym2 α // a.IsDiag } = card α := by
  convert card_image_diag (univ : Finset α)
  rw [← filter_image_mk_isDiag, Fintype.card_of_subtype]
  rintro x
  rw [mem_filter, univ_product_univ, mem_image]
  obtain ⟨a, ha⟩ := Quot.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩
#align sym2.card_subtype_diag Sym2.card_subtype_diag

theorem card_subtype_not_diag [Fintype α] :
    card { a : Sym2 α // ¬a.IsDiag } = (card α).choose 2 := by
  convert card_image_offDiag (univ : Finset α)
  rw [← filter_image_mk_not_isDiag, Fintype.card_of_subtype]
  rintro x
  rw [mem_filter, univ_product_univ, mem_image]
  obtain ⟨a, ha⟩ := Quot.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩
#align sym2.card_subtype_not_diag Sym2.card_subtype_not_diag

/-- Type **stars and bars** for the case `n = 2`. -/
protected theorem card [Fintype α] : card (Sym2 α) = Nat.choose (card α + 1) 2 :=
  Finset.card_sym2 _
#align sym2.card Sym2.card

end Sym2
