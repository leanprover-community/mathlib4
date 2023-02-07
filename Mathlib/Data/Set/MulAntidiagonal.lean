/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn

! This file was ported from Lean 3 source module data.set.mul_antidiagonal
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.WellFoundedSet

/-! # Multiplication antidiagonal -/


namespace Set

variable {α : Type _}

section Mul

variable [Mul α] {s s₁ s₂ t t₁ t₂ : Set α} {a : α} {x : α × α}

/-- `set.mul_antidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
that multiply to `a`. -/
@[to_additive
      "`set.add_antidiagonal s t a` is the set of all pairs of an element in `s` and an\nelement in `t` that add to `a`."]
def mulAntidiagonal (s t : Set α) (a : α) : Set (α × α) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a }
#align set.mul_antidiagonal Set.mulAntidiagonal
#align set.add_antidiagonal Set.addAntidiagonal

@[simp, to_additive]
theorem mem_mulAntidiagonal : x ∈ mulAntidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a :=
  Iff.rfl
#align set.mem_mul_antidiagonal Set.mem_mulAntidiagonal
#align set.mem_add_antidiagonal Set.mem_add_antidiagonal

@[to_additive]
theorem mulAntidiagonal_mono_left (h : s₁ ⊆ s₂) : mulAntidiagonal s₁ t a ⊆ mulAntidiagonal s₂ t a :=
  fun x hx => ⟨h hx.1, hx.2.1, hx.2.2⟩
#align set.mul_antidiagonal_mono_left Set.mulAntidiagonal_mono_left
#align set.add_antidiagonal_mono_left Set.add_antidiagonal_mono_left

@[to_additive]
theorem mulAntidiagonal_mono_right (h : t₁ ⊆ t₂) :
    mulAntidiagonal s t₁ a ⊆ mulAntidiagonal s t₂ a := fun x hx => ⟨hx.1, h hx.2.1, hx.2.2⟩
#align set.mul_antidiagonal_mono_right Set.mulAntidiagonal_mono_right
#align set.add_antidiagonal_mono_right Set.add_antidiagonal_mono_right

end Mul

@[simp, to_additive]
theorem swap_mem_mulAntidiagonal [CommSemigroup α] {s t : Set α} {a : α} {x : α × α} :
    x.symm ∈ Set.mulAntidiagonal s t a ↔ x ∈ Set.mulAntidiagonal t s a := by
  simp [mul_comm, and_left_comm]
#align set.swap_mem_mul_antidiagonal Set.swap_mem_mulAntidiagonal
#align set.swap_mem_add_antidiagonal Set.swap_mem_add_antidiagonal

namespace MulAntidiagonal

section CancelCommMonoid

variable [CancelCommMonoid α] {s t : Set α} {a : α} {x y : mulAntidiagonal s t a}

@[to_additive]
theorem fst_eq_fst_iff_snd_eq_snd : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2 :=
  ⟨fun h =>
    mul_left_cancel
      (y.Prop.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    mul_right_cancel
      (y.Prop.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩
#align set.mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd Set.mulAntidiagonal.fst_eq_fst_iff_snd_eq_snd
#align set.add_antidiagonal.fst_eq_fst_iff_snd_eq_snd Set.addAntidiagonal.fst_eq_fst_iff_snd_eq_snd

@[to_additive]
theorem eq_of_fst_eq_fst (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| fst_eq_fst_iff_snd_eq_snd.1 h
#align set.mul_antidiagonal.eq_of_fst_eq_fst Set.mulAntidiagonal.eq_of_fst_eq_fst
#align set.add_antidiagonal.eq_of_fst_eq_fst Set.addAntidiagonal.eq_of_fst_eq_fst

@[to_additive]
theorem eq_of_snd_eq_snd (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h
#align set.mul_antidiagonal.eq_of_snd_eq_snd Set.mulAntidiagonal.eq_of_snd_eq_snd
#align set.add_antidiagonal.eq_of_snd_eq_snd Set.addAntidiagonal.eq_of_snd_eq_snd

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] (s t : Set α) (a : α) {x y : mulAntidiagonal s t a}

@[to_additive]
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : α × α).1 ≤ (y : α × α).1)
    (h₂ : (x : α × α).2 ≤ (y : α × α).2) : x = y :=
  eq_of_fst_eq_fst <|
    h₁.eq_of_not_lt fun hlt =>
      (mul_lt_mul_of_lt_of_le hlt h₂).Ne <|
        (mem_mulAntidiagonal.1 x.2).2.2.trans (mem_mulAntidiagonal.1 y.2).2.2.symm
#align set.mul_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd Set.mulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd
#align set.add_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd Set.addAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd

variable {s t}

@[to_additive]
theorem finite_of_isPwo (hs : s.IsPwo) (ht : t.IsPwo) (a) : (mulAntidiagonal s t a).Finite :=
  by
  refine' not_infinite.1 fun h => _
  have h1 : (mul_antidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) := fun f hf =>
    hs (Prod.fst ∘ f) fun n => (mem_mul_antidiagonal.1 (hf n)).1
  have h2 : (mul_antidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) := fun f hf =>
    ht (Prod.snd ∘ f) fun n => (mem_mul_antidiagonal.1 (hf n)).2.1
  obtain ⟨g, hg⟩ :=
    h1.exists_monotone_subseq (fun n => h.nat_embedding _ n) fun n => (h.nat_embedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 (fun x => (h.nat_embedding _) (g x)) fun n => (h.nat_embedding _ _).2
  refine' mn.ne (g.injective <| (h.nat_embedding _).Injective _)
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ mn.le) h2'
#align set.mul_antidiagonal.finite_of_is_pwo Set.mulAntidiagonal.finite_of_isPwo
#align set.add_antidiagonal.finite_of_is_pwo Set.addAntidiagonal.finite_of_isPwo

end OrderedCancelCommMonoid

@[to_additive]
theorem finite_of_isWf [LinearOrderedCancelCommMonoid α] {s t : Set α} (hs : s.IsWf) (ht : t.IsWf)
    (a) : (mulAntidiagonal s t a).Finite :=
  finite_of_isPwo hs.IsPwo ht.IsPwo a
#align set.mul_antidiagonal.finite_of_is_wf Set.mulAntidiagonal.finite_of_isWf
#align set.add_antidiagonal.finite_of_is_wf Set.addAntidiagonal.finite_of_isWf

end MulAntidiagonal

end Set

