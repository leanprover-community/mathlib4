/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathlib.Order.WellFoundedSet

#align_import data.set.mul_antidiagonal from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-! # Multiplication antidiagonal -/


namespace Set

variable {α : Type*}

section Mul

variable [Mul α] {s s₁ s₂ t t₁ t₂ : Set α} {a : α} {x : α × α}

/-- `Set.mulAntidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
that multiply to `a`. -/
@[to_additive
      "`Set.addAntidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that add to `a`."]
def mulAntidiagonal (s t : Set α) (a : α) : Set (α × α) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a }
#align set.mul_antidiagonal Set.mulAntidiagonal
#align set.add_antidiagonal Set.addAntidiagonal

@[to_additive (attr := simp)]
theorem mem_mulAntidiagonal : x ∈ mulAntidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a :=
  Iff.rfl
#align set.mem_mul_antidiagonal Set.mem_mulAntidiagonal
#align set.mem_add_antidiagonal Set.mem_addAntidiagonal

@[to_additive]
theorem mulAntidiagonal_mono_left (h : s₁ ⊆ s₂) : mulAntidiagonal s₁ t a ⊆ mulAntidiagonal s₂ t a :=
  fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩
#align set.mul_antidiagonal_mono_left Set.mulAntidiagonal_mono_left
#align set.add_antidiagonal_mono_left Set.addAntidiagonal_mono_left

@[to_additive]
theorem mulAntidiagonal_mono_right (h : t₁ ⊆ t₂) :
    mulAntidiagonal s t₁ a ⊆ mulAntidiagonal s t₂ a := fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩
#align set.mul_antidiagonal_mono_right Set.mulAntidiagonal_mono_right
#align set.add_antidiagonal_mono_right Set.addAntidiagonal_mono_right

end Mul

-- Porting note: Removed simp attribute, simpnf linter can simplify lhs. Added aux version below
@[to_additive]
theorem swap_mem_mulAntidiagonal [CommSemigroup α] {s t : Set α} {a : α} {x : α × α} :
    x.swap ∈ Set.mulAntidiagonal s t a ↔ x ∈ Set.mulAntidiagonal t s a := by
  simp [mul_comm, and_left_comm]
  -- 🎉 no goals
#align set.swap_mem_mul_antidiagonal Set.swap_mem_mulAntidiagonal
#align set.swap_mem_add_antidiagonal Set.swap_mem_addAntidiagonal

@[to_additive (attr := simp)]
theorem swap_mem_mulAntidiagonal_aux [CommSemigroup α] {s t : Set α} {a : α} {x : α × α} :
     x.snd ∈ s ∧ x.fst ∈ t ∧ x.snd * x.fst = a
      ↔ x ∈ Set.mulAntidiagonal t s a := by
  simp [mul_comm, and_left_comm]
  -- 🎉 no goals


namespace MulAntidiagonal

section CancelCommMonoid

variable [CancelCommMonoid α] {s t : Set α} {a : α} {x y : mulAntidiagonal s t a}

-- Porting note: to_additive cannot translate the "Mul" in "MulAntidiagonal" by itself here
@[to_additive Set.AddAntidiagonal.fst_eq_fst_iff_snd_eq_snd]
theorem fst_eq_fst_iff_snd_eq_snd : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2 :=
  ⟨fun h =>
    mul_left_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          -- ⊢ a = (↑x).fst * (↑x).snd
          exact x.2.2.2.symm).symm,
          -- 🎉 no goals
    fun h =>
    mul_right_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          -- ⊢ a = (↑x).fst * (↑x).snd
          exact x.2.2.2.symm).symm⟩
          -- 🎉 no goals
#align set.mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd Set.MulAntidiagonal.fst_eq_fst_iff_snd_eq_snd
#align set.add_antidiagonal.fst_eq_fst_iff_snd_eq_snd Set.AddAntidiagonal.fst_eq_fst_iff_snd_eq_snd

@[to_additive Set.AddAntidiagonal.eq_of_fst_eq_fst]
theorem eq_of_fst_eq_fst (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| fst_eq_fst_iff_snd_eq_snd.1 h
#align set.mul_antidiagonal.eq_of_fst_eq_fst Set.MulAntidiagonal.eq_of_fst_eq_fst
#align set.add_antidiagonal.eq_of_fst_eq_fst Set.AddAntidiagonal.eq_of_fst_eq_fst

@[to_additive Set.AddAntidiagonal.eq_of_snd_eq_snd]
theorem eq_of_snd_eq_snd (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h
#align set.mul_antidiagonal.eq_of_snd_eq_snd Set.MulAntidiagonal.eq_of_snd_eq_snd
#align set.add_antidiagonal.eq_of_snd_eq_snd Set.AddAntidiagonal.eq_of_snd_eq_snd

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] (s t : Set α) (a : α) {x y : mulAntidiagonal s t a}

@[to_additive Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd]
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : α × α).1 ≤ (y : α × α).1)
    (h₂ : (x : α × α).2 ≤ (y : α × α).2) : x = y :=
  eq_of_fst_eq_fst <|
    h₁.eq_of_not_lt fun hlt =>
      (mul_lt_mul_of_lt_of_le hlt h₂).ne <|
        (mem_mulAntidiagonal.1 x.2).2.2.trans (mem_mulAntidiagonal.1 y.2).2.2.symm
#align set.mul_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd
#align set.add_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd

variable {s t}

@[to_additive Set.AddAntidiagonal.finite_of_isPwo]
theorem finite_of_isPwo (hs : s.IsPwo) (ht : t.IsPwo) (a) : (mulAntidiagonal s t a).Finite := by
  refine' not_infinite.1 fun h => _
  -- ⊢ False
  have h1 : (mulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) := fun f hf =>
    hs (Prod.fst ∘ f) fun n => (mem_mulAntidiagonal.1 (hf n)).1
  have h2 : (mulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) := fun f hf =>
    ht (Prod.snd ∘ f) fun n => (mem_mulAntidiagonal.1 (hf n)).2.1
  obtain ⟨g, hg⟩ :=
    h1.exists_monotone_subseq (fun n => h.natEmbedding _ n) fun n => (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 (fun x => (h.natEmbedding _) (g x)) fun n => (h.natEmbedding _ _).2
  -- ⊢ False
  refine' mn.ne (g.injective <| (h.natEmbedding _).injective _)
  -- ⊢ ↑(Infinite.natEmbedding (mulAntidiagonal s t a) h) (↑g m) = ↑(Infinite.natEm …
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ mn.le) h2'
  -- 🎉 no goals
#align set.mul_antidiagonal.finite_of_is_pwo Set.MulAntidiagonal.finite_of_isPwo
#align set.add_antidiagonal.finite_of_is_pwo Set.AddAntidiagonal.finite_of_isPwo

end OrderedCancelCommMonoid

@[to_additive Set.AddAntidiagonal.finite_of_isWf]
theorem finite_of_isWf [LinearOrderedCancelCommMonoid α] {s t : Set α} (hs : s.IsWf) (ht : t.IsWf)
    (a) : (mulAntidiagonal s t a).Finite :=
  finite_of_isPwo hs.isPwo ht.isPwo a
#align set.mul_antidiagonal.finite_of_is_wf Set.MulAntidiagonal.finite_of_isWf
#align set.add_antidiagonal.finite_of_is_wf Set.AddAntidiagonal.finite_of_isWf

end MulAntidiagonal

end Set
