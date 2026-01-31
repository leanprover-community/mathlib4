/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
module

public import Mathlib.Order.WellFoundedSet

/-! # Multiplication antidiagonal -/

@[expose] public section


namespace Set

variable {α : Type*}

section Mul

variable [Mul α] {s s₁ s₂ t t₁ t₂ : Set α} {a : α} {x : α × α}

/-- `Set.setMulAntidiagonal s t a` is the set of all pairs of an element in `s` and an element
in `t` that multiply to `a`. -/
@[to_additive
      /-- `Set.setAddAntidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that add to `a`. -/]
def setMulAntidiagonal (s t : Set α) (a : α) : Set (α × α) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a }

@[to_additive (attr := deprecated setAddAntidiagonal (since := "2026-01-31")),
  deprecated setMulAntidiagonal (since := "2026-01-31")]
alias mulAntidiagonal := setMulAntidiagonal

@[to_additive (attr := simp)]
theorem mem_mulAntidiagonal : x ∈ setMulAntidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a :=
  Iff.rfl

@[to_additive]
theorem mulAntidiagonal_mono_left (h : s₁ ⊆ s₂) :
    setMulAntidiagonal s₁ t a ⊆ setMulAntidiagonal s₂ t a :=
  fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]
theorem mulAntidiagonal_mono_right (h : t₁ ⊆ t₂) :
    setMulAntidiagonal s t₁ a ⊆ setMulAntidiagonal s t₂ a := fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩

end Mul

-- The left-hand side is not in simp normal form, see variant below.
@[to_additive]
theorem swap_mem_mulAntidiagonal [CommMagma α] {s t : Set α} {a : α} {x : α × α} :
    x.swap ∈ Set.setMulAntidiagonal s t a ↔ x ∈ Set.setMulAntidiagonal t s a := by
  simp [mul_comm, and_left_comm]

@[to_additive (attr := simp)]
theorem swap_mem_mulAntidiagonal_aux [CommMagma α] {s t : Set α} {a : α} {x : α × α} :
    x.snd ∈ s ∧ x.fst ∈ t ∧ x.snd * x.fst = a
      ↔ x ∈ Set.setMulAntidiagonal t s a := by
  simp [mul_comm, and_left_comm]


namespace MulAntidiagonal

section CancelCommMonoid

variable [CommMonoid α] [IsCancelMul α] {s t : Set α} {a : α} {x y : setMulAntidiagonal s t a}

-- We have to translate the names manually because the namespace name `MulAntidiagonal`
-- does not match the declaration `mulAntidiagonal` that has the `to_additive` attribute.
@[to_additive Set.AddAntidiagonal.fst_eq_fst_iff_snd_eq_snd]
theorem fst_eq_fst_iff_snd_eq_snd : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2 :=
  ⟨fun h =>
    mul_left_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    mul_right_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive Set.AddAntidiagonal.eq_of_fst_eq_fst]
theorem eq_of_fst_eq_fst (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| fst_eq_fst_iff_snd_eq_snd.1 h

@[to_additive Set.AddAntidiagonal.eq_of_snd_eq_snd]
theorem eq_of_snd_eq_snd (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [CommMonoid α] [PartialOrder α] [IsCancelMul α] [MulLeftMono α] [MulRightStrictMono α]
  (s t : Set α) (a : α) {x y : setMulAntidiagonal s t a}

@[to_additive Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd]
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : α × α).1 ≤ (y : α × α).1)
    (h₂ : (x : α × α).2 ≤ (y : α × α).2) : x = y :=
  eq_of_fst_eq_fst <|
    h₁.eq_of_not_lt fun hlt =>
      (mul_lt_mul_of_lt_of_le hlt h₂).ne <|
        (mem_mulAntidiagonal.1 x.2).2.2.trans (mem_mulAntidiagonal.1 y.2).2.2.symm

variable {s t}

@[to_additive Set.AddAntidiagonal.finite_of_isPWO]
theorem finite_of_isPWO (hs : s.IsPWO) (ht : t.IsPWO) (a) : (setMulAntidiagonal s t a).Finite := by
  by_contra! h
  have h1 : (setMulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) :=
    fun f ↦ hs fun n ↦ ⟨_, (mem_mulAntidiagonal.1 (f n).2).1⟩
  have h2 : (setMulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) :=
    fun f ↦ ht fun n ↦ ⟨_, (mem_mulAntidiagonal.1 (f n).2).2.1⟩
  obtain ⟨g, hg⟩ :=
    h1.exists_monotone_subseq fun n ↦ (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 fun n ↦ h.natEmbedding _ _
  refine mn.ne (g.injective <| (h.natEmbedding _).injective ?_)
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ mn.le) h2'

end OrderedCancelCommMonoid

variable [CancelCommMonoid α] [LinearOrder α] [MulLeftMono α] [MulRightStrictMono α]

@[to_additive Set.AddAntidiagonal.finite_of_isWF]
theorem finite_of_isWF {s t : Set α} (hs : s.IsWF) (ht : t.IsWF)
    (a) : (setMulAntidiagonal s t a).Finite :=
  finite_of_isPWO hs.isPWO ht.isPWO a

end MulAntidiagonal

end Set
