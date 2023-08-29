/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.MulAntidiagonal

#align_import data.finset.mul_antidiagonal from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-! # Multiplication antidiagonal as a `Finset`.

We construct the `Finset` of all pairs
of an element in `s` and an element in `t` that multiply to `a`,
given that `s` and `t` are well-ordered.-/


namespace Set

open Pointwise

variable {α : Type*} {s t : Set α}

@[to_additive]
theorem IsPwo.mul [OrderedCancelCommMonoid α] (hs : s.IsPwo) (ht : t.IsPwo) : IsPwo (s * t) := by
  rw [← image_mul_prod]
  -- ⊢ IsPwo ((fun x => x.fst * x.snd) '' s ×ˢ t)
  exact (hs.prod ht).image_of_monotone (monotone_fst.mul' monotone_snd)
  -- 🎉 no goals
#align set.is_pwo.mul Set.IsPwo.mul
#align set.is_pwo.add Set.IsPwo.add

variable [LinearOrderedCancelCommMonoid α]

@[to_additive]
theorem IsWf.mul (hs : s.IsWf) (ht : t.IsWf) : IsWf (s * t) :=
  (hs.isPwo.mul ht.isPwo).isWf
#align set.is_wf.mul Set.IsWf.mul
#align set.is_wf.add Set.IsWf.add

@[to_additive]
theorem IsWf.min_mul (hs : s.IsWf) (ht : t.IsWf) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.mul ht).min (hsn.mul htn) = hs.min hsn * ht.min htn := by
  refine' le_antisymm (IsWf.min_le _ _ (mem_mul.2 ⟨_, _, hs.min_mem _, ht.min_mem _, rfl⟩)) _
  -- ⊢ min hs hsn * min ht htn ≤ min (_ : IsWf (s * t)) (_ : Set.Nonempty (s * t))
  rw [IsWf.le_min_iff]
  -- ⊢ ∀ (b : α), b ∈ s * t → min hs hsn * min ht htn ≤ b
  rintro _ ⟨x, y, hx, hy, rfl⟩
  -- ⊢ min hs hsn * min ht htn ≤ (fun x x_1 => x * x_1) x y
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy)
  -- 🎉 no goals
#align set.is_wf.min_mul Set.IsWf.min_mul
#align set.is_wf.min_add Set.IsWf.min_add

end Set

namespace Finset

open Pointwise

variable {α : Type*}

variable [OrderedCancelCommMonoid α] {s t : Set α} (hs : s.IsPwo) (ht : t.IsPwo) (a : α)

/-- `Finset.mulAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` that multiply to `a`, but its construction requires proofs that `s` and `t` are
well-ordered. -/
@[to_additive "`Finset.addAntidiagonal hs ht a` is the set of all pairs of an element in
`s` and an element in `t` that add to `a`, but its construction requires proofs that `s` and `t` are
well-ordered."]
noncomputable def mulAntidiagonal : Finset (α × α) :=
  (Set.MulAntidiagonal.finite_of_isPwo hs ht a).toFinset
#align finset.mul_antidiagonal Finset.mulAntidiagonal
#align finset.add_antidiagonal Finset.addAntidiagonal

variable {hs ht a} {u : Set α} {hu : u.IsPwo} {x : α × α}

@[to_additive (attr := simp)]
theorem mem_mulAntidiagonal : x ∈ mulAntidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a := by
  simp only [mulAntidiagonal, Set.Finite.mem_toFinset, Set.mem_mulAntidiagonal]
  -- 🎉 no goals
#align finset.mem_mul_antidiagonal Finset.mem_mulAntidiagonal
#align finset.mem_add_antidiagonal Finset.mem_addAntidiagonal

@[to_additive]
theorem mulAntidiagonal_mono_left (h : u ⊆ s) : mulAntidiagonal hu ht a ⊆ mulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.mulAntidiagonal_mono_left h
#align finset.mul_antidiagonal_mono_left Finset.mulAntidiagonal_mono_left
#align finset.add_antidiagonal_mono_left Finset.addAntidiagonal_mono_left

@[to_additive]
theorem mulAntidiagonal_mono_right (h : u ⊆ t) :
    mulAntidiagonal hs hu a ⊆ mulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.mulAntidiagonal_mono_right h
#align finset.mul_antidiagonal_mono_right Finset.mulAntidiagonal_mono_right
#align finset.add_antidiagonal_mono_right Finset.addAntidiagonal_mono_right

-- Porting note: removed `(attr := simp)`. simp can prove this.
@[to_additive]
theorem swap_mem_mulAntidiagonal :
    x.swap ∈ Finset.mulAntidiagonal hs ht a ↔ x ∈ Finset.mulAntidiagonal ht hs a := by
  simp only [mem_mulAntidiagonal, Prod.fst_swap, Prod.snd_swap, Set.swap_mem_mulAntidiagonal_aux,
             Set.mem_mulAntidiagonal]
#align finset.swap_mem_mul_antidiagonal Finset.swap_mem_mulAntidiagonal
#align finset.swap_mem_add_antidiagonal Finset.swap_mem_addAntidiagonal

@[to_additive]
theorem support_mulAntidiagonal_subset_mul : { a | (mulAntidiagonal hs ht a).Nonempty } ⊆ s * t :=
  fun a ⟨b, hb⟩ => by
  rw [mem_mulAntidiagonal] at hb
  -- ⊢ a ∈ s * t
  exact ⟨b.1, b.2, hb⟩
  -- 🎉 no goals
#align finset.support_mul_antidiagonal_subset_mul Finset.support_mulAntidiagonal_subset_mul
#align finset.support_add_antidiagonal_subset_add Finset.support_addAntidiagonal_subset_add

@[to_additive]
theorem isPwo_support_mulAntidiagonal : { a | (mulAntidiagonal hs ht a).Nonempty }.IsPwo :=
  (hs.mul ht).mono support_mulAntidiagonal_subset_mul
#align finset.is_pwo_support_mul_antidiagonal Finset.isPwo_support_mulAntidiagonal
#align finset.is_pwo_support_add_antidiagonal Finset.isPwo_support_addAntidiagonal

@[to_additive]
theorem mulAntidiagonal_min_mul_min {α} [LinearOrderedCancelCommMonoid α] {s t : Set α}
    (hs : s.IsWf) (ht : t.IsWf) (hns : s.Nonempty) (hnt : t.Nonempty) :
    mulAntidiagonal hs.isPwo ht.isPwo (hs.min hns * ht.min hnt) = {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  -- ⊢ (a, b) ∈ mulAntidiagonal (_ : Set.IsPwo s) (_ : Set.IsPwo t) (Set.IsWf.min h …
  simp only [mem_mulAntidiagonal, mem_singleton, Prod.ext_iff]
  -- ⊢ a ∈ s ∧ b ∈ t ∧ a * b = Set.IsWf.min hs hns * Set.IsWf.min ht hnt ↔ a = Set. …
  constructor
  -- ⊢ a ∈ s ∧ b ∈ t ∧ a * b = Set.IsWf.min hs hns * Set.IsWf.min ht hnt → a = Set. …
  · rintro ⟨has, hat, hst⟩
    -- ⊢ a = Set.IsWf.min hs hns ∧ b = Set.IsWf.min ht hnt
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (mul_lt_mul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, mul_left_cancel hst⟩
    -- 🎉 no goals
  · rintro ⟨rfl, rfl⟩
    -- ⊢ Set.IsWf.min hs hns ∈ s ∧ Set.IsWf.min ht hnt ∈ t ∧ Set.IsWf.min hs hns * Se …
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩
    -- 🎉 no goals
#align finset.mul_antidiagonal_min_mul_min Finset.mulAntidiagonal_min_mul_min
#align finset.add_antidiagonal_min_add_min Finset.addAntidiagonal_min_add_min

end Finset

