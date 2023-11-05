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
  exact (hs.prod ht).image_of_monotone (monotone_fst.mul' monotone_snd)

variable [LinearOrderedCancelCommMonoid α]

@[to_additive]
theorem IsWf.mul (hs : s.IsWf) (ht : t.IsWf) : IsWf (s * t) :=
  (hs.isPwo.mul ht.isPwo).isWf

@[to_additive]
theorem IsWf.min_mul (hs : s.IsWf) (ht : t.IsWf) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.mul ht).min (hsn.mul htn) = hs.min hsn * ht.min htn := by
  refine' le_antisymm (IsWf.min_le _ _ (mem_mul.2 ⟨_, _, hs.min_mem _, ht.min_mem _, rfl⟩)) _
  rw [IsWf.le_min_iff]
  rintro _ ⟨x, y, hx, hy, rfl⟩
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy)

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

variable {hs ht a} {u : Set α} {hu : u.IsPwo} {x : α × α}

@[to_additive (attr := simp)]
theorem mem_mulAntidiagonal : x ∈ mulAntidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a := by
  simp only [mulAntidiagonal, Set.Finite.mem_toFinset, Set.mem_mulAntidiagonal]

@[to_additive]
theorem mulAntidiagonal_mono_left (h : u ⊆ s) : mulAntidiagonal hu ht a ⊆ mulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.mulAntidiagonal_mono_left h

@[to_additive]
theorem mulAntidiagonal_mono_right (h : u ⊆ t) :
    mulAntidiagonal hs hu a ⊆ mulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.mulAntidiagonal_mono_right h

-- Porting note: removed `(attr := simp)`. simp can prove this.
@[to_additive]
theorem swap_mem_mulAntidiagonal :
    x.swap ∈ Finset.mulAntidiagonal hs ht a ↔ x ∈ Finset.mulAntidiagonal ht hs a := by
  simp only [mem_mulAntidiagonal, Prod.fst_swap, Prod.snd_swap, Set.swap_mem_mulAntidiagonal_aux,
             Set.mem_mulAntidiagonal]

@[to_additive]
theorem support_mulAntidiagonal_subset_mul : { a | (mulAntidiagonal hs ht a).Nonempty } ⊆ s * t :=
  fun a ⟨b, hb⟩ => by
  rw [mem_mulAntidiagonal] at hb
  exact ⟨b.1, b.2, hb⟩

@[to_additive]
theorem isPwo_support_mulAntidiagonal : { a | (mulAntidiagonal hs ht a).Nonempty }.IsPwo :=
  (hs.mul ht).mono support_mulAntidiagonal_subset_mul

@[to_additive]
theorem mulAntidiagonal_min_mul_min {α} [LinearOrderedCancelCommMonoid α] {s t : Set α}
    (hs : s.IsWf) (ht : t.IsWf) (hns : s.Nonempty) (hnt : t.Nonempty) :
    mulAntidiagonal hs.isPwo ht.isPwo (hs.min hns * ht.min hnt) = {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  simp only [mem_mulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (mul_lt_mul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, mul_left_cancel hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩

end Finset
