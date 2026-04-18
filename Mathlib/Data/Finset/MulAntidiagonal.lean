/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Set.MulAntidiagonal
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Set-based multiplication antidiagonal as a `Finset`.

We construct the `Finset` of all pairs
of an element in `s` and an element in `t` that multiply to `a`,
given that `s` and `t` are well-ordered.

The definitions are named `setMulAntidiagonal` / `setAddAntidiagonal` to distinguish them from
the typeclass-based `HasMulAntidiagonal.mulAntidiagonal` / `HasAntidiagonal.antidiagonal`
in `Mathlib.Algebra.Order.Antidiag.Prod`. -/

@[expose] public section


namespace Set

open Pointwise

variable {α : Type*} {s t : Set α}

@[to_additive]
theorem IsPWO.mul [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
    (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s * t) := by
  rw [← image_mul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.mul' monotone_snd)

variable [CommMonoid α] [LinearOrder α] [IsOrderedCancelMonoid α]

@[to_additive]
theorem IsWF.mul (hs : s.IsWF) (ht : t.IsWF) : IsWF (s * t) :=
  (hs.isPWO.mul ht.isPWO).isWF

@[to_additive]
theorem IsWF.min_mul (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.mul ht).min (hsn.mul htn) = hs.min hsn * ht.min htn := by
  refine le_antisymm (IsWF.min_le _ _ (mem_mul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) ?_
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy)

end Set

namespace Finset

open Pointwise

variable {α : Type*}
variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
  {s t : Set α} (hs : s.IsPWO) (ht : t.IsPWO) (a : α)

/-- `Finset.setMulAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` that multiply to `a`, but its construction requires proofs that `s` and `t` are
well-ordered. -/
@[to_additive /-- `Finset.setAddAntidiagonal hs ht a` is the set of all pairs of an element in
`s` and an element in `t` that add to `a`, but its construction requires proofs that `s` and `t` are
well-ordered. -/]
noncomputable def setMulAntidiagonal : Finset (α × α) :=
  (Set.MulAntidiagonal.finite_of_isPWO hs ht a).toFinset

/-- Deprecated alias of `Finset.setMulAntidiagonal`. -/
@[to_additive (attr := deprecated setAddAntidiagonal (since := "2026-04-02"))
    /-- Deprecated alias of `Finset.setAddAntidiagonal`. -/,
  deprecated setMulAntidiagonal (since := "2026-04-02")]
noncomputable alias mulAntidiagonal := setMulAntidiagonal

variable {hs ht a} {u : Set α} {hu : u.IsPWO} {x : α × α}

@[to_additive (attr := simp)]
theorem mem_setMulAntidiagonal :
    x ∈ setMulAntidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a := by
  simp only [setMulAntidiagonal, Set.Finite.mem_toFinset, Set.mem_mulAntidiagonal]

@[to_additive (attr := deprecated mem_setAddAntidiagonal (since := "2026-04-02")),
  deprecated mem_setMulAntidiagonal (since := "2026-04-02")]
alias mem_mulAntidiagonal := mem_setMulAntidiagonal

@[to_additive]
theorem setMulAntidiagonal_mono_left (h : u ⊆ s) :
    setMulAntidiagonal hu ht a ⊆ setMulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.mulAntidiagonal_mono_left h

@[to_additive (attr := deprecated setAddAntidiagonal_mono_left (since := "2026-04-02")),
  deprecated setMulAntidiagonal_mono_left (since := "2026-04-02")]
alias mulAntidiagonal_mono_left := setMulAntidiagonal_mono_left

@[to_additive]
theorem setMulAntidiagonal_mono_right (h : u ⊆ t) :
    setMulAntidiagonal hs hu a ⊆ setMulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.mulAntidiagonal_mono_right h

@[to_additive (attr := deprecated setAddAntidiagonal_mono_right (since := "2026-04-02")),
  deprecated setMulAntidiagonal_mono_right (since := "2026-04-02")]
alias mulAntidiagonal_mono_right := setMulAntidiagonal_mono_right

@[to_additive]
theorem swap_mem_setMulAntidiagonal :
    x.swap ∈ Finset.setMulAntidiagonal hs ht a ↔ x ∈ Finset.setMulAntidiagonal ht hs a := by
  simp

@[to_additive (attr := deprecated swap_mem_setAddAntidiagonal (since := "2026-04-02")),
  deprecated swap_mem_setMulAntidiagonal (since := "2026-04-02")]
alias swap_mem_mulAntidiagonal := swap_mem_setMulAntidiagonal

@[to_additive]
theorem support_setMulAntidiagonal_subset_mul :
    { a | (setMulAntidiagonal hs ht a).Nonempty } ⊆ s * t :=
  fun a ⟨b, hb⟩ => by
  rw [mem_setMulAntidiagonal] at hb
  exact ⟨b.1, hb.1, b.2, hb.2⟩

@[to_additive (attr := deprecated support_setAddAntidiagonal_subset_add (since := "2026-04-02")),
  deprecated support_setMulAntidiagonal_subset_mul (since := "2026-04-02")]
alias support_mulAntidiagonal_subset_mul := support_setMulAntidiagonal_subset_mul

@[to_additive]
theorem isPWO_support_setMulAntidiagonal :
    { a | (setMulAntidiagonal hs ht a).Nonempty }.IsPWO :=
  (hs.mul ht).mono support_setMulAntidiagonal_subset_mul

@[to_additive (attr := deprecated isPWO_support_setAddAntidiagonal (since := "2026-04-02")),
  deprecated isPWO_support_setMulAntidiagonal (since := "2026-04-02")]
alias isPWO_support_mulAntidiagonal := isPWO_support_setMulAntidiagonal

@[to_additive]
theorem setMulAntidiagonal_min_mul_min {α} [CommMonoid α] [LinearOrder α]
    [IsOrderedCancelMonoid α]
    {s t : Set α} (hs : s.IsWF) (ht : t.IsWF) (hns : s.Nonempty) (hnt : t.Nonempty) :
    setMulAntidiagonal hs.isPWO ht.isPWO (hs.min hns * ht.min hnt) =
      {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  simp only [mem_setMulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (mul_lt_mul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, mul_left_cancel hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩

@[to_additive (attr := deprecated setAddAntidiagonal_min_add_min (since := "2026-04-02")),
  deprecated setMulAntidiagonal_min_mul_min (since := "2026-04-02")]
alias mulAntidiagonal_min_mul_min := setMulAntidiagonal_min_mul_min

end Finset
