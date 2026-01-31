/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Data.Set.SMulAntidiagonal

/-!
# Antidiagonal for scalar multiplication as a `Finset`.

Given partially ordered sets `G` and `P`, with an action of `G` on `P` that preserves and reflects
the order relation, we construct, for any element `a` in `P` and partially well-ordered subsets `s`
in `G` and `t` in `P`, the `Finset` of all pairs of an element in `s` and an element in `t` that
scalar-multiply to `a`.

## Definitions
* Finset.setSMulAntidiagonal : Finset antidiagonal for PWO inputs.
* Finset.setVAddAntidiagonal : Finset antidiagonal for PWO inputs.

-/

@[expose] public section

variable {G P : Type*}

open Pointwise

namespace Set

@[to_additive]
theorem IsPWO.smul [Preorder G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
    {s : Set G} {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s • t) := by
  rw [← @image_smul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.smul monotone_snd)

@[to_additive]
theorem IsWF.smul [LinearOrder G] [LinearOrder P] [SMul G P] [IsOrderedSMul G P] {s : Set G}
    {t : Set P} (hs : s.IsWF) (ht : t.IsWF) : IsWF (s • t) :=
  (hs.isPWO.smul ht.isPWO).isWF

@[to_additive]
theorem IsWF.min_smul [LinearOrder G] [LinearOrder P] [SMul G P] [IsOrderedSMul G P]
    {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.smul ht).min (hsn.smul htn) = hs.min hsn • ht.min htn := by
  refine le_antisymm (IsWF.min_le _ _ (mem_smul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) ?_
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact IsOrderedSMul.smul_le_smul (hs.min_le _ hx) (ht.min_le _ hy)

end Set

namespace Finset

section

open Set

variable [PartialOrder G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P] {s : Set G}
    {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) (a : P) {u : Set G} {hu : u.IsPWO} {v : Set P}
    {hv : v.IsPWO} {x : G × P}

/-- `Finset.setSMulAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` whose scalar multiplication yields `a`, but its construction requires proofs that `s`
and `t` are well-ordered. -/
@[to_additive /-- `Finset.setVAddAntidiagonal hs ht a` is the set of all pairs of an element in `s`
and an element in `t` whose vector addition yields `a`, but its construction requires proofs that
`s` and `t` are well-ordered. -/]
noncomputable def setSMulAntidiagonal [PartialOrder G] [PartialOrder P] [IsOrderedCancelSMul G P]
    {s : Set G} {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) (a : P) : Finset (G × P) :=
  (SMulAntidiagonal.finite_of_isPWO hs ht a).toFinset

@[to_additive (attr := deprecated setVAddAntidiagonal (since := "2026-01-31")),
  deprecated setSMulAntidiagonal (since := "2026-01-31")]
alias smulAntidiagonal := setSMulAntidiagonal

@[to_additive (attr := simp)]
theorem mem_smulAntidiagonal :
    x ∈ setSMulAntidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a := by
  simp only [setSMulAntidiagonal, Set.Finite.mem_toFinset]
  exact Set.mem_sep_iff

@[to_additive]
theorem smulAntidiagonal_mono_left {a : P} {hs : s.IsPWO} {ht : t.IsPWO} (h : u ⊆ s) :
    setSMulAntidiagonal hu ht a ⊆ setSMulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.smulAntidiagonal_mono_left h

@[to_additive]
theorem smulAntidiagonal_mono_right {a : P} {hs : s.IsPWO} {ht : t.IsPWO} (h : v ⊆ t) :
    setSMulAntidiagonal hs hv a ⊆ setSMulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.smulAntidiagonal_mono_right h

@[to_additive]
theorem support_smulAntidiagonal_subset_smul {hs : s.IsPWO} {ht : t.IsPWO} :
    { a | (setSMulAntidiagonal hs ht a).Nonempty } ⊆ (s • t) :=
  fun a ⟨b, hb⟩ => by
  rw [mem_smulAntidiagonal] at hb
  rw [Set.mem_smul]
  use b.1
  refine { left := hb.1, right := ?_ }
  use b.2
  exact { left := hb.2.1, right := hb.2.2 }

@[to_additive]
theorem isPWO_support_smulAntidiagonal {hs : s.IsPWO} {ht : t.IsPWO} :
    { a | (setSMulAntidiagonal hs ht a).Nonempty }.IsPWO :=
  (hs.smul ht).mono (support_smulAntidiagonal_subset_smul)

end

@[to_additive]
theorem smulAntidiagonal_min_smul_min [LinearOrder G] [LinearOrder P] [SMul G P]
    [IsOrderedCancelSMul G P] {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hns : s.Nonempty)
    (hnt : t.Nonempty) :
    setSMulAntidiagonal hs.isPWO ht.isPWO (hs.min hns • ht.min hnt) =
      {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  simp only [mem_smulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (SMul.smul_lt_smul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, IsCancelSMul.left_cancel _ _ _ hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩

end Finset
