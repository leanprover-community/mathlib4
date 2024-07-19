/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathlib.Data.Set.SMulAntidiagonal

#align_import data.finset.mul_antidiagonal from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-! # Multiplication antidiagonal as a `Finset`.

We construct the `Finset` of all pairs
of an element in `s` and an element in `t` that multiply to `a`,
given that `s` and `t` are well-ordered. -/

variable {G P : Type*}

open Pointwise

namespace Finset

section

open Set

variable [PartialOrder G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P] {s : Set G}
    {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) (a : P) {u : Set G} {hu : u.IsPWO} {v : Set P}
    {hv : v.IsPWO} {x : G × P}

/-- `Finset.SMulAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` whose scalar multiplicatoin yields `a`, but its construction requires proofs that `s`
and `t` are well-ordered. -/
@[to_additive "`Finset.VAddAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` whose vector addition yields `a`, but its construction requires proofs that `s` and
`t` are well-ordered."]
noncomputable def SMulAntidiagonal [PartialOrder G] [PartialOrder P] [IsOrderedCancelSMul G P]
    {s : Set G} {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) (a : P) : Finset (G × P) :=
  (SMulAntidiagonal.finite_of_isPWO hs ht a).toFinset

@[to_additive (attr := simp)]
theorem mem_SMulAntidiagonal :
    x ∈ SMulAntidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a := by
  simp only [SMulAntidiagonal, Set.Finite.mem_toFinset]
  exact Set.mem_sep_iff

@[to_additive]
theorem SMulAntidiagonal_mono_left {a : P} {hs : s.IsPWO} {ht : t.IsPWO} (h : u ⊆ s) :
    SMulAntidiagonal hu ht a ⊆ SMulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| smulAntidiagonal_mono_left h

@[to_additive]
theorem SMulAntidiagonal_mono_right {a : P} {hs : s.IsPWO} {ht : t.IsPWO} (h : v ⊆ t) :
    SMulAntidiagonal hs hv a ⊆ SMulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| smulAntidiagonal_mono_right h

@[to_additive]
theorem support_SMulAntidiagonal_subset_SMul {hs : s.IsPWO} {ht : t.IsPWO} :
    { a | (SMulAntidiagonal hs ht a).Nonempty } ⊆ (s • t) :=
  fun a ⟨b, hb⟩ => by
  rw [mem_SMulAntidiagonal] at hb
  rw [Set.mem_smul]
  use b.1
  refine { left := hb.1, right := ?_ }
  use b.2
  exact { left := hb.2.1, right := hb.2.2 }

@[to_additive]
theorem isPWO_support_SMulAntidiagonal {hs : s.IsPWO} {ht : t.IsPWO} :
    { a | (SMulAntidiagonal hs ht a).Nonempty }.IsPWO :=
  (hs.SMul ht).mono (support_SMulAntidiagonal_subset_SMul)

end

@[to_additive]
theorem SMulAntidiagonal_min_SMul_min [LinearOrder G] [LinearOrder P] [SMul G P]
    [IsOrderedCancelSMul G P] {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hns : s.Nonempty)
    (hnt : t.Nonempty) :
    SMulAntidiagonal hs.isPWO ht.isPWO (hs.min hns • ht.min hnt) = {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  simp only [mem_SMulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (SMul.smul_lt_smul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, IsCancelSMul.left_cancel _ _ _ hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩

end Finset
