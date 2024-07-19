/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Fintype.BigOperators

#align_import data.finset.finsupp from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

/-!
# Finitely supported product of finsets

This file defines the finitely supported product of finsets as a `Finset (ι →₀ α)`.

## Main declarations

* `Finset.finsupp`: Finitely supported product of finsets. `s.finset t` is the product of the `t i`
  over all `i ∈ s`.
* `Finsupp.pi`: `f.pi` is the finset of `Finsupp`s whose `i`-th value lies in `f i`. This is the
  special case of `Finset.finsupp` where we take the product of the `f i` over the support of `f`.

## Implementation notes

We make heavy use of the fact that `0 : Finset α` is `{0}`. This scalar actions convention turns out
to be precisely what we want here too.
-/


noncomputable section

open Finsupp

open scoped Classical
open Pointwise

variable {ι α : Type*} [Zero α] {s : Finset ι} {f : ι →₀ α}

namespace Finset

/-- Finitely supported product of finsets. -/
protected def finsupp (s : Finset ι) (t : ι → Finset α) : Finset (ι →₀ α) :=
  (s.pi t).map ⟨indicator s, indicator_injective s⟩
#align finset.finsupp Finset.finsupp

theorem mem_finsupp_iff {t : ι → Finset α} :
    f ∈ s.finsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i := by
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨support_indicator_subset _ _, fun i hi => ?_⟩
    convert mem_pi.1 hf i hi
    exact indicator_of_mem hi _
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    exact ite_eq_left_iff.2 fun hi => (not_mem_support_iff.1 fun H => hi <| h.1 H).symm
#align finset.mem_finsupp_iff Finset.mem_finsupp_iff

/-- When `t` is supported on `s`, `f ∈ s.finsupp t` precisely means that `f` is pointwise in `t`. -/
@[simp]
theorem mem_finsupp_iff_of_support_subset {t : ι →₀ Finset α} (ht : t.support ⊆ s) :
    f ∈ s.finsupp t ↔ ∀ i, f i ∈ t i := by
  refine
    mem_finsupp_iff.trans
      (forall_and.symm.trans <|
        forall_congr' fun i =>
          ⟨fun h => ?_, fun h =>
            ⟨fun hi => ht <| mem_support_iff.2 fun H => mem_support_iff.1 hi ?_, fun _ => h⟩⟩)
  · by_cases hi : i ∈ s
    · exact h.2 hi
    · rw [not_mem_support_iff.1 (mt h.1 hi), not_mem_support_iff.1 fun H => hi <| ht H]
      exact zero_mem_zero
  · rwa [H, mem_zero] at h
#align finset.mem_finsupp_iff_of_support_subset Finset.mem_finsupp_iff_of_support_subset

@[simp]
theorem card_finsupp (s : Finset ι) (t : ι → Finset α) :
    (s.finsupp t).card = ∏ i ∈ s, (t i).card :=
  (card_map _).trans <| card_pi _ _
#align finset.card_finsupp Finset.card_finsupp

end Finset

open Finset

namespace Finsupp

/-- Given a finitely supported function `f : ι →₀ Finset α`, one can define the finset
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for all `i`. -/
def pi (f : ι →₀ Finset α) : Finset (ι →₀ α) :=
  f.support.finsupp f
#align finsupp.pi Finsupp.pi

@[simp]
theorem mem_pi {f : ι →₀ Finset α} {g : ι →₀ α} : g ∈ f.pi ↔ ∀ i, g i ∈ f i :=
  mem_finsupp_iff_of_support_subset <| Subset.refl _
#align finsupp.mem_pi Finsupp.mem_pi

@[simp]
theorem card_pi (f : ι →₀ Finset α) : f.pi.card = f.prod fun i => (f i).card := by
  rw [pi, card_finsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.natCast_apply, Nat.cast_id]
#align finsupp.card_pi Finsupp.card_pi

end Finsupp
