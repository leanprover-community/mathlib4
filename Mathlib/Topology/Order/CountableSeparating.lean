/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.CountableSeparatingOn

/-!
# Countably many infinite intervals separate points

In this file we prove that in a linear order with second countable order topology,
the points can be separated by countably many infinite intervals.
We prove 4 versions of this statement (one for each of the infinite intervals),
as well as provide convenience corollaries about `Filter.EventuallyEq`.
-/

open Set

variable {X : Type*} [TopologicalSpace X] [LinearOrder X]
  [OrderTopology X] [SecondCountableTopology X]

namespace HasCountableSeparatingOn

variable {s : Set X}

instance range_Iio : HasCountableSeparatingOn X (· ∈ range Iio) s := by
  constructor
  rcases TopologicalSpace.exists_countable_dense X with ⟨s, hsc, hsd⟩
  set t := s ∪ {x | ∃ y, y ⋖ x}
  refine ⟨Iio '' t, .image ?_ _, ?_, ?_⟩
  · exact hsc.union countable_setOf_covBy_left
  · exact image_subset_range _ _
  · rintro x - y - h
    by_contra! hne
    wlog hlt : x < y generalizing x y
    · refine this y x ?_ hne.symm (hne.lt_or_gt.resolve_left hlt)
      simpa only [iff_comm] using h
    cases (Ioo x y).eq_empty_or_nonempty with
    | inl he =>
      specialize h (Iio y) (mem_image_of_mem _ (.inr ⟨x, hlt, by simpa using Set.ext_iff.mp he⟩))
      simp [hlt.not_ge] at h
    | inr hne =>
      rcases hsd.inter_open_nonempty _ isOpen_Ioo hne with ⟨z, ⟨hxz, hzy⟩, hzs⟩
      simpa [hxz, hzy.not_gt] using h (Iio z) (mem_image_of_mem _ (.inl hzs))

instance range_Ioi : HasCountableSeparatingOn X (· ∈ range Ioi) s :=
  .range_Iio (X := Xᵒᵈ)

instance range_Iic : HasCountableSeparatingOn X (· ∈ range Iic) s :=
  let ⟨t, htc, ht_sub, ht⟩ := (range_Ioi (X := X) (s := s)).1
  ⟨compl '' t, htc.image _, by simpa [← compl_inj_iff (x := Ioi _)] using ht_sub,
    by simpa [not_iff_not]⟩

instance range_Ici : HasCountableSeparatingOn X (· ∈ range Ici) s :=
  range_Iic (X := Xᵒᵈ)

end HasCountableSeparatingOn

namespace Filter.EventuallyEq

variable {α : Type*} {l : Filter α} [CountableInterFilter l] {f g : α → X}

lemma of_forall_eventually_lt_iff (h : ∀ x, ∀ᶠ a in l, f a < x ↔ g a < x) : f =ᶠ[l] g :=
  of_forall_separating_preimage (· ∈ range Iio) <| forall_mem_range.2 <| fun x ↦ .set_eq (h x)

lemma of_forall_eventually_le_iff (h : ∀ x, ∀ᶠ a in l, f a ≤ x ↔ g a ≤ x) : f =ᶠ[l] g :=
  of_forall_separating_preimage (· ∈ range Iic) <| forall_mem_range.2 <| fun x ↦ .set_eq (h x)

lemma of_forall_eventually_gt_iff (h : ∀ x, ∀ᶠ a in l, x < f a ↔ x < g a) : f =ᶠ[l] g :=
  of_forall_eventually_lt_iff (X := Xᵒᵈ) h

lemma of_forall_eventually_ge_iff (h : ∀ x, ∀ᶠ a in l, x ≤ f a ↔ x ≤ g a) : f =ᶠ[l] g :=
  of_forall_eventually_le_iff (X := Xᵒᵈ) h

end Filter.EventuallyEq
