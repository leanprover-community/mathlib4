/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.Function

#align_import data.set.intervals.surj_on from "leanprover-community/mathlib"@"a59dad53320b73ef180174aae867addd707ef00e"

/-!
# Monotone surjective functions are surjective on intervals

A monotone surjective function sends any interval in the domain onto the interval with corresponding
endpoints in the range.  This is expressed in this file using `Set.surjOn`, and provided for all
permutations of interval endpoints.
-/


variable {α : Type*} {β : Type*} [LinearOrder α] [PartialOrder β] {f : α → β}

open Set Function

open OrderDual (toDual)

theorem surjOn_Ioo_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ioo a b) (Ioo (f a) (f b)) := by
  intro p hp
  rcases h_surj p with ⟨x, rfl⟩
  refine ⟨x, mem_Ioo.2 ?_, rfl⟩
  contrapose! hp
  exact fun h => h.2.not_le (h_mono <| hp <| h_mono.reflect_lt h.1)
#align surj_on_Ioo_of_monotone_surjective surjOn_Ioo_of_monotone_surjective

theorem surjOn_Ico_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ico a b) (Ico (f a) (f b)) := by
  obtain hab | hab := lt_or_le a b
  · intro p hp
    rcases eq_left_or_mem_Ioo_of_mem_Ico hp with (rfl | hp')
    · exact mem_image_of_mem f (left_mem_Ico.mpr hab)
    · have := surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'
      exact image_subset f Ioo_subset_Ico_self this
  · rw [Ico_eq_empty (h_mono hab).not_lt]
    exact surjOn_empty f _
#align surj_on_Ico_of_monotone_surjective surjOn_Ico_of_monotone_surjective

theorem surjOn_Ioc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ioc a b) (Ioc (f a) (f b)) := by
  simpa using surjOn_Ico_of_monotone_surjective h_mono.dual h_surj (toDual b) (toDual a)
#align surj_on_Ioc_of_monotone_surjective surjOn_Ioc_of_monotone_surjective

-- to see that the hypothesis `a ≤ b` is necessary, consider a constant function
theorem surjOn_Icc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    {a b : α} (hab : a ≤ b) : SurjOn f (Icc a b) (Icc (f a) (f b)) := by
  intro p hp
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hp with (rfl | rfl | hp')
  · exact ⟨a, left_mem_Icc.mpr hab, rfl⟩
  · exact ⟨b, right_mem_Icc.mpr hab, rfl⟩
  · have := surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'
    exact image_subset f Ioo_subset_Icc_self this
#align surj_on_Icc_of_monotone_surjective surjOn_Icc_of_monotone_surjective

theorem surjOn_Ioi_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Ioi a) (Ioi (f a)) := by
  rw [← compl_Iic, ← compl_compl (Ioi (f a))]
  refine MapsTo.surjOn_compl ?_ h_surj
  exact fun x hx => (h_mono hx).not_lt
#align surj_on_Ioi_of_monotone_surjective surjOn_Ioi_of_monotone_surjective

theorem surjOn_Iio_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Iio a) (Iio (f a)) :=
  @surjOn_Ioi_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a
#align surj_on_Iio_of_monotone_surjective surjOn_Iio_of_monotone_surjective

theorem surjOn_Ici_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Ici a) (Ici (f a)) := by
  rw [← Ioi_union_left, ← Ioi_union_left]
  exact
    (surjOn_Ioi_of_monotone_surjective h_mono h_surj a).union_union
      (@image_singleton _ _ f a ▸ surjOn_image _ _)
#align surj_on_Ici_of_monotone_surjective surjOn_Ici_of_monotone_surjective

theorem surjOn_Iic_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Iic a) (Iic (f a)) :=
  @surjOn_Ici_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a
#align surj_on_Iic_of_monotone_surjective surjOn_Iic_of_monotone_surjective
