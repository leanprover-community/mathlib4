/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Interval.Finset
import Mathlib.Order.Interval.Multiset

#align_import data.multiset.locally_finite from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

/-!
# Algebraic properties of multiset intervals

This file provides results about the interaction of algebra with `Multiset.Ixx`.
-/

variable {α : Type*}

namespace Multiset
variable [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]

lemma map_add_left_Icc (a b c : α) : (Icc a b).map (c + ·) = Icc (c + a) (c + b) := by
  classical rw [Icc, Icc, ← Finset.image_add_left_Icc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Icc Multiset.map_add_left_Icc

lemma map_add_left_Ico (a b c : α) : (Ico a b).map (c + ·) = Ico (c + a) (c + b) := by
  classical rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Ico Multiset.map_add_left_Ico

lemma map_add_left_Ioc (a b c : α) : (Ioc a b).map (c + ·) = Ioc (c + a) (c + b) := by
  classical rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Ioc Multiset.map_add_left_Ioc

lemma map_add_left_Ioo (a b c : α) : (Ioo a b).map (c + ·) = Ioo (c + a) (c + b) := by
  classical rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Ioo Multiset.map_add_left_Ioo

lemma map_add_right_Icc (a b c : α) : ((Icc a b).map fun x => x + c) = Icc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Icc _ _ _
#align multiset.map_add_right_Icc Multiset.map_add_right_Icc

lemma map_add_right_Ico (a b c : α) : ((Ico a b).map fun x => x + c) = Ico (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ico _ _ _
#align multiset.map_add_right_Ico Multiset.map_add_right_Ico

lemma map_add_right_Ioc (a b c : α) : ((Ioc a b).map fun x => x + c) = Ioc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioc _ _ _
#align multiset.map_add_right_Ioc Multiset.map_add_right_Ioc

lemma map_add_right_Ioo (a b c : α) : ((Ioo a b).map fun x => x + c) = Ioo (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioo _ _ _
#align multiset.map_add_right_Ioo Multiset.map_add_right_Ioo

end Multiset
