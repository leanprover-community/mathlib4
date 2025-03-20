/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-! # Casting lemmas for rational numbers involving sums and products
-/

variable {ι α : Type*}

namespace Rat

section WithDivRing

variable [DivisionRing α] [CharZero α]

@[simp, norm_cast]
theorem cast_list_sum (s : List ℚ) : (↑s.sum : α) = (s.map (↑)).sum :=
  map_list_sum (Rat.castHom α) _

@[simp, norm_cast]
theorem cast_multiset_sum (s : Multiset ℚ) : (↑s.sum : α) = (s.map (↑)).sum :=
  map_multiset_sum (Rat.castHom α) _

@[simp, norm_cast]
theorem cast_sum (s : Finset ι) (f : ι → ℚ) : ∑ i ∈ s, f i = ∑ i ∈ s, (f i : α) :=
  map_sum (Rat.castHom α) _ s

@[simp, norm_cast]
theorem cast_list_prod (s : List ℚ) : (↑s.prod : α) = (s.map (↑)).prod :=
  map_list_prod (Rat.castHom α) _

end WithDivRing

section Field

variable [Field α] [CharZero α]

@[simp, norm_cast]
theorem cast_multiset_prod (s : Multiset ℚ) : (↑s.prod : α) = (s.map (↑)).prod :=
  map_multiset_prod (Rat.castHom α) _

@[simp, norm_cast]
theorem cast_prod (s : Finset ι) (f : ι → ℚ) : ∏ i ∈ s, f i = ∏ i ∈ s, (f i : α) :=
  map_prod (Rat.castHom α) _ _

end Field

end Rat
