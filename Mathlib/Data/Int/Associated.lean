import Mathlib.Algebra.Group.Int.Defs
/-!
# Associated elements and the integers

This file contains some results on equality up to units in the integers.

## Main results

* `Int.natAbs_eq_iff_associated`: the absolute value is equal iff integers are associated
-/

public section


theorem Int.natAbs_eq_iff_associated {a b : ℤ} : a.natAbs = b.natAbs ↔ Associated a b := by
  refine Int.natAbs_eq_natAbs_iff.trans ?_
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact ⟨-1, by simp⟩
  · rintro ⟨u, rfl⟩
    obtain rfl | rfl := Int.units_eq_one_or u
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
