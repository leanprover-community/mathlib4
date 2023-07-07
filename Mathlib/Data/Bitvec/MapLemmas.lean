import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.ConstantLemmas
import Mathlib.Data.Vector.MapLemmas

namespace Bitvec

open Vector

variable (xs : Vector α n)

/-! # Zero -/
@[simp]
theorem mapAccumr₂_zero_left :
    mapAccumr₂ f 0 xs s = mapAccumr (f false · ·) xs s := by
  rw[zero_eq_replicate, mapAccumr₂_replicate_left]

@[simp]
theorem mapAccumr₂_zero_right :
    mapAccumr₂ f xs 0 s = mapAccumr (f · false ·) xs s := by
  rw[zero_eq_replicate, mapAccumr₂_replicate_right]

@[simp]
theorem map₂_zero_left :
    map₂ f 0 xs = map (f false ·) xs := by
  rw[zero_eq_replicate, map₂_replicate_left]

@[simp]
theorem map₂_zero_right :
    map₂ f xs 0 = map (f · false) xs := by
  rw[zero_eq_replicate, map₂_replicate_right]


/-! # Minus One -/
@[simp]
theorem mapAccumr₂_negOne_left :
    mapAccumr₂ f (-1) xs s = mapAccumr (f true · ·) xs s := by
  rw[neg_one, mapAccumr₂_replicate_left]

@[simp]
theorem mapAccumr₂_negOne_right :
    mapAccumr₂ f xs (-1) s = mapAccumr (f · true ·) xs s := by
  rw[neg_one, mapAccumr₂_replicate_right]

@[simp]
theorem map₂_negOne_left :
    map₂ f (-1) xs = map (f true ·) xs := by
  rw[neg_one, map₂_replicate_left]

@[simp]
theorem map₂_negOne_right :
    map₂ f xs (-1) = map (f · true) xs := by
  rw[neg_one, map₂_replicate_right]


end Bitvec
