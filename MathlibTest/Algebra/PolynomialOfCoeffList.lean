module

import Mathlib.Algebra.Polynomial.CoeffList

open Polynomial

example : ofCoeffList ([] : List ℤ) = 0 := by simp

example : ofCoeffList ([1, 2, 3] : List ℤ) = 1 + 2 * X + 3 * X ^ 2 := by
  simp only [ofCoeffList_cons, ofCoeffList_nil, map_ofNat, map_one]
  ring

example : (ofCoeffList ([1, 2, 3] : List ℤ)).coeff 1 = 2 := by simp

example : (ofCoeffList ([1, 2, 3] : List ℤ)).coeff 5 = 0 := by simp

example (P : ℤ[X]) : ofCoeffList P.coeffList.reverse = P := by simp

example : (ofCoeffList ([1, 2, 3] : List ℤ)).map (Int.castRingHom ℚ) = ofCoeffList [1, 2, 3] := by
  simp [map_ofCoeffList]

example : coeffScale 3 ([1, 2, 3] : List ℤ) = [3, 6, 9] := by decide

example : coeffAdd ([1, 2, 3] : List ℤ) [10, 20] = [11, 22, 3] := by decide

example : coeffShift ([1, 2] : List ℤ) = [0, 1, 2] := by decide

example : coeffSub ([5, 7] : List ℤ) [1, 2, 3] = [4, 5, -3] := by decide

example (p q : List ℤ) :
    ofCoeffList (coeffSub (coeffShift p) (coeffScale 2 q)) =
      X * ofCoeffList p - C 2 * ofCoeffList q := by
  rw [ofCoeffList_coeffSub, ofCoeffList_coeffShift, ofCoeffList_coeffScale]

example (p q : List ℤ) : ofCoeffList (coeffAdd p q) = ofCoeffList p + ofCoeffList q :=
  ofCoeffList_coeffAdd p q
