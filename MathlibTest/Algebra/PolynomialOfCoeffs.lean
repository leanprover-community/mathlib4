module

import Mathlib.Algebra.Polynomial.CoeffList

open Polynomial

example : ofCoeffs ([] : List ℤ) = 0 := by simp

example : ofCoeffs ([1, 2, 3] : List ℤ) = 1 + 2 * X + 3 * X ^ 2 := by
  simp only [ofCoeffs_cons, ofCoeffs_nil, map_ofNat, map_one]
  ring

example : (ofCoeffs ([1, 2, 3] : List ℤ)).coeff 1 = 2 := by simp

example : (ofCoeffs ([1, 2, 3] : List ℤ)).coeff 5 = 0 := by simp

example (P : ℤ[X]) : ofCoeffs P.coeffList.reverse = P := by simp

example : (ofCoeffs ([1, 2, 3] : List ℤ)).map (Int.castRingHom ℚ) = ofCoeffs [1, 2, 3] := by
  simp [map_ofCoeffs]

example : coeffScale 3 ([1, 2, 3] : List ℤ) = [3, 6, 9] := by decide

example : coeffAdd ([1, 2, 3] : List ℤ) [10, 20] = [11, 22, 3] := by decide

example : coeffShift ([1, 2] : List ℤ) = [0, 1, 2] := by decide

example : coeffSub ([5, 7] : List ℤ) [1, 2, 3] = [4, 5, -3] := by decide

example (p q : List ℤ) :
    ofCoeffs (coeffSub (coeffShift p) (coeffScale 2 q)) = X * ofCoeffs p - C 2 * ofCoeffs q := by
  rw [ofCoeffs_coeffSub, ofCoeffs_coeffShift, ofCoeffs_coeffScale]

example (p q : List ℤ) : ofCoeffs (coeffAdd p q) = ofCoeffs p + ofCoeffs q :=
  ofCoeffs_coeffAdd p q
