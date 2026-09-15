/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Tactic.Hessenberg.Recurrence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# The coefficient-level mirror of the Hessenberg recurrence
-/

public section

open Polynomial

namespace Mathlib.Tactic.Hessenberg

variable {R : Type*} [CommRing R]

/-- The Array version of `hessP`. -/
@[expose]
def coeffHessSum (n : ℕ) (H : Array R) (kcol : ℕ) :
    (i : ℕ) → (beta : R) → Array (List R) → List R
  | 0, beta, ps => (ps.getD 0 []).map (H.getD (n * 0 + kcol) 0 * beta * ·)
  | i + 1, beta, ps =>
    List.zipWithAll (fun a b => a.getD 0 + b.getD 0)
      ((ps.getD (i + 1) []).map (H.getD (n * (i + 1) + kcol) 0 * beta * ·))
      (coeffHessSum n H kcol i (beta * H.getD (n * (i + 1) + i) 0) ps)

/-- The Array version of one step of `hessP`. -/
@[expose]
def coeffHessStep (n : ℕ) (H : Array R) (k : ℕ) (ps : Array (List R)) : List R :=
  match k with
  | 0 => [1]
  | 1 =>
    List.zipWithAll (fun a b => a.getD 0 - b.getD 0) (0 :: ps.getD 0 [])
      ((ps.getD 0 []).map (H.getD (n * 0 + 0) 0 * ·))
  | k' + 2 =>
    List.zipWithAll (fun a b => a.getD 0 - b.getD 0)
      (List.zipWithAll (fun a b => a.getD 0 - b.getD 0) (0 :: ps.getD (k' + 1) [])
        ((ps.getD (k' + 1) []).map (H.getD (n * (k' + 1) + (k' + 1)) 0 * ·)))
      (coeffHessSum n H (k' + 1) k' (H.getD (n * (k' + 1) + k') 0) ps)

/-- The Arrays representing the results `hessP n H 0`, ..., `hessP n H k`. -/
@[expose]
def coeffHessAux (n : ℕ) (H : Array R) : ℕ → Array (List R)
  | 0 => #[[1]]
  | k + 1 =>
    let ps := coeffHessAux n H k
    ps.push (coeffHessStep n H (k + 1) ps)

/-- The Array version of `hessCharPoly`. -/
@[expose]
def coeffHessCharPoly (n : ℕ) (H : Array R) : List R :=
  (coeffHessAux n H n).getD n []

theorem ofCoeffList_coeffHessSum (n : ℕ) (H : Array R) (kcol : ℕ) :
    ∀ (i : ℕ) (beta : R) (ps : Array (List R)),
      ofCoeffList (coeffHessSum n H kcol i beta ps) =
        ∑ t : Fin (i + 1),
          C (H.getD (n * (t : ℕ) + kcol) 0 *
              (beta * ∏ j ∈ Finset.Ico (t : ℕ) i, H.getD (n * (j + 1) + j) 0)) *
            ofCoeffList (ps.getD (t : ℕ) [])
  | 0, beta, ps => by simp [coeffHessSum]
  | i + 1, beta, ps => by
    rw [Fin.sum_univ_castSucc, coeffHessSum, ofCoeffList_zipWithAll_add, ofCoeffList_map_mul,
      ofCoeffList_coeffHessSum, add_comm]
    simp only [Fin.val_castSucc, Fin.val_last, Finset.Ico_self, Finset.prod_empty, mul_one]
    congrm ∑ t, ?_ + _
    rw [Finset.prod_Ico_succ_top (Nat.lt_succ_iff.mp t.isLt)]
    simp only [map_mul]
    ring

theorem ofCoeffList_coeffHessStep (n : ℕ) (H : Array R) (k : ℕ) (ps : Array (List R)) :
    ofCoeffList (coeffHessStep n H (k + 1) ps) =
      (X - C (H.getD (n * k + k) 0)) * ofCoeffList (ps.getD k []) -
        ∑ t : Fin k,
          C (H.getD (n * (t : ℕ) + k) 0 * ∏ j ∈ Finset.Ico (t : ℕ) k, H.getD (n * (j + 1) + j) 0) *
            ofCoeffList (ps.getD (t : ℕ) []) := by
  cases k with
  | zero =>
    simp [coeffHessStep, sub_mul]
  | succ k =>
    rw [coeffHessStep, ofCoeffList_zipWithAll_sub, ofCoeffList_zipWithAll_sub,
      ofCoeffList_zero_cons, ofCoeffList_map_mul, ofCoeffList_coeffHessSum, sub_mul]
    congrm _ - ∑ t, ?_
    rw [Finset.prod_Ico_succ_top (Nat.lt_succ_iff.mp t.isLt)]
    simp only [map_mul]
    ring

theorem coeffHessAux_size (n : ℕ) (H : Array R) : ∀ k, (coeffHessAux n H k).size = k + 1
  | 0 => rfl
  | k + 1 => by rw [coeffHessAux, Array.size_push, coeffHessAux_size n H k]

theorem ofCoeffList_coeffHessAux_getD (n : ℕ) (H : Array R) :
    ∀ k m, m ≤ k → ofCoeffList ((coeffHessAux n H k).getD m []) = hessP n H m
  | 0, m, hm => by
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    simp [coeffHessAux, ofCoeffList_cons, hessP_zero]
  | k + 1, m, hm => by
    rw [coeffHessAux, Array.getD_eq_getD_getElem?, Array.getElem?_push, coeffHessAux_size]
    split_ifs with hmk
    · subst hmk
      rw [Option.getD_some, ofCoeffList_coeffHessStep, hessP_succ]
      simp (disch := omega) only [ofCoeffList_coeffHessAux_getD n H k]
    · rw [← Array.getD_eq_getD_getElem?]
      exact ofCoeffList_coeffHessAux_getD n H k m (by omega)

theorem hessCharPoly_eq_ofCoeffList (n : ℕ) (H : Array R) :
    hessCharPoly n H = ofCoeffList (coeffHessCharPoly n H) := by
  rw [hessCharPoly_eq, coeffHessCharPoly, ofCoeffList_coeffHessAux_getD n H n n le_rfl]

end Mathlib.Tactic.Hessenberg

end
