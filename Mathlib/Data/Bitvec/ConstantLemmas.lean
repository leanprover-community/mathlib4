import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas

namespace Bitvec

open Bitvec (zero one not)


/-!
  ### Negation
  Show how bitwise negation relates various constants
-/
section NegateConstants
  @[simp]
  theorem not_zero : not (negOne n) = zero n := by
    ext; simp

  @[simp]
  theorem not_ones : not (zero n) = (negOne n) := by
    ext; simp
end NegateConstants




section NegOne
  private theorem toList_neg_one_aux : ∀ (n : ℕ),
  (List.mapAccumr (fun y c ↦ (y || c, xor y c))
    (List.replicate n false ++ [true]) false) =
    (true, List.replicate (n+1) true)
  | 0 => rfl
  | n+1 => by rw [List.replicate_succ, List.cons_append, List.mapAccumr,
    toList_neg_one_aux n]; simp


  theorem neg_one : ∀ {n : ℕ}, (-1: Bitvec n) = Vector.replicate n true
    | 0 => rfl
    | n+1 => by
      show (Bitvec.one (n+1)).neg = Vector.replicate (n+1) true
      simp [Bitvec.neg, Bitvec.one, Vector.mapAccumr, Vector.replicate,
        Vector.append, List.cons_append, List.mapAccumr, toList_neg_one_aux n]


  theorem toList_neg_one : ∀ {n : ℕ}, (-1 : Bitvec n).toList = List.replicate n true := by
    simp only [neg_one, Vector.replicate, Vector.toList_mk, forall_const, toList]

  /-- The all-ones bit pattern is also spelled `-1` -/
  @[simp]
  theorem neg_one_eq_allOnes : (-1 : Bitvec n) = negOne n :=
    neg_one

  @[simp]
  theorem ofInt_neg_one_eq_negOne : (Bitvec.ofInt n (-1)) = negOne n := by
    simp only [Bitvec.ofInt, Neg.neg, Int.neg, Int.negOfNat, ofNat_zero_eq_zero, not_ones]


end NegOne









end Bitvec
