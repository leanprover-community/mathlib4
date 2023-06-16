import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas

namespace Bitvec
  open Bitvec (zero one not)

/-- Every bit in `zero` is `0`/`false` -/
@[simp]
theorem get_zeroe_eq_false : get (zero n) i = false :=
  get_replicate_val_eq_val

/-- Every bit in `ones` is `1`/`true` -/
@[simp]
theorem get_ones_eq_true : get (allOnes n) i = true :=
  get_replicate_val_eq_val



section NegateConstants
  @[simp]
  theorem not_zeroes : not (allOnes n) = zero n := by
    ext; simp

  @[simp]
  theorem not_ones : not (zero n) = (allOnes n) := by
    ext; simp
end NegateConstants


section Zero
  @[simp]
  theorem ofNat_zero_eq_zero : (Bitvec.ofNat n 0) = zero n := by
    simp only [OfNat.ofNat, Zero.zero, Bitvec.zero]
    induction n
    case zero =>
      rfl
    case succ n ih =>
      show (Bitvec.ofNat n 0).snoc false
            = (Vector.replicate (n+1) false)
      rw[Vector.replicate_succ_to_snoc, ih]


  @[simp]
  theorem zero_eq_bitvec_zero : 0 = (zero n) :=
    rfl

  @[aesop 50%]
  theorem zero_unfold : (zero (n+1)) = false ::ᵥ 0 := by
    rfl

  @[aesop 50%]
  theorem zero_unfold_snoc : (zero (n+1)) = Vector.snoc 0 false := by
    induction n
    . rfl
    . simp[zero_unfold, *]; congr
end Zero


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
  theorem neg_one_eq_allOnes : (-1 : Bitvec n) = allOnes n :=
    neg_one

  @[simp]
  theorem ofInt_neg_one_eq_allOnes : (Bitvec.ofInt n (-1)) = allOnes n := by
    simp only [Bitvec.ofInt, Neg.neg, Int.neg, Int.negOfNat, ofNat_zero_eq_zero, not_ones]


end NegOne









end Bitvec
