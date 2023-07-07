import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Vector.Snoc

namespace Bitvec
  open Bitvec (zero one not)

/-- Every bit in `zero` is `0`/`false` -/
@[simp]
theorem get_zero_eq_false : get (0 : Bitvec n) i = false :=
  get_replicate ..

/-- Every bit in `ones` is `1`/`true` -/
@[simp]
theorem get_ones_eq_true : get (allOnes n) i = true :=
  get_replicate ..



section NegateConstants
@[simp]
theorem not_zero : ~~~ (allOnes n) = 0 := by
  ext; simp

@[simp]
theorem not_ones : ~~~ (0 : Bitvec n) = (allOnes n) := by
  ext; simp
end NegateConstants


section Zero

@[aesop 50%]
theorem zero_unfold : (0 : Bitvec (n+1)) = false ::ᵥ 0 := by
  rfl

@[aesop 50%]
theorem zero_unfold_snoc : (0 : Bitvec (n+1)) = Vector.snoc 0 false := by
  induction n
  . rfl
  . simp[zero_unfold, *]; congr

@[simp]
theorem toNat_zero : ∀ {n : Nat}, (0 : Bitvec n).toNat = 0
  | 0 => rfl
  | n+1 => by simpa only [Bitvec.toNat] using @toNat_zero n

@[simp]
theorem ofNat_zero : Bitvec.ofNat w 0 = 0 := by
  rw [← toNat_zero, ofNat_toNat]

theorem zero_eq_replicate :
    (0 : Bitvec n) = Vector.replicate n false  :=
  rfl

end Zero


section NegOne

private theorem toList_neg_one_aux : ∀ (n : ℕ),
(List.mapAccumr (fun y c ↦ (y || c, xor y c))
  (List.replicate n false ++ [true]) false) =
  (true, List.replicate (n+1) true)
| 0 => rfl
| n+1 => by rw [List.replicate_succ, List.cons_append, List.mapAccumr,
  toList_neg_one_aux n]; simp


/-- The all-ones bit pattern is also spelled `-1` -/
theorem neg_one : ∀ {n : ℕ}, (-1: Bitvec n) = Vector.replicate n true
  | 0 => rfl
  | n+1 => by
    show (Bitvec.one (n+1)).neg = Vector.replicate (n+1) true
    simp [Bitvec.neg, Bitvec.one, Vector.mapAccumr, Vector.replicate,
      Vector.append, List.cons_append, List.mapAccumr, toList_neg_one_aux n]


theorem toList_neg_one : ∀ {n : ℕ}, (-1 : Bitvec n).toList = List.replicate n true := by
  simp only [neg_one, Vector.replicate, Vector.toList_mk, forall_const, toList]



@[simp]
theorem ofInt_neg_one_eq_allOnes : (Bitvec.ofInt n (-1)) = allOnes n := by
  simp only [Bitvec.ofInt, Neg.neg, Int.neg, Int.negOfNat, ofNat_zero, not_ones]


end NegOne









end Bitvec
