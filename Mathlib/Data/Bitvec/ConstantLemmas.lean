import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas

namespace Bitvec

/-- Every bit in `zero` is `0`/`false` -/
@[simp]
theorem get_zeroes_eq_false : get (Bitvec.zero n) i = false :=
  get_replicate_val_eq_val

@[simp]
theorem get_zero_eq_false : get 0 i = false :=
  get_replicate_val_eq_val

/-- Every bit in `ones` is `1`/`true` -/
@[simp]
theorem get_ones_eq_true : get (allOnes n) i = true :=
  get_replicate_val_eq_val

/-- The all-ones bit pattern is also spelled `-1` -/
@[simp]
theorem get_minus_one : get (-1 : Bitvec n) i = true := by
  rw[neg_one]; apply get_ones_eq_true

@[simp]
theorem ofNat_zero_succ : (Bitvec.ofNat (n+1) 0) = false ::ᵥ (Bitvec.ofNat n 0) := by
  induction n
  case zero =>
    rfl
  case succ n ih =>
    show Vector.append (Bitvec.ofNat (n+1) 0) (false ::ᵥ Vector.nil)
          = false ::ᵥ (Bitvec.ofNat (n+1) 0)
    rw[ih]
    apply eq_of_heq
    apply HEq.trans <| Vector.append_cons_left false (Bitvec.ofNat n 0) (false ::ᵥ Vector.nil)
    congr



@[simp]
theorem ofNat_zero_eq_zero : (Bitvec.ofNat n 0) = 0 := by
  simp only [OfNat.ofNat, Zero.zero, Bitvec.zero]
  induction n
  case zero =>
    rfl
  case succ n ih =>
    rw[ofNat_zero_succ, Vector.replicate_succ, ih]





end Bitvec
