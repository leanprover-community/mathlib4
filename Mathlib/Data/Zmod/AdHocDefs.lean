import Mathlib.Data.Fin.Basic

/-!
# A partial ad-hoc port of some instances from `Mathlib/Data/Zmod/Defs.lean`

These should be replaced with the real port
-/

namespace Fin

instance (n) : CommSemigroup (Fin n) where
  mul_assoc a b c := by
    apply Fin.eq_of_val_eq
    simp only [Fin.mul_def]
    generalize lhs : ((a.val * b.val) % n * c.val) % n = l
    generalize rhs : a.val * (b.val * c.val % n) % n = r
    rw [← Nat.mod_eq_of_lt c.isLt, (Nat.mul_mod (a.val * b.val) c.val n).symm] at lhs
    rw [← Nat.mod_eq_of_lt a.isLt, (Nat.mul_mod a.val (b.val * c.val) n).symm,
        ← Nat.mul_assoc] at rhs
    rw [← lhs, ← rhs]
  mul_comm := Fin.mul_comm

instance (n) [NeZero n] : MonoidWithZero (Fin n) where
  __ := inferInstanceAs (CommSemigroup (Fin n))
  mul_one := Fin.mul_one
  one_mul := Fin.one_mul
  zero_mul := Fin.zero_mul
  mul_zero := Fin.mul_zero

-- Porting note: new
private theorem mul_add (a b c : Fin n) : a * (b + c) = a * b + a * c := by
    apply Fin.eq_of_val_eq
    simp [Fin.mul_def, Fin.add_def]
    generalize lhs : a.val * ((b.val + c.val) % n) % n = l
    rw [(Nat.mod_eq_of_lt a.isLt).symm, ← Nat.mul_mod] at lhs
    rw [← lhs, left_distrib]

-- Porting note: new
instance (n) [NeZero n] : CommSemiring (Fin n) where
  __ := inferInstanceAs (MonoidWithZero (Fin n))
  __ := inferInstanceAs (CommSemigroup (Fin n))
  __ := inferInstanceAs (AddCommMonoid (Fin n))
  __ := inferInstanceAs (AddMonoidWithOne (Fin n))
  left_distrib := Fin.mul_add
  right_distrib a b c := (by rw [mul_comm, Fin.mul_add, mul_comm c, mul_comm c])

section CommRing
/-- Modular projection `ℤ → Fin n` whenever `Fin n` is nonempty. -/
protected def ofInt'' [NeZero n] : Int → Fin n
  | Int.ofNat a => Fin.ofNat' a Fin.size_positive'
  | Int.negSucc a => -(Fin.ofNat' a.succ Fin.size_positive')

/-- Modular projection `ℤ → Fin n` whenever `Fin n` is nonempty. -/
def ofInt' [NeZero n] : ℤ → Fin n
  | (i : ℕ) => i
  | (Int.negSucc i) => -↑(i + 1 : ℕ)

instance [NeZero n] : AddGroupWithOne (Fin n) where
  __ := inferInstanceAs (AddMonoidWithOne (Fin n))
  sub_eq_add_neg := sub_eq_add_neg
  add_left_neg := add_left_neg
  intCast := Fin.ofInt'
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

instance [NeZero n] : CommRing (Fin n) where
  __ := inferInstanceAs (AddGroupWithOne (Fin n))
  __ := inferInstanceAs (CommSemiring (Fin n))

end CommRing

end Fin
