import Mathlib

universe u

/-- `R[X]/(X^2−a*X−b)` -/
@[ext]
structure QuadraticAlgebra (R : Type u) (a b : R) : Type u where
  re : R
  im : R

namespace QuadraticAlgebra

variable {R : Type u} [CommSemiring R] {a b : R}

def ofInt (n : R) : QuadraticAlgebra R a b :=
  ⟨n, 0⟩

theorem ofInt_re (n : R) : (ofInt n : QuadraticAlgebra R a b).re = n :=
  rfl

theorem ofInt_im (n : R) : (ofInt n : QuadraticAlgebra R a b).im = 0 :=
  rfl

/-- The zero of the ring -/
instance : Zero (QuadraticAlgebra R a b) :=
  ⟨ofInt 0⟩

@[simp]
theorem zero_re : (0 : QuadraticAlgebra R a b).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : QuadraticAlgebra R a b).im = 0 :=
  rfl

/-- The one of the ring -/
instance : One (QuadraticAlgebra R a b) :=
  ⟨ofInt 1⟩

@[simp]
theorem one_re : (1 : QuadraticAlgebra R a b).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : QuadraticAlgebra R a b).im = 0 :=
  rfl

instance : Add (QuadraticAlgebra R a b) :=
  ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]
theorem add_re (z w : QuadraticAlgebra R a b) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
theorem add_im (z w : QuadraticAlgebra R a b) : (z + w).im = z.im + w.im :=
  rfl

instance : Mul (QuadraticAlgebra R a b) :=
  ⟨fun z w => ⟨z.1 * w.1 + b * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + a * z.2 * w.2⟩⟩

@[simp]
theorem mul_re (z w : QuadraticAlgebra R a b) :
    (z * w).re = z.re * w.re + b * z.im * w.im :=
  rfl

@[simp]
theorem mul_im (z w : QuadraticAlgebra R a b) :
    (z * w).im = z.re * w.im + z.im * w.re + a * z.im * w.im :=
  rfl

instance addCommMonoid : AddCommMonoid (QuadraticAlgebra R a b) := by
  refine
  { add := (· + ·)
    zero := 0
    nsmul n z := ⟨n • z.1, n • z.2⟩
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    add_comm := ?_
    nsmul_zero := ?_
    nsmul_succ := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm, add_mul]

instance addMonoidWithOne : AddMonoidWithOne (QuadraticAlgebra R a b) :=
  { QuadraticAlgebra.addCommMonoid with
    natCast := fun n => ofInt n
    natCast_zero := by ext <;> simp [ofInt_re, ofInt_im]
    natCast_succ := fun n => by
      ext <;> simp [ofInt_re, ofInt_im, Nat.succ_eq_add_one]
    one := 1 }

instance commSemiring : CommSemiring (QuadraticAlgebra R a b) := by
  refine
  { addMonoidWithOne with
    mul := (· * ·)
    npow := @npowRec (QuadraticAlgebra R a b) ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

end QuadraticAlgebra
