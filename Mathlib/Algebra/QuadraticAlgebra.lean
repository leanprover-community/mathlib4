import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Ring.RingNF

universe u

/-- `R[X]/(X^2−a*X−b)` -/
@[ext]
structure QuadraticAlgebra (R : Type u) (a b : R) : Type u where
  re : R
  im : R

namespace QuadraticAlgebra

variable {R : Type u}

section SMul


variable {α} [SMul α R] {a b : R}

instance : SMul α (QuadraticAlgebra R a b) where
  smul a z := ⟨a • z.1, a • z.2⟩

@[simp]
theorem re_smul (r : α) (z : QuadraticAlgebra R a b) : (r • z).re = r • z.re := rfl

@[simp]
theorem im_smul (r : α) (z : QuadraticAlgebra R a b) : (r • z).im = r • z.im := rfl

end SMul

variable [CommSemiring R] {a b : R}

def ofInt (n : R) : QuadraticAlgebra R a b :=
  ⟨n, 0⟩

theorem re_ofInt (n : R) : (ofInt n : QuadraticAlgebra R a b).re = n :=
  rfl

theorem im_ofInt (n : R) : (ofInt n : QuadraticAlgebra R a b).im = 0 :=
  rfl

/-- The zero of the ring -/
instance : Zero (QuadraticAlgebra R a b) :=
  ⟨ofInt 0⟩

@[simp]
theorem re_zero : (0 : QuadraticAlgebra R a b).re = 0 :=
  rfl

@[simp]
theorem im_zero : (0 : QuadraticAlgebra R a b).im = 0 :=
  rfl

/-- The one of the ring -/
instance : One (QuadraticAlgebra R a b) :=
  ⟨ofInt 1⟩

@[simp]
theorem re_one : (1 : QuadraticAlgebra R a b).re = 1 :=
  rfl

@[simp]
theorem im_one : (1 : QuadraticAlgebra R a b).im = 0 :=
  rfl

instance : Add (QuadraticAlgebra R a b) :=
  ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]
theorem re_add (z w : QuadraticAlgebra R a b) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
theorem im_add (z w : QuadraticAlgebra R a b) : (z + w).im = z.im + w.im :=
  rfl

instance : Mul (QuadraticAlgebra R a b) :=
  ⟨fun z w => ⟨z.1 * w.1 + b * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + a * z.2 * w.2⟩⟩

@[simp]
theorem re_mul (z w : QuadraticAlgebra R a b) :
    (z * w).re = z.re * w.re + b * z.im * w.im :=
  rfl

@[simp]
theorem im_mul (z w : QuadraticAlgebra R a b) :
    (z * w).im = z.re * w.im + z.im * w.re + a * z.im * w.im :=
  rfl


instance addCommMonoid : AddCommMonoid (QuadraticAlgebra R a b) := by
  refine
  { add := (· + ·)
    zero := 0
    nsmul n z := n • z
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
    natCast_zero := by ext <;> simp [re_ofInt, im_ofInt]
    natCast_succ := fun n => by
      ext <;> simp [re_ofInt, im_ofInt, Nat.succ_eq_add_one]
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
