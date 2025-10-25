import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.NonUnitalSubalgebra

set_option autoImplicit true

section Delab
variable {M : Type u} [Monoid M] (S S' : Submonoid M)

set_option linter.style.commandStart false

/-- info: ↥S → ↥S' : Type u -/
#guard_msgs in #check S → S'

/-- info: ↥S : Type u -/
#guard_msgs in #check {x // x ∈ S}

/-- info: { x // 1 * x ∈ S } : Type u -/
#guard_msgs in #check {x // 1 * x ∈ S}

end Delab

example [Ring R] (S : Subring R) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (n m : ℕ) :
    n • x ^ 3 - 2 • y + z ^ m ∈ S := by
  aesop

example [Ring R] (S : Set R) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (n m : ℕ) :
    n • x ^ 3 - y + z ^ m ∈ Subring.closure S := by
  aesop

example [CommRing R] [Ring A] [Algebra R A]
    (r : R) (a b c : A) (n : ℕ) :
    -b + (algebraMap R A r) + a ^ n * c ∈ Algebra.adjoin R {a, b, c} := by
  aesop

example [CommRing R] [Ring A] [Algebra R A] [StarRing R] [StarRing A] [StarModule R A]
    (r : R) (a b c : A) (n : ℕ) :
    -b + star (algebraMap R A r) + a ^ n * c ∈ StarAlgebra.adjoin R {a, b, c} := by
  aesop

example [Monoid M] (x : M) (n : ℕ) : x ^ n ∈ Submonoid.closure {x} := by
  aesop

example [Monoid M] (x y z w : M) (n : ℕ) : (x * y) ^ n * w ∈ Submonoid.closure {x, y, z, w} := by
  aesop

example [Group M] (x : M) (n : ℤ) : x ^ n ∈ Subgroup.closure {x} := by
  aesop

example [Monoid M] (x y z : M) (S₁ S₂ : Submonoid M) (h : S₁ ≤ S₂) (hx : x ∈ S₁)
    (hy : y ∈ S₁) (hz : z ∈ S₂) :
    x * y * z ∈ S₂ := by
  aesop

example [Monoid M] (x y z : M) (S₁ S₂ : Submonoid M) (h : S₁ ≤ S₂) (hx : x ∈ S₁)
    (hy : y ∈ S₁) (hz : z ∈ S₂) :
    x * y * z ∈ S₁ ⊔ S₂ := by
  aesop

example [Monoid M] (x y z : M) (S : Submonoid M) (hxy : x * y ∈ S) (hz : z ∈ S) :
    z * (x * y) ∈ S := by
  aesop

example [Field F] (S : Subfield F) (q : ℚ) : (q : F) ∈ S := by
  aesop

example [Field F] (S : Subfield F) : (1.2 : F) ∈ S := by
  aesop

example [Field F] (S : Subfield F) (x : F) (hx : x ∈ S) : ((12e-100 : F) • x⁻¹) ∈ S := by
  aesop
