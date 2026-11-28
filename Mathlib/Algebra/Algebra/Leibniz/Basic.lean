/-
Copyright (c) 2026 Viviana del Barco, Gustavo Infanti, Exequiel Rivas and Paul Schwahn.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Span.Defs

import Aesop.BuiltinRules
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Module
import Mathlib.Tactic.TypeStar
/-!
# Leibniz rings and algebras

A **right Leibniz ring** is a non-unital, non-associative ring satisfying
`(x * y) * z = (x * z) * y + x * (y * z)` for all `x`, `y`, and `z`.

We study Leibniz algebras by additionally assuming a module structure
with bilinear multiplication.

## Main definitions

* `IsLeibniz`: the right Leibniz identity.
* `Submodule.spanOfSquares`: the linear span of the squares `x * x`.
* `Submodule.spanOfMulSubmodules`: the linear span of products between two submodules
  in both orders.
* `NonUnitalNonAssocSemiring.IsSkew`: the condition that every element squares to zero.

## Main results

* `Leibniz.mul_left_mul_self`: multiplying a square on the left by any element gives zero.
* `Leibniz.squareSpan_left_mul_mem` and `Leibniz.squareSpan_right_mul_mem`: the span of
  squares is stable under left and right multiplication, assuming the corresponding
  compatibility with scalar multiplication.
* `Leibniz.instLieRing` and `Leibniz.instLieAlgebra`: a Leibniz ring or algebra in which
  every element squares to zero carries a Lie structure with bracket given by multiplication.
* `Leibniz.ofLieRing`: every Lie ring satisfies the right Leibniz identity when its bracket
  is used as multiplication.

## Implementation notes

`Leibniz.ofLieRing` uses the ring structure `LieRing.toNonUnitalNonAssocRing` explicitly;
it does not install a global multiplication on Lie rings.

## References

* https://en.wikipedia.org/wiki/Leibniz_algebra
-/

public section

/-- The right Leibniz identity for a non-unital, non-associative ring. -/
@[mk_iff isLeibniz_iff]
class IsLeibniz (A : Type*) [NonUnitalNonAssocRing A] : Prop where
  leibniz' (x y z : A) : (x * y) * z = (x * z) * y + x * (y * z)

namespace Leibniz

variable {A : Type*} [NonUnitalNonAssocRing A] [IsLeibniz A]

/-- The right Leibniz identity. -/
theorem leibniz (x y z : A) : (x * y) * z = (x * z) * y + x * (y * z) :=
  IsLeibniz.leibniz' x y z

/-- The right Leibniz identity expressed as a formula for `x * (y * z)`. -/
theorem mul_left_mul (x y z : A) : x * (y * z) = (x * y) * z - (x * z) * y := by
  rw [leibniz]
  simp only [add_sub_cancel_left]

/-- Multiplying a square on the left by any element gives zero. -/
theorem mul_left_mul_self (x z : A) : z * (x * x) = 0 := by
  rw [mul_left_mul, sub_self]

/-- Swapping the factors of the inner product negates `x * (y * z)`. -/
theorem mul_left_mul_anticomm (x y z : A) : x * (y * z) = - (x * (z * y)) := by
  rw [mul_left_mul, mul_left_mul, neg_sub]

end Leibniz

namespace Submodule

/-- The `R`-linear span of the squares `x * x` in `A`. -/
def spanOfSquares (R A : Type*) [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
    : Submodule R A :=
  Submodule.span R (Set.range fun x : A => x * x)

/-- Every symmetrized product belongs to the span of squares. -/
theorem symm_SpanOfSquares_mem {R A : Type*} [Ring R] [NonUnitalNonAssocRing A] [Module R A]
    (x y : A) : x * y + y * x ∈ spanOfSquares R A:= by
  have : x * y + y * x = (x + y) * (x + y) - x * x - y * y := by
    rw [add_mul, mul_add, mul_add]
    abel
  rw [this]
  refine sub_mem (sub_mem ?_ ?_) ?_ <;> exact Submodule.subset_span ⟨_, rfl⟩

/-- The `R`-linear span of all products `u * v` and `v * u` with `u ∈ U` and `v ∈ V`. -/
def spanOfMulSubmodules {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
    (U V : Submodule R A) : Submodule R A := Submodule.span R
    (Set.range (fun p : U × V => (p.1 : A) * (p.2 : A)) ∪
      Set.range (fun p : V × U => (p.1 : A) * (p.2 : A)))

/-- A product of elements of `U` and `V` belongs to their product span. -/
@[simp]
theorem mem_bracketSpan_of_mem {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
    {U V : Submodule R A} {x y : A} (hx : x ∈ U) (hy : y ∈ V) :
    x * y ∈ spanOfMulSubmodules (R := R) (A := A) U V :=
  Submodule.subset_span (Or.inl ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩)

/-- A product in the reverse order also belongs to the product span of `U` and `V`. -/
@[simp]
theorem mem_bracketSpan_of_mem_swap {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A]
    [Module R A] {U V : Submodule R A} {x y : A} (hx : x ∈ U) (hy : y ∈ V) :
    y * x ∈ spanOfMulSubmodules (R := R) (A := A) U V :=
  Submodule.subset_span (Or.inr ⟨(⟨y, hy⟩, ⟨x, hx⟩), rfl⟩)

end Submodule

namespace Leibniz

open Submodule

/-- The span of squares is stable under left multiplication in a right Leibniz ring. -/
lemma squareSpan_left_mul_mem
    {R : Type*} [Semiring R] {A : Type*} [NonUnitalNonAssocRing A]
    [IsLeibniz A] [Module R A] [SMulCommClass R A A] (a : A) :
    map (LinearMap.mulLeft R a) (spanOfSquares R A) ≤ spanOfSquares R A := by
  dsimp [spanOfSquares]
  rw [map_span_le (LinearMap.mulLeft R a) (Set.range fun x : A => x * x)
    (span R (Set.range fun x ↦ x * x))]
  intro x ⟨y, hy⟩
  simp only at hy
  simp only [LinearMap.mulLeft_apply]
  rw [← hy, mul_left_mul_self]
  apply zero_mem

/-- The span of squares is stable under right multiplication in a right Leibniz ring. -/
lemma squareSpan_right_mul_mem {R : Type*} [Ring R] {A : Type*}
      [NonUnitalNonAssocRing A] [IsLeibniz A] [Module R A] [IsScalarTower R A A] (a : A) :
    map (LinearMap.mulRight R a) (spanOfSquares R A) ≤
      spanOfSquares R A := by
  dsimp [spanOfSquares]
  rw [map_span_le (LinearMap.mulRight R a) (Set.range fun x : A => x * x)
    (span R (Set.range fun x ↦ x * x))]
  intro x ⟨y, hy⟩
  simp only at hy
  simp only [LinearMap.mulRight_apply]
  rw [← hy,Leibniz.leibniz y y a]
  exact symm_SpanOfSquares_mem (R := R) (y * a) y

end Leibniz

namespace NonUnitalNonAssocSemiring

/-- The condition that every element of a non-unital, non-associative semiring squares to zero.
For a unital ring, this condition forces `1 = 0`. -/
class IsSkew (A : Type*) [NonUnitalNonAssocSemiring A] where
  skew (x : A) : x * x = 0

end NonUnitalNonAssocSemiring

namespace Leibniz

open NonUnitalNonAssocSemiring

/-- A Leibniz ring in which every element squares to zero is a Lie ring,
with bracket given by multiplication. -/
instance instLieRing {A : Type*} [NonUnitalNonAssocRing A] [IsLeibniz A] [IsSkew A] :
    LieRing A := {
  bracket := fun x y ↦ x * y
  add_lie := add_mul
  lie_add := smul_add
  lie_self := IsSkew.skew
  leibniz_lie := by
    intro x y z
    rw [mul_left_mul]
    have : (y + x * z) * y + (y + x * z) * (x * z) = 0 := by
      rw [← mul_add]
      apply IsSkew.skew
    simp only [← neg_eq_iff_add_eq_zero, add_mul, add_mul, IsSkew.skew, zero_add, add_zero] at this
    rw [sub_eq_add_neg, this]
}

/-- A Leibniz algebra in which every element squares to zero is a Lie algebra,
with bracket given by multiplication. -/
instance instLieAlgebra {R : Type*} [CommRing R] {A : Type*} [NonUnitalNonAssocRing A]
      [IsLeibniz A] [IsSkew A] [Module R A] [SMulCommClass R A A] :
    LieAlgebra R A := {
  lie_smul := by
    intro r x y
    change x * (r • y) = r • (x * y)
    rw [← smul_eq_mul, ← smul_eq_mul, ← smul_comm]
}

section OfLie

/-- A Lie ring satisfies the right Leibniz identity when its bracket is used as multiplication
via `LieRing.toNonUnitalNonAssocRing`. -/
instance ofLieRing {A : Type*} [LieRing A] : @IsLeibniz A (LieRing.toNonUnitalNonAssocRing A):= by
  let _ := LieRing.toNonUnitalNonAssocRing A
  exact {
  leibniz' := by
    intro x y z
    change ⁅⁅x, y⁆, z⁆ = ⁅⁅x, z⁆, y⁆ + ⁅x, ⁅y, z⁆⁆
    rw [lie_lie,add_comm]
    refine sub_eq_iff_eq_add.mpr ?_
    abel_nf
    refine left_eq_add.mpr ?_
    rw [← lie_skew]
    module }

end OfLie

end Leibniz
