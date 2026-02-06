/-
Copyright (c) 2025 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Ring.Idempotent

open TensorProduct

/-!
# Affine Algebraic Groups

An affine algebraic group over a field k is a smooth affine group scheme of finite type.
In Hopf algebra terms: a commutative Hopf k-algebra that is finitely generated and
geometrically reduced.

## Main definitions

* `AffineAlgGroup`: Typeclass for affine algebraic groups
* `AffineAlgGroup.AlgPoints`: The k-points G(k) as algebra homomorphisms (correct definition)
* `AffineAlgGroup.IsConnected`: G is connected (no nontrivial idempotents)
* `AffineAlgGroup.baseChangeAlg`: Base change G_K for a field extension K/k

## Known limitations

**WARNING**: This file contains preliminary definitions that are not yet mathematically
complete. The following issues are known:

1. **k-points via convolution**: The correct k-points `AlgPoints k A := A →ₐ[k] k` should
   have a group structure via convolution, not composition. The group instance is `sorry`
   pending development of the convolution group structure for algebra homomorphisms.

2. **GroupLike is NOT k-points**: The type `GroupLike k A` represents group-like elements
   of the Hopf algebra (elements g with Δ(g) = g ⊗ g), which always form a COMMUTATIVE
   group for commutative Hopf algebras. This is NOT the functor of points - for GL_n,
   the k-points are non-commutative!

3. **Base change**: The `HopfAlgebra K (K ⊗[k] A)` instance is `sorry`. The tensor product
   infrastructure exists in `Mathlib/RingTheory/HopfAlgebra/TensorProduct.lean` but needs
   to be adapted for the base change case.

## Implementation notes

An affine group scheme over k corresponds to a commutative Hopf algebra A over k.
The smoothness condition translates to A being geometrically reduced.

## TODO

* Implement convolution group structure on `AlgPoints`
* Show base change preserves the AffineAlgGroup structure
* Define closed subgroup schemes via Hopf subalgebras
* Examples: GL_n, SL_n, tori

## References

* Brian Conrad, "Reductive Group Schemes", Section 1
* Armand Borel, "Linear Algebraic Groups"
-/

variable (k A : Type*) [Field k] [CommRing A] [HopfAlgebra k A]

/-- An affine algebraic group over a field k is a commutative Hopf algebra that is
finitely generated as a k-algebra and geometrically reduced (smooth).

This corresponds to a smooth affine group scheme of finite type over Spec(k). -/
class AffineAlgGroup : Prop where
  /-- The coordinate ring is finitely generated as a k-algebra -/
  finiteType : Algebra.FiniteType k A
  /-- The coordinate ring is geometrically reduced (smoothness) -/
  geomReduced : Algebra.IsGeometricallyReduced k A

namespace AffineAlgGroup

/-!
### The k-points functor

The k-points of an affine group scheme G = Spec(A) are the k-algebra homomorphisms A → k.
These form a group under convolution:
- Multiplication: (f * g)(a) = ∑ f(a₁) · g(a₂) where Δ(a) = ∑ a₁ ⊗ a₂
- Identity: the counit ε : A → k
- Inverse: f⁻¹ = f ∘ S where S is the antipode

**Note**: `GroupLike k A` is NOT the correct type for k-points! It represents group-like
elements of the Hopf algebra, which always form a commutative group for commutative A.
-/

/-- The k-points of an affine algebraic group: algebra homomorphisms A → k.

This is the correct definition of the functor of points. For a Hopf algebra,
this carries a group structure via convolution (not composition). -/
def AlgPoints (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] := A →ₐ[k] k

/-- The group structure on k-points via convolution.

For a Hopf algebra A over k, the k-algebra homomorphisms A → k form a group where:
- Multiplication is convolution: (f * g)(a) = ∑ f(a₁) · g(a₂)
- The identity is the counit ε
- The inverse of f is f ∘ S (precomposition with the antipode)

**TODO**: This requires showing:
1. Convolution of two algebra homomorphisms is an algebra homomorphism
2. The counit is an algebra homomorphism (it is, by definition)
3. f ∘ S is an algebra homomorphism when S is an algebra anti-homomorphism -/
instance AlgPoints.instGroup : Group (AlgPoints k A) := sorry

/-- For a cocommutative Hopf algebra, the k-points form a commutative group. -/
instance AlgPoints.instCommGroup [Coalgebra.IsCocomm k A] : CommGroup (AlgPoints k A) := sorry

/-- **DEPRECATED**: Group-like elements of the Hopf algebra.

WARNING: This is NOT the correct k-points! For a commutative Hopf algebra, `GroupLike k A`
always forms a commutative group, which is wrong for non-abelian algebraic groups like GL_n.

Use `AlgPoints k A` instead for the functor of points. -/
@[deprecated AlgPoints (since := "2025-02-06")]
def points (k A : Type*) [Field k] [CommRing A] [HopfAlgebra k A] := GroupLike k A

/-!
### Connectedness

An affine algebraic group is connected if its coordinate ring has no nontrivial idempotents.
This is equivalent to Spec(A) being connected as a topological space.

Note: `IsDomain A` (integral domain) is strictly stronger than connectedness and is
not the correct notion. A ring can have no nontrivial idempotents without being a domain.
-/

/-- A ring has no nontrivial idempotents if every idempotent is 0 or 1.

This is the ring-theoretic characterization of Spec(R) being connected. -/
class NoNontrivialIdempotents (R : Type*) [Ring R] : Prop where
  /-- Every idempotent element is trivial (0 or 1) -/
  trivial_idempotent : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1

/-- An integral domain has no nontrivial idempotents. -/
instance NoNontrivialIdempotents.of_isDomain {R : Type*} [Ring R] [Nontrivial R]
    [NoZeroDivisors R] : NoNontrivialIdempotents R where
  trivial_idempotent e he := by
    -- e * e = e means e * (e - 1) = 0
    have h : e * (e - 1) = 0 := by simp [mul_sub, he.eq]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h with he0 | he1
    · left; exact he0
    · right; exact sub_eq_zero.mp he1

/-- An affine algebraic group is connected if its coordinate ring has no nontrivial idempotents.

This is equivalent to Spec(A) being a connected topological space. For a reduced ring
(which affine algebraic groups are), this is equivalent to Spec(A) being irreducible
iff A is a domain, but connectedness is the weaker and correct notion. -/
class IsConnected (k A : Type*) [Field k] [CommRing A] [HopfAlgebra k A]
    [AffineAlgGroup k A] : Prop where
  /-- The coordinate ring has no nontrivial idempotents -/
  connected : NoNontrivialIdempotents A

variable {k A}

/-- The base change of the coordinate ring to a field extension K/k.
This represents G_K, the group obtained by extending scalars. -/
def baseChangeAlg (K : Type*) [Field K] [Algebra k K] := K ⊗[k] A

section BaseChange

variable (K : Type*) [Field K] [Algebra k K]

/-!
### Base Change

When A is a Hopf algebra over k, the tensor product K ⊗[k] A inherits a Hopf algebra
structure over K. This is needed to define reductive groups (which require base change
to the algebraic closure).

The tensor product of Hopf algebras is implemented in
`Mathlib/RingTheory/HopfAlgebra/TensorProduct.lean`, but adapting it for base change
requires some additional work.
-/

/-- The base change K ⊗[k] A inherits a Hopf algebra structure.

TODO: Use the tensor product infrastructure from `HopfAlgebra/TensorProduct.lean`.
The instance there is for `HopfAlgebra S (B ⊗[R] A)` when both B and A are Hopf algebras.
For base change, we need to treat K as a (trivial) Hopf algebra over itself. -/
instance baseChangeHopfAlgebra [HopfAlgebra k A] : HopfAlgebra K (K ⊗[k] A) := sorry

/-- The base change preserves finite type.

This uses the existing `Algebra.FiniteType.baseChange` instance from
`Mathlib/RingTheory/FiniteStability.lean`. -/
instance baseChangeFiniteType [Algebra.FiniteType k A] :
    Algebra.FiniteType K (K ⊗[k] A) :=
  inferInstance

/-- If A is an affine algebraic group over k, then K ⊗[k] A is one over K.

The key point is that geometric reducedness is preserved: if A ⊗_k k̄ is reduced,
then (K ⊗_k A) ⊗_K K̄ ≅ A ⊗_k K̄ is also reduced (where K̄ is an algebraic
closure of K containing k̄). -/
instance baseChangeAffineAlgGroup [AffineAlgGroup k A] :
    AffineAlgGroup K (K ⊗[k] A) := sorry

end BaseChange

end AffineAlgGroup
