/-
Copyright (c) 2025 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.AlgebraicGroup.Defs
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Unipotent Elements and Unipotent Radical

Over an algebraically closed field, an element g ∈ G(k) is unipotent if for any faithful
finite-dimensional representation, the endomorphism (ρ(g) - 1) is nilpotent.

The unipotent radical R_u(G) is the maximal connected normal unipotent subgroup.

## Main definitions

* `IsUnipotent`: Predicate for unipotent elements in G(k)
* `unipotentRadical`: The unipotent radical of G over an algebraically closed field
* `unipotentRadical_isTrivial`: Predicate that the unipotent radical is trivial

## Implementation notes

The definition of `IsUnipotent` is simplified: we say g is unipotent if (g - 1) is nilpotent
directly in the Hopf algebra A. This agrees with the standard definition for linear algebraic
groups (embedded in GL_n), because group-like elements correspond to invertible matrices,
and an invertible matrix M has (M - 1) nilpotent iff all eigenvalues of M are 1.

The full definition via faithful representations would require:
1. Defining comodules over A (which correspond to representations of G)
2. Defining "faithful" comodules (injective coaction)
3. Showing the definition is independent of the choice of faithful comodule

The unipotent radical is defined using `sorry`; the full construction requires showing
that the set of connected normal unipotent subgroups has a maximum, which uses
dimension theory for algebraic groups.

## References

* Brian Conrad, "Reductive Group Schemes", Section 1.1 (Definition 1.1.5)
* Armand Borel, "Linear Algebraic Groups", Section 4.4
-/

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {A : Type*} [CommRing A] [HopfAlgebra k A] [AffineAlgGroup k A]

/-- An element g ∈ G(k) is unipotent if (g - 1) is nilpotent in A.

Over an algebraically closed field, this is equivalent to: for every faithful
finite-dimensional representation ρ : G → GL_n, the endomorphism ρ(g) - 1 is nilpotent
(equivalently, all eigenvalues of ρ(g) are 1, equivalently, ρ(g) is conjugate to an
upper triangular matrix with 1's on the diagonal).

**Simplified definition**: We define unipotence directly in terms of nilpotence in the
coordinate ring. This is correct for linear algebraic groups and avoids the need for
comodule theory. -/
def IsUnipotent (g : GroupLike k A) : Prop :=
  IsNilpotent ((g : A) - 1)

/-- Unipotent elements are closed under multiplication.

Proof sketch: If (g-1) and (h-1) are nilpotent, then gh - 1 = (g-1)(h-1) + (g-1) + (h-1)
is nilpotent because the sum of commuting nilpotent elements is nilpotent.
Note: g and h commute with their differences from 1, so this works. -/
theorem IsUnipotent.mul {g h : GroupLike k A} (hg : IsUnipotent g) (hh : IsUnipotent h) :
    IsUnipotent (g * h) := sorry

/-- The identity is unipotent (trivially: 1 - 1 = 0 is nilpotent). -/
theorem isUnipotent_one : IsUnipotent (1 : GroupLike k A) := by
  unfold IsUnipotent
  simp only [GroupLike.val_one, sub_self]
  exact ⟨1, pow_one 0⟩

/-- If g is unipotent, so is g⁻¹.

Proof sketch: If g - 1 is nilpotent, say (g-1)^n = 0, then we can write
g⁻¹ = (1 - (1-g))⁻¹ = 1 + (1-g) + (1-g)² + ... + (1-g)^{n-1}
so g⁻¹ - 1 = (1-g) + (1-g)² + ... = (1-g)(1 + (1-g) + ... + (1-g)^{n-2})
which shows g⁻¹ - 1 is divisible by (1-g) = -(g-1), hence nilpotent. -/
theorem IsUnipotent.inv {g : GroupLike k A} (hg : IsUnipotent g) :
    IsUnipotent g⁻¹ := sorry

/-- If g is unipotent, so is any conjugate hgh⁻¹. -/
theorem IsUnipotent.conj {g h : GroupLike k A} (hg : IsUnipotent g) :
    IsUnipotent (h * g * h⁻¹) := sorry

section UnipotentRadical

/-!
### The Unipotent Radical

The unipotent radical of an affine algebraic group G over an algebraically closed field
is the maximal connected normal unipotent subgroup.

For now, we define this as a subgroup of G(k) and state the required properties as theorems
with `sorry` proofs. A full implementation would:
1. Define closed subgroups via Hopf subalgebras (quotients of A)
2. Define connected closed subgroups (quotients that are integral domains)
3. Define normal closed subgroups (invariant under the adjoint action)
4. Show the set of connected normal unipotent subgroups is bounded in dimension
5. Construct the maximum as a Hopf subalgebra

The existence of a maximal such subgroup follows from dimension considerations:
unipotent groups over algebraically closed fields have bounded dimension
(they embed into strictly upper triangular matrices), so there exists a maximum.
-/

/-- The k-points of the unipotent radical of G.

This is the maximal connected normal unipotent subgroup of G(k).
The full construction would give a closed subgroup scheme, i.e., a Hopf subalgebra of A.

**Construction outline** (not implemented):
- Consider all connected normal unipotent closed subgroups H ⊆ G
- These correspond to Hopf ideals I ⊆ A such that A/I is an integral domain
  and the induced subgroup of G(k) consists of unipotent elements
- The dimensions of such H are bounded (unipotent groups embed in U_n)
- Take the unique maximal such H -/
def unipotentRadical : Subgroup (GroupLike k A) := sorry

/-- The unipotent radical consists of unipotent elements. -/
theorem unipotentRadical_isUnipotent (g : GroupLike k A)
    (hg : g ∈ (unipotentRadical : Subgroup (GroupLike k A))) :
    IsUnipotent g := sorry

/-- The unipotent radical is a normal subgroup.

This follows from the characterization as the maximal connected normal unipotent subgroup:
for any h ∈ G(k), the conjugate h · R_u(G) · h⁻¹ is also a connected normal unipotent
subgroup, hence contained in R_u(G), which gives normality. -/
theorem unipotentRadical_normal : (unipotentRadical : Subgroup (GroupLike k A)).Normal := sorry

/-- The unipotent radical is maximal among connected normal unipotent subgroups.

Note: The statement includes a `sorry` for connectedness because we haven't defined
what it means for a subgroup of G(k) to be "connected" (this would correspond to
the associated Hopf subalgebra being an integral domain). -/
theorem unipotentRadical_isMaximal (H : Subgroup (GroupLike k A))
    (hNormal : H.Normal)
    (hUnipotent : ∀ g ∈ H, IsUnipotent g)
    /- (hConnected : ...) -- TODO: need notion of connectedness for subgroups -/
    : H ≤ (unipotentRadical : Subgroup (GroupLike k A)) := sorry

/-- The unipotent radical is trivial iff it only contains the identity.

For a reductive group G, this condition holds after base change to the algebraic closure. -/
def unipotentRadical_isTrivial : Prop :=
  (unipotentRadical : Subgroup (GroupLike k A)) = ⊥

end UnipotentRadical
