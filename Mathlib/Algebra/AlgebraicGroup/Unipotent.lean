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

## Known limitations

**WARNING**: The definitions in this file are preliminary placeholders that are not
mathematically complete. They sketch the API structure but have known issues.

### Issue 1: `IsUnipotent` is vacuous for affine algebraic groups

The definition `IsUnipotent g := IsNilpotent ((g : A) - 1)` checks if `(g - 1)` is nilpotent
in the coordinate ring A. However:

1. `AffineAlgGroup` requires A to be geometrically reduced
2. Geometrically reduced implies reduced (no nonzero nilpotent elements)
3. Therefore `(g - 1)` nilpotent forces `g - 1 = 0`, i.e., `g = 1`
4. **Conclusion**: Only the identity element satisfies `IsUnipotent`!

This makes the definition vacuous and every group "reductive" by this criterion.

### Issue 2: Uses `GroupLike` instead of `AlgPoints`

The definitions use `GroupLike k A` (group-like elements of the Hopf algebra), but:
- `GroupLike k A` always forms a COMMUTATIVE group for commutative A
- The correct k-points are `AlgPoints k A := A →ₐ[k] k` with convolution

### Issue 3: `unipotentRadical` should be a subgroup SCHEME

The unipotent radical is defined as a `Subgroup` of `GroupLike k A`, but it should be a
closed subgroup scheme, corresponding to a Hopf ideal of A. This requires Hopf ideal
theory which does not yet exist in Mathlib.

### What would be needed for correct definitions

1. **Comodule theory**: Define comodules over Hopf algebras (representations of G)
2. **Faithful comodules**: Define what it means for a comodule to be faithful
3. **Representation-theoretic `IsUnipotent`**: g is unipotent iff for every faithful
   finite-dimensional comodule V, the induced endomorphism ρ(g) - 1 is nilpotent
4. **Hopf ideals**: Define Hopf ideals as ideals stable under comultiplication and antipode
5. **Closed subgroups**: Define closed subgroup schemes via Hopf ideals

## References

* Brian Conrad, "Reductive Group Schemes", Section 1.1 (Definition 1.1.5)
* Armand Borel, "Linear Algebraic Groups", Section 4.4
-/

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {A : Type*} [CommRing A] [HopfAlgebra k A] [AffineAlgGroup k A]

/-- An element g ∈ G(k) is "unipotent" if (g - 1) is nilpotent in A.

**WARNING**: This definition is VACUOUS for affine algebraic groups!
Since A is geometrically reduced (hence reduced), the only nilpotent element is 0.
Therefore `IsNilpotent ((g : A) - 1)` forces `g = 1`.

The correct definition requires representation/comodule theory:
g is unipotent iff for every faithful finite-dimensional representation ρ : G → GL_n,
the endomorphism ρ(g) - 1 is nilpotent. -/
def IsUnipotent (g : GroupLike k A) : Prop :=
  IsNilpotent ((g : A) - 1)

/-- Unipotent elements are closed under multiplication. -/
theorem IsUnipotent.mul {g h : GroupLike k A} (hg : IsUnipotent g) (hh : IsUnipotent h) :
    IsUnipotent (g * h) := sorry

omit [IsAlgClosed k] [AffineAlgGroup k A] in
/-- The identity is unipotent (trivially: 1 - 1 = 0 is nilpotent). -/
theorem isUnipotent_one : IsUnipotent (1 : GroupLike k A) := by
  unfold IsUnipotent
  simp only [GroupLike.val_one, sub_self]
  exact ⟨1, pow_one 0⟩

/-- If g is unipotent, so is g⁻¹. -/
theorem IsUnipotent.inv {g : GroupLike k A} (hg : IsUnipotent g) :
    IsUnipotent g⁻¹ := sorry

/-- If g is unipotent, so is any conjugate hgh⁻¹. -/
theorem IsUnipotent.conj {g h : GroupLike k A} (hg : IsUnipotent g) :
    IsUnipotent (h * g * h⁻¹) := sorry

section UnipotentRadical

/-!
### The Unipotent Radical

**WARNING**: The unipotent radical should be a closed subgroup SCHEME (a Hopf ideal),
not a `Subgroup` of the k-points. The current definition is a placeholder.

The correct approach would:
1. Define Hopf ideals (ideals I ⊆ A stable under comultiplication and antipode)
2. Define closed subgroups as quotients A/I with induced Hopf structure
3. Define "connected" as A/I being an integral domain
4. Define "normal" as I being stable under the adjoint action
5. Define "unipotent" using correct representation theory
6. Show the set of connected normal unipotent closed subgroups has a maximum
-/

/-- The k-points of the unipotent radical of G.

**WARNING**: This should be a Hopf ideal (closed subgroup scheme), not a `Subgroup`
of `GroupLike k A`. The current definition is a placeholder. -/
def unipotentRadical : Subgroup (GroupLike k A) := sorry

/-- The unipotent radical consists of unipotent elements. -/
theorem unipotentRadical_isUnipotent (g : GroupLike k A)
    (hg : g ∈ (unipotentRadical : Subgroup (GroupLike k A))) :
    IsUnipotent g := sorry

/-- The unipotent radical is a normal subgroup. -/
theorem unipotentRadical_normal : (unipotentRadical : Subgroup (GroupLike k A)).Normal := sorry

/-- The unipotent radical is maximal among connected normal unipotent subgroups. -/
theorem unipotentRadical_isMaximal (H : Subgroup (GroupLike k A))
    (hNormal : H.Normal)
    (hUnipotent : ∀ g ∈ H, IsUnipotent g)
    : H ≤ (unipotentRadical : Subgroup (GroupLike k A)) := sorry

/-- The unipotent radical is trivial iff it only contains the identity. -/
def unipotentRadical_isTrivial : Prop :=
  (unipotentRadical : Subgroup (GroupLike k A)) = ⊥

end UnipotentRadical
