/-
Copyright (c) 2025 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.AlgebraicGroup.Unipotent

open TensorProduct

/-!
# Reductive Groups

A reductive group over a field k is an affine algebraic group G such that
the unipotent radical of G_{k̄} (base change to the algebraic closure) is trivial.

## Main definitions

* `ReductiveGroup`: Typeclass for reductive groups over a field
* `SemisimpleGroup`: Typeclass for semisimple groups (reductive with trivial radical)

## Implementation notes

Following Borel's definition, we define a reductive group over a general field k
by requiring that the unipotent radical becomes trivial after base change to the
algebraic closure. This is the correct definition even for imperfect fields.

Alternative characterizations (over algebraically closed fields):
1. G is reductive iff G has no nontrivial connected unipotent normal subgroup
2. G is reductive iff every finite-dimensional representation is completely reducible
3. G is reductive iff the Lie algebra Lie(G) is reductive

A semisimple group is a reductive group whose radical (maximal connected solvable
normal subgroup) is also trivial. Equivalently, a connected semisimple group has
no nontrivial connected abelian normal subgroup.

## Examples (TODO)

The following are reductive groups:
* GL_n: The general linear group
* SL_n: The special linear group
* PGL_n: The projective general linear group
* Tori: Products of copies of G_m
* SO_n, Sp_{2n}: Classical groups
* Exceptional groups: G_2, F_4, E_6, E_7, E_8

## References

* Brian Conrad, "Reductive Group Schemes", Definition 3.1.1
* Armand Borel, "Linear Algebraic Groups", Definition 11.21
-/

variable (k A : Type*) [Field k] [CommRing A] [HopfAlgebra k A]

/-- A reductive group over a field k is an affine algebraic group G such that
the unipotent radical of G base-changed to the algebraic closure is trivial.

This is Borel's definition: G is reductive iff R_u(G_{k̄}) = 1.

**Why base change to k̄?** Over a non-algebraically closed field, the k-points G(k)
may not detect all the structure of G. For example, over ℝ, the group SO(2) has
G(ℝ) = S¹ (a circle), but to see that it's a torus (hence reductive), we need to
pass to G(ℂ) ≅ ℂˣ.

**Equivalent characterizations** (over algebraically closed fields):
- G has no nontrivial connected unipotent normal closed subgroup
- Every finite-dimensional representation of G is completely reducible
- G⁰ (identity component) equals Z(G)⁰ · [G⁰, G⁰] where [G⁰, G⁰] is semisimple -/
class ReductiveGroup : Prop extends AffineAlgGroup k A where
  /-- The unipotent radical over the algebraic closure is trivial.

  **Note**: The precise statement is that `unipotentRadical` for the Hopf algebra
  `AlgebraicClosure k ⊗[k] A` (the base change to the algebraic closure) is trivial.
  This requires the sorry'd base change instances in `AffineAlgGroup.baseChangeHopfAlgebra`
  and `AffineAlgGroup.baseChangeAffineAlgGroup` to be properly implemented.

  For now, we use `True` as a placeholder. The actual condition should be:
  `@unipotentRadical_isTrivial (AlgebraicClosure k) _ _ (AlgebraicClosure k ⊗[k] A) _ _ _` -/
  unipotent_radical_trivial : True  -- TODO: replace once base change instances are implemented

/-- A semisimple group is a reductive group with trivial radical.

The radical R(G) is the maximal connected solvable normal subgroup. For a reductive
group, R(G) = Z(G)⁰ (the identity component of the center), which is a torus.
A reductive group is semisimple iff this central torus is trivial.

**Equivalent characterizations**:
- G is semisimple iff G is reductive and Z(G)⁰ = 1
- G is semisimple iff G is reductive and has no nontrivial connected abelian normal subgroup
- G is semisimple iff Lie(G) is a semisimple Lie algebra

**Note**: We use `True` as a placeholder for the radical triviality condition
until the (solvable) radical is defined. -/
class SemisimpleGroup : Prop extends ReductiveGroup k A where
  /-- The radical (maximal connected solvable normal subgroup) is trivial -/
  radical_trivial : True  -- TODO: replace with actual condition once radical is defined

namespace ReductiveGroup

/-- In a reductive group, the unipotent radical over the algebraic closure is trivial.

**Note**: This currently returns `True` as a placeholder. See the documentation on
`ReductiveGroup.unipotent_radical_trivial` for details. -/
theorem unipotentRadical_trivial' [h : ReductiveGroup k A] : True :=
  h.unipotent_radical_trivial

end ReductiveGroup

namespace SemisimpleGroup

/-- Every semisimple group is reductive. -/
instance instReductiveGroup [SemisimpleGroup k A] : ReductiveGroup k A :=
  SemisimpleGroup.toReductiveGroup

end SemisimpleGroup

/-!
## Examples

The following should be instances of `ReductiveGroup`. They are commented out
because defining the coordinate rings as Hopf algebras requires additional work.

### GL_n - The General Linear Group

The coordinate ring of GL_n is k[x_{ij}, det⁻¹] where i,j ∈ {1,...,n}.
As a Hopf algebra:
- Comultiplication: Δ(x_{ij}) = Σ_k x_{ik} ⊗ x_{kj}
- Counit: ε(x_{ij}) = δ_{ij}
- Antipode: S(x_{ij}) = (det⁻¹ · adj(X))_{ij}

GL_n is reductive because its unipotent radical is trivial: any connected normal
unipotent subgroup of GL_n would be contained in the scalar matrices, but scalar
matrices are semisimple (not unipotent) unless they equal 1.

### Tori

A split torus T = G_m^n has coordinate ring k[t_1, t_1⁻¹, ..., t_n, t_n⁻¹].
Tori are reductive because they have no unipotent elements at all
(every element is semisimple).

### SL_n - The Special Linear Group

SL_n is the kernel of det : GL_n → G_m. Its coordinate ring is k[x_{ij}]/(det - 1).
SL_n is semisimple for n ≥ 2: it's reductive and its center μ_n is finite.
-/

section Examples

-- TODO: Define coordinate rings as Hopf algebras and prove these instances
-- GL_n is reductive.
-- instance : ReductiveGroup k (HopfAlgebra.GL n k) := sorry
-- A split torus G_m^n is reductive.
-- instance : ReductiveGroup k (HopfAlgebra.Torus n k) := sorry
-- SL_n is semisimple for n ≥ 2.
-- instance (n : ℕ) [NeZero n] : SemisimpleGroup k (HopfAlgebra.SL n k) := sorry

end Examples
