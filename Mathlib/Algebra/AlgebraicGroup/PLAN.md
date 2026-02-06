# Reductive Algebraic Groups: Implementation Plan

This document outlines what is needed to complete mathematically correct definitions
of reductive algebraic groups in Mathlib.

## Current State

The files in this directory provide **preliminary scaffolding** with known issues:

| File | Status | Issues |
|------|--------|--------|
| `Defs.lean` | Partial | `AlgPoints` group instance is `sorry`; base change `sorry` |
| `Unipotent.lean` | Placeholder | `IsUnipotent` is vacuous; `unipotentRadical` wrong type |
| `Reductive.lean` | Placeholder | Uses `True` because dependencies are broken |

## Missing Infrastructure

### 1. Convolution Group on Algebra Homomorphisms

**Goal**: Show `A →ₐ[k] k` forms a group under convolution for a Hopf algebra A.

**What exists**:
- `Mathlib/RingTheory/Coalgebra/Convolution.lean` defines convolution on `C →ₗ[R] A`
- Ring/semiring instances exist for linear maps with convolution
- `HopfAlgebra.antipode` with key axioms

**What's needed**:
1. Show convolution of two algebra homomorphisms is an algebra homomorphism
   - This requires: if `f, g : A →ₐ[k] k`, then `(f * g)(ab) = (f * g)(a) · (f * g)(b)`
   - Uses bialgebra axiom: `Δ(ab) = Δ(a) · Δ(b)` (comultiplication is an algebra hom)

2. Show the counit `ε : A → k` is an algebra homomorphism (already true by definition)

3. Show `f ∘ S` is an algebra homomorphism when f is
   - Requires: `S(ab) = S(b) · S(a)` (antipode is an anti-homomorphism)
   - This is stated as TODO in `HopfAlgebra/Basic.lean`

4. Prove the group axioms using the antipode axioms

**Difficulty**: Medium. The convolution infrastructure exists; main work is:
- Proving `S(ab) = S(b)S(a)` for the antipode
- Showing algebra homs are closed under convolution

### 2. Comodule Theory (for correct `IsUnipotent`)

**Goal**: Define representations of affine group schemes via comodules.

**What's needed**:
1. **Comodules**: A k-vector space V with a coaction `ρ : V → V ⊗ A` satisfying:
   - `(id ⊗ Δ) ∘ ρ = (ρ ⊗ id) ∘ ρ` (coassociativity)
   - `(id ⊗ ε) ∘ ρ = id` (counit)

2. **Comodule morphisms**: Linear maps commuting with coaction

3. **Finite-dimensional comodules**: Category of f.d. comodules over A

4. **Faithful comodules**: Coaction is injective (or equivalent condition)

5. **Induced endomorphism**: For `g : A →ₐ[k] k` and comodule V, define
   `ρ_g : V → V` by `v ↦ (id ⊗ g)(ρ(v))`

**Correct IsUnipotent**: g is unipotent iff for every faithful f.d. comodule V,
the endomorphism `(ρ_g - id)` is nilpotent.

**Difficulty**: High. This is substantial new theory. Could be simplified by:
- Working only with the regular comodule (A acting on itself)
- Using that for affine algebraic groups, there exists a faithful f.d. representation

### 3. Hopf Ideals and Closed Subgroups

**Goal**: Define closed subgroup schemes as Hopf ideals.

**What's needed**:
1. **Hopf ideal**: An ideal I ⊆ A such that:
   - `Δ(I) ⊆ I ⊗ A + A ⊗ I` (stable under comultiplication)
   - `ε(I) = 0` (contained in kernel of counit)
   - `S(I) ⊆ I` (stable under antipode)

2. **Quotient Hopf algebra**: Show A/I inherits Hopf structure

3. **Closed subgroups**: Correspondence between Hopf ideals and closed subgroup schemes

4. **Normal subgroups**: Hopf ideals stable under adjoint action

5. **Connected subgroups**: Hopf ideals I where A/I has no nontrivial idempotents

**Difficulty**: Medium-High. Requires careful handling of quotients and induced structures.

### 4. The Unipotent Radical

**Goal**: Define `R_u(G)` as a Hopf ideal.

**What's needed** (after items 2-3):
1. Define "unipotent closed subgroup" using comodule theory
2. Show connected normal unipotent subgroups form a bounded family
3. Construct the maximum (requires dimension theory or Noetherian argument)
4. Prove it's characterized as the intersection of kernels of reductive quotients

**Difficulty**: High. This is the mathematical core of the theory.

### 5. Base Change

**Goal**: Complete the `sorry` instances for `K ⊗[k] A`.

**What exists**:
- `Mathlib/RingTheory/HopfAlgebra/TensorProduct.lean` has tensor product of Hopf algebras
- `Algebra.FiniteType.baseChange` exists in `FiniteStability.lean`

**What's needed**:
1. Adapt tensor product instance for base change (K is a trivial Hopf algebra)
2. Show geometric reducedness is preserved under base change

**Difficulty**: Low-Medium. Infrastructure mostly exists.

## Recommended Roadmap

### Phase 1: Complete k-points (Priority: High)
1. Prove `S(ab) = S(b)S(a)` in `HopfAlgebra/Basic.lean`
2. Show algebra homs closed under convolution
3. Complete `Group (AlgPoints k A)` instance

**Unlocks**: Correct definition of G(k) as a (generally non-commutative) group

### Phase 2: Base Change (Priority: Medium)
1. Define trivial Hopf structure on a field
2. Instantiate tensor product for base change
3. Prove geometric reducedness preserved

**Unlocks**: Definition of G_k̄ needed for reductive groups

### Phase 3: Hopf Ideals (Priority: Medium)
1. Define `HopfIdeal` structure
2. Prove quotient inherits Hopf structure
3. Define `ClosedSubgroup` as anti-equivalence

**Unlocks**: Correct type for `unipotentRadical`

### Phase 4: Comodule Theory (Priority: High for correctness)
1. Define comodules and their category
2. Define faithful comodules
3. Define induced endomorphisms from k-points

**Unlocks**: Correct definition of `IsUnipotent`

### Phase 5: Unipotent Radical (Priority: High)
1. Define unipotent closed subgroups using comodules
2. Prove existence of maximum
3. Define `unipotentRadical` as a Hopf ideal

**Unlocks**: Correct `ReductiveGroup` definition

## Alternative Approaches

### Scheme-theoretic
Instead of Hopf algebras, work with:
- Affine schemes `Spec(A)`
- Group scheme structure via Yoneda
- Closed subschemes as ideals

Pro: More geometric, matches standard references
Con: Requires more scheme theory infrastructure

### Representation-theoretic (for GL_n)
For classical groups, define directly:
- GL_n, SL_n, tori as specific Hopf algebras
- Prove they are reductive by explicit computation

Pro: Concrete, avoids abstract machinery
Con: Doesn't give general theory

## References

- Brian Conrad, "Reductive Group Schemes" (SGA3 exposition)
  - Definition 1.1.5: Unipotent elements
  - Section 3.1: Reductive groups over fields
- Armand Borel, "Linear Algebraic Groups"
  - Section 4.4: Unipotent elements and groups
  - Section 11.21: Reductive groups
- Waterhouse, "Introduction to Affine Group Schemes"
  - Chapter 3: Comodules and representations
  - Chapter 11: The unipotent radical
