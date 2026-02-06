# Reductive Algebraic Groups: Implementation Plan

This document outlines what is needed to complete mathematically correct definitions
of reductive algebraic groups in Mathlib.

## Scope and Standing Hypotheses

**We work with affine group schemes that are:**
- **Affine**: Represented by a commutative Hopf algebra A over a field k
- **Finite type**: A is finitely generated as a k-algebra
- **Smooth**: A is geometrically reduced (equivalently, A ⊗ k̄ is reduced)

These hypotheses are essential. Without them:
- Unipotent radical may not exist
- Faithful finite-dimensional representations may not exist
- Geometric notions are ill-defined

The `AffineAlgGroup` typeclass in `Defs.lean` captures these via `Algebra.FiniteType`
and `Algebra.IsGeometricallyReduced`.

## Current State

| File | Status | Issues |
|------|--------|--------|
| `Defs.lean` | Partial | `AlgPoints` group instance is `sorry`; base change `sorry` |
| `Unipotent.lean` | Placeholder | `IsUnipotent` is vacuous; `unipotentRadical` wrong type |
| `Reductive.lean` | Placeholder | Uses `True` because dependencies are broken |

## Missing Infrastructure

### 1. Functor of Points (Priority: HIGH)

**Goal**: Show `A →ₐ[k] R` forms a group under convolution for any commutative k-algebra R.

The current `AlgPoints k A := A →ₐ[k] k` only gives k-rational points. For group schemes,
we need the full functor of points: `R ↦ Hom_k(A, R)` valued in groups.

**What exists**:
- `Mathlib/RingTheory/Coalgebra/Convolution.lean` defines convolution on `C →ₗ[R] A`
- Ring/semiring instances exist for linear maps with convolution
- `HopfAlgebra.antipode` with key axioms

**What's needed**:
1. **Generalize to R-points**: Define `AlgPoints R A := A →ₐ[k] R` for any k-algebra R
2. Show convolution of two algebra homomorphisms is an algebra homomorphism
   - Uses bialgebra axiom: `Δ(ab) = Δ(a) · Δ(b)` (comultiplication is an algebra hom)
3. Prove `S(ab) = S(b) · S(a)` (antipode is an anti-homomorphism)
   - Stated as TODO in `HopfAlgebra/Basic.lean`
4. Show `f ∘ S` gives the inverse in the convolution group
5. **Show functoriality**: For k-algebra maps `R → R'`, the induced map on points is a group hom

**Difficulty**: Medium. Main work is proving the antipode anti-homomorphism property.

### 2. Hopf Ideals and Closed Subgroups (Priority: HIGH)

**Goal**: Define closed subgroup schemes as Hopf ideals.

This must come before unipotence, since the unipotent radical is a closed subgroup.

**What's needed**:
1. **Hopf ideal**: An ideal I ⊆ A such that:
   - `Δ(I) ⊆ I ⊗ A + A ⊗ I` (stable under comultiplication)
   - `ε(I) = 0` (contained in kernel of counit)
   - `S(I) ⊆ I` (stable under antipode)

2. **Quotient Hopf algebra**: Show A/I inherits Hopf structure

3. **Closed subgroups**: Anti-equivalence between Hopf ideals and closed subgroup schemes

4. **Normal subgroups**: Hopf ideals stable under the adjoint coaction
   - Requires defining the conjugation morphism `G × G → G` at the Hopf algebra level
   - The adjoint action is `ad_g(h) = ghg⁻¹`, which dualizes to a coaction on A

5. **Connected subgroups**: Hopf ideals I where A/I has no nontrivial idempotents

**Difficulty**: Medium-High. The adjoint action definition needs care.

### 3. Geometric Notions (Priority: HIGH)

Many properties must be defined "geometrically" (after base change to k̄).

**What's needed**:
1. **Geometric connectedness**: A ⊗ k̄ has no nontrivial idempotents
   - Stronger than connectedness over k
   - Current `IsConnected` should be renamed or generalized

2. **Geometric unipotence**: g ∈ G(k) is unipotent iff its image in G(k̄) is unipotent
   - Over non-algebraically closed fields, must base change first

3. **Geometric unipotent radical**: R_u(G) := R_u(G_k̄) descended to k
   - This is the correct definition for reductive groups over general fields

**Difficulty**: Medium. Requires base change infrastructure.

### 4. Base Change (Priority: MEDIUM)

**Goal**: Complete the `sorry` instances for `K ⊗[k] A`.

**What exists**:
- `Mathlib/RingTheory/HopfAlgebra/TensorProduct.lean` has tensor product of Hopf algebras
- `Algebra.FiniteType.baseChange` exists in `FiniteStability.lean`

**What's needed**:
1. Adapt tensor product instance for base change
   - Note: Do NOT define "trivial Hopf structure on K" - just use the induced structure
   - Base change is `K ⊗[k] A` with Hopf structure coming from A
2. Smoothness implies geometric reducedness is preserved

**Difficulty**: Low-Medium. Infrastructure mostly exists.

### 5. Comodule Theory (Priority: MEDIUM)

**Goal**: Define representations of affine group schemes via comodules.

**First**: Check what already exists in Mathlib under `Coalgebra/Comodule` or similar.

**What's needed** (if not already present):
1. **Comodules**: A k-vector space V with a coaction `ρ : V → V ⊗ A` satisfying:
   - `(id ⊗ Δ) ∘ ρ = (ρ ⊗ id) ∘ ρ` (coassociativity)
   - `(id ⊗ ε) ∘ ρ = id` (counit)

2. **Comodule morphisms**: Linear maps commuting with coaction

3. **Finite-dimensional comodules**: Category of f.d. comodules over A

4. **Faithful representations**: A representation V is faithful iff the morphism
   `G → GL(V)` is a closed immersion. Equivalently: **matrix coefficients generate A**.
   - WARNING: "Coaction is injective" is NOT equivalent to faithfulness!

5. **Induced endomorphism**: For `g : A →ₐ[k] k` and comodule V, define
   `ρ_g : V → V` by `v ↦ (id ⊗ g)(ρ(v))`

**Difficulty**: Medium-High. Faithfulness criterion needs care.

### 6. Unipotent Elements (Priority: MEDIUM)

**Goal**: Correct definition of unipotent elements.

**Correct definition**: g ∈ G(k̄) is unipotent iff for **every** finite-dimensional
representation V, the endomorphism `(ρ_g - id)` is nilpotent.

**Key points**:
- Definition is over k̄ (geometrically unipotent)
- Quantifies over ALL f.d. representations, not just faithful ones
- The reduction to a single faithful representation is a **theorem** (not definition)
  that requires proving existence of faithful f.d. representations

**What's needed**:
1. Theorem: For smooth affine group schemes of finite type, there exists a
   faithful finite-dimensional representation
2. Theorem: g is unipotent iff (ρ_g - id) is nilpotent for ONE faithful representation

**Difficulty**: High. The existence theorem is non-trivial.

### 7. The Unipotent Radical (Priority: HIGH but HARD)

**Goal**: Define `R_u(G)` as a Hopf ideal.

**Requires**: Items 2, 3, 5, 6 above.

**What's needed**:
1. Define "unipotent closed subgroup" using comodule theory
2. Show connected normal unipotent subgroups form a bounded family
   - Requires dimension theory or embedding into GL_n
3. Construct the maximum (Noetherian + dimension argument)
4. Prove it's characterized as the intersection of kernels of reductive quotients

**Key theorem**: For smooth connected affine group schemes of finite type over a field,
the unipotent radical exists and is the unique maximal connected normal unipotent
closed subgroup.

**Difficulty**: Very High. This is deep mathematics (SGA3, Borel).

## Recommended Roadmap

### Phase 1: Functor of Points
1. Generalize `AlgPoints` to R-points for any k-algebra R
2. Prove `S(ab) = S(b)S(a)` in `HopfAlgebra/Basic.lean`
3. Show algebra homs closed under convolution
4. Complete `Group (AlgPoints R A)` instance
5. Prove functoriality in R

**Unlocks**: Correct group scheme structure

### Phase 2: Hopf Ideals and Closed Subgroups
1. Define `HopfIdeal` structure
2. Prove quotient inherits Hopf structure
3. Define adjoint coaction for normality
4. Define `ClosedSubgroup` correspondence

**Unlocks**: Correct type for `unipotentRadical`

### Phase 3: Geometric Infrastructure
1. Base change for Hopf algebras (use existing tensor product)
2. Define geometric connectedness, geometric unipotence
3. Ensure smoothness/finite type hypotheses are explicit

**Unlocks**: Definitions over non-algebraically closed fields

### Phase 4: Comodule Theory
1. Check existing Mathlib infrastructure first!
2. Define comodules and morphisms
3. Define faithful = matrix coefficients generate A
4. Prove existence of faithful f.d. representation (hard)

**Unlocks**: Correct definition of `IsUnipotent`

### Phase 5: Unipotent Radical
1. Define unipotent closed subgroups
2. Prove existence of maximum (very hard)
3. Define `unipotentRadical` as a Hopf ideal

**Unlocks**: Correct `ReductiveGroup` definition

## Alternative Approaches

### Complete Reducibility (Simpler)
Instead of defining reductive via unipotent radical, define:
- G is **linearly reductive** if every f.d. representation is completely reducible

Pro: Avoids unipotent radical machinery entirely
Con: Not equivalent to "reductive" in positive characteristic

Over characteristic 0, this is equivalent to reductive. This could be a
pragmatic first definition while the full theory is developed.

### Scheme-theoretic
Work with:
- Affine schemes `Spec(A)`
- Group scheme structure via Yoneda
- Closed subschemes as ideals

Pro: More geometric, matches standard references (SGA3)
Con: Requires more scheme theory infrastructure

### Classical Groups First
Define GL_n, SL_n, tori as specific Hopf algebras and prove they are reductive
by explicit computation.

Pro: Concrete, gives examples
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
- SGA3, Exposé XIX: Reductive group schemes
