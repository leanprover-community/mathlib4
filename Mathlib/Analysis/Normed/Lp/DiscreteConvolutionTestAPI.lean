/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.ENNReal.Basic

/-!
# Discrete Convolution of Functions

This file defines the discrete convolution of two functions `f : M → E` and `g : M → E'`
where `M` is a monoid, using a bilinear map `L : E →ₗ[S] E' →ₗ[S] F`:

  `(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`

where `mulFiber x = {(a, b) | a * b = x}` is the fiber of the multiplication map.

This is analogous to `MeasureTheory.convolution` but for the discrete (counting measure) setting.

## Design Notes

### Bilinear Map Approach

We use a bilinear map `L` to combine values, following the design of `MeasureTheory.convolution`.
This has several advantages:
* Supports the case where functions are vector-valued with different codomains
* Unifies scalar multiplication, ring multiplication, and other bilinear operations

The curried bilinear map type `E →ₗ[S] E' →ₗ[S] F` requires `[CommSemiring S]` so that
`E' →ₗ[S] F` is an `S`-module. This is the standard Mathlib requirement for curried
linear maps (see `LinearMap.mk₂'`).

For ring multiplication, use `mulConvolution` which is `convolution (LinearMap.mul R R)`.

### Why `@[to_additive]` Only Applies to Fibers

The `@[to_additive]` attribute converts names in its dictionary. However, convolution
involves `Module S E` which has implicit monoid structures that `to_additive` incorrectly
tries to convert (e.g., `CommMonoid S` from scalar action compatibility).

**Solution:** We manually define both `convolution` (for `[Monoid M]`) and
`addConvolution` (for `[AddMonoid M]`). The fiber definitions use `@[to_additive]`:
* `mulFiber` → `addFiber`
* `mulMap` → `addMap`
* `delta` → `addDelta`
* `tripleFiber` → `tripleAddFiber`
* `leftAssocEquiv` → `leftAddAssocEquiv`
* `rightAssocEquiv` → `rightAddAssocEquiv`

### When to Use Each Index Type

* **Multiplicative `[Monoid M]`**: Group algebras R[G], monoid algebras
* **Additive `[AddMonoid M]`**: Power series, polynomials

For `HasAntidiagonal` types (ℕ, ℕ × ℕ), the additive fiber is finite and the tsum
reduces to a finite sum, matching `CauchyProduct`.

### Why `mulMap` is Uncurried

We define `mulMap : M × M → M` (uncurried) rather than `M → M → M` (curried) because:

1. **Fiber as preimage**: `mulFiber x = mulMap ⁻¹' {x}` uses the preimage notation
   `f ⁻¹' S` which requires `f : α → β`.

2. **`Equiv.sigmaFiberEquiv`**: The equivalence `(Σ x, mulFiber x) ≃ M × M` used for
   sum reindexing in associativity proofs requires `mulMap : M × M → M`.

3. **Subtype iteration**: Elements of `mulFiber x` are pairs `⟨(a, b), hab⟩` where
   `hab : a * b = x`, fitting naturally with the uncurried domain `M × M`.

### Generalizability: Index vs Coefficient Commutativity

This API separates two algebraic structures with different commutativity requirements:

1. **Index monoid `M`**: Can be **non-commutative/non-abelian**. This is the key
   generality for group algebras R[G] where G may be non-abelian.

2. **Coefficient ring `R`**: Requires `[CommSemiring R]` when using `LinearMap.mul R R`,
   because bilinearity needs `r • (a * b) = (r * a) * b = a * (r * b)`.

For the ℓ¹ Banach algebra structure, `NormedCommRing R` is required. This covers all
standard cases (ℤ, ℚ, ℝ, ℂ, finite fields, p-adics). Non-commutative coefficient
rings (quaternions, matrix algebras) would need a separate direct definition
bypassing `LinearMap.mul`.

## Main Definitions

### Fibers
* `DiscreteConvolution.mulFiber x`: the set `{(a, b) | a * b = x}`
* `DiscreteConvolution.tripleFiber x`: the set `{(a, b, c) | a * b * c = x}`

### Convolution
* `DiscreteConvolution.convolution L f g`: convolution `f ⋆[L] g` for `[Monoid M]`
* `DiscreteConvolution.addConvolution L f g`: additive convolution `f ⋆₊[L] g` for `[AddMonoid M]`
* `DiscreteConvolution.mulConvolution f g`: ring multiplication convolution `f ⋆ₘ g`
* `DiscreteConvolution.delta e`: identity element `δ₁(e)` for convolution

### CauchyProduct (finite sums for HasAntidiagonal)
* `DiscreteConvolution.CauchyProduct.apply`: `(a ⋆ b) n = ∑ kl ∈ antidiagonal n, a kl.1 * b kl.2`
* `DiscreteConvolution.CauchyProduct.one`: identity `δ₀`
* `DiscreteConvolution.CauchyProduct.assoc`: associativity without `CompleteSpace`

### Summability Predicates
* `DiscreteConvolution.ConvolutionExistsAt L f g x`: convolution sum converges at `x`
* `DiscreteConvolution.ConvolutionExists L f g`: convolution exists everywhere

## Main Results

### Ring Axioms (General Bilinear)
* `DiscreteConvolution.convolution_add`: left distributivity
* `DiscreteConvolution.add_convolution`: right distributivity
* `DiscreteConvolution.zero_convolution`: left zero
* `DiscreteConvolution.convolution_zero`: right zero

### Ring Axioms (mulConvolution)
* `DiscreteConvolution.mulConvolution_add`, `add_mulConvolution`: distributivity
* `DiscreteConvolution.zero_mulConvolution`, `mulConvolution_zero`: zero laws
* `DiscreteConvolution.delta_mulConvolution`, `mulConvolution_delta`: identity laws
* `DiscreteConvolution.mulConvolution_comm`: commutativity (when M commutative)

### CauchyProduct Ring Axioms
* `CauchyProduct.assoc`: associativity via `sum_nbij'`
* `CauchyProduct.one_mul`, `CauchyProduct.mul_one`: identity laws
* `CauchyProduct.comm`: commutativity (when G commutative)
* `CauchyProduct.left_distrib`, `CauchyProduct.right_distrib`: distributivity

### Identity Laws
* `DiscreteConvolution.delta_convolution`: left identity
* `DiscreteConvolution.convolution_delta`: right identity

### Fiber Equivalences (with additive versions via `@[to_additive]`)
* `DiscreteConvolution.leftAssocEquiv`: `(Σ cd : mulFiber x, mulFiber cd.1.1) ≃ tripleFiber x`
* `DiscreteConvolution.rightAssocEquiv`: `(Σ ae : mulFiber x, mulFiber ae.1.2) ≃ tripleFiber x`

### HasAntidiagonal (bridge to finite sums)
* `DiscreteConvolution.addFiber_eq_antidiagonal`: fiber equals antidiagonal
* `DiscreteConvolution.addFiber_finite`: fiber is finite
* `DiscreteConvolution.addConvolution_eq_sum_antidiagonal`: `tsum` reduces to `Finset.sum`

## Related Files

* `LpOneBanachAlgebra.lean`: ℓ¹ Banach algebra instances using this convolution

## Notation

* `f ⋆[L] g` for discrete convolution with bilinear map `L`
* `f ⋆₊[L] g` for additive convolution
* `f ⋆ₘ g` for ring multiplication convolution
* `a ⋆ b` for CauchyProduct (finite sum)

## TODO

* Associativity for general bilinear maps (requires composition of bilinear maps);
  currently only proved for ℓ¹ ring multiplication in `LpOneBanachAlgebra.lean`
-/

@[expose] public section

open scoped BigOperators NNReal ENNReal

open Finset

noncomputable section

namespace DiscreteConvolution

variable {M : Type*} {S : Type*} {E E' F : Type*}

/-! ### Multiplication Fiber -/

section Fiber

variable [Monoid M]

/-- The multiplication map `(a, b) ↦ a * b`. -/
@[to_additive /-- The addition map `(a, b) ↦ a + b`. -/]
def mulMap : M × M → M := Function.uncurry (· * ·)

@[to_additive (attr := simp)]
theorem mulMap_apply (ab : M × M) : mulMap ab = ab.1 * ab.2 := rfl

/-- The fiber of multiplication at `x`: all pairs `(a, b)` with `a * b = x`. -/
@[to_additive /-- The fiber of addition at `x`: all pairs `(a, b)` with `a + b = x`. -/]
def mulFiber (x : M) : Set (M × M) := mulMap ⁻¹' {x}

@[to_additive (attr := simp)]
theorem mem_mulFiber {x : M} {ab : M × M} : ab ∈ mulFiber x ↔ ab.1 * ab.2 = x := Set.mem_preimage

@[to_additive]
theorem mulFiber_one_mem : (1, 1) ∈ mulFiber (1 : M) := mul_one 1

end Fiber

/-! ### Convolution Existence -/

section Existence

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

/-- The convolution of `f` and `g` with bilinear map `L` exists at `x` when the sum over
the fiber is summable. -/
def ConvolutionExistsAt (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) : Prop :=
  Summable fun ab : mulFiber x => L (f ab.1.1) (g ab.1.2)

/-- The convolution of `f` and `g` with bilinear map `L` exists when it exists at every point. -/
def ConvolutionExists (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : Prop :=
  ∀ x, ConvolutionExistsAt L f g x

end Existence

/-! ### Convolution Definition -/

section Definition

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

/-- The discrete convolution of `f` and `g` using bilinear map `L`:
`(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`. -/
def convolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : M → F :=
  fun x => ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)

/-- Notation for discrete convolution with explicit bilinear map. -/
scoped notation:70 f:70 " ⋆[" L:70 "] " g:71 => convolution L f g

@[simp]
theorem convolution_apply (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2) := rfl

end Definition

/-! ### Additive Convolution

For `[AddMonoid M]`, we define additive convolution using `addFiber` instead of `mulFiber`.
This is needed for `HasAntidiagonal` types like ℕ. -/

section AddConvolution

variable {M : Type*} [AddMonoid M] {S : Type*} [CommSemiring S]
variable {E E' F : Type*} [AddCommMonoid E] [Module S E]
variable [AddCommMonoid E'] [Module S E'] [AddCommMonoid F] [Module S F]
variable [TopologicalSpace F]

/-- Additive convolution using `addFiber`: `(f ⋆₊[L] g) x = ∑' (a, b) : addFiber x, L (f a) (g b)`.
This is the additive analogue of `convolution` for use with `HasAntidiagonal`. -/
def addConvolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : M → F :=
  fun x => ∑' ab : addFiber x, L (f ab.1.1) (g ab.1.2)

/-- Notation for additive convolution. -/
scoped notation:70 f:70 " ⋆₊[" L "] " g:71 => addConvolution L f g

@[simp]
theorem addConvolution_apply (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1.1) (g ab.1.2) := rfl

end AddConvolution

/-! ### Ring Multiplication Specialization -/

section RingMul

variable [Monoid M] {R : Type*}

/-- Convolution using ring multiplication. This is `convolution (LinearMap.mul R R)`. -/
def mulConvolution [CommSemiring R] [TopologicalSpace R] (f g : M → R) : M → R :=
  convolution (LinearMap.mul R R) f g

/-- Notation for ring multiplication convolution. -/
scoped notation:70 f:70 " ⋆ₘ " g:71 => mulConvolution f g

theorem mulConvolution_apply [CommSemiring R] [TopologicalSpace R] (f g : M → R) (x : M) :
    (f ⋆ₘ g) x = ∑' ab : mulFiber x, f ab.1.1 * g ab.1.2 := rfl

end RingMul

/-! ### Identity Element -/

section Identity

variable [Monoid M] [DecidableEq M] [Semiring S] [AddCommMonoid E] [Module S E]

/-- The identity for convolution: `δ₁(x) = e` if `x = 1`, else `0`,
where `e` is the provided identity element. -/
@[to_additive addDelta /-- The identity for additive convolution: `δ₀(x) = e` if `x = 0`,
else `0`. -/]
def delta (e : E) : M → E := Pi.single 1 e

@[to_additive (attr := simp) addDelta_zero]
theorem delta_one (e : E) : delta e 1 = e := rfl

@[to_additive addDelta_ne]
theorem delta_ne (e : E) {x : M} (hx : x ≠ 1) : delta e x = 0 :=
  Pi.single_eq_of_ne (M := fun _ => E) hx e

end Identity

/-! ### Ring Axioms (Zero) -/

section RingAxiomsZero

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

/-- Left zero: `0 ⋆[L] f = 0`. -/
@[simp]
theorem zero_convolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E') :
    (0 : M → E) ⋆[L] f = 0 := by
  ext x; simp only [convolution_apply, Pi.zero_apply, map_zero, LinearMap.zero_apply, tsum_zero]

/-- Right zero: `f ⋆[L] 0 = 0`. -/
@[simp]
theorem convolution_zero (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) :
    f ⋆[L] (0 : M → E') = 0 := by
  ext x; simp only [convolution_apply, Pi.zero_apply, map_zero, tsum_zero]

end RingAxiomsZero

/-! ### Ring Axioms (Distributivity) -/

section RingAxiomsDistrib

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F] [T2Space F] [ContinuousAdd F]

/-- Left distributivity: `f ⋆[L] (g + h) = f ⋆[L] g + f ⋆[L] h`. -/
theorem convolution_add (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g h : M → E')
    (hfg : ConvolutionExists L f g) (hfh : ConvolutionExists L f h) :
    f ⋆[L] (g + h) = f ⋆[L] g + f ⋆[L] h := by
  ext x; simp only [convolution_apply, Pi.add_apply, map_add]
  exact (hfg x).tsum_add (hfh x)

/-- Right distributivity: `(f + g) ⋆[L] h = f ⋆[L] h + g ⋆[L] h`. -/
theorem add_convolution (L : E →ₗ[S] E' →ₗ[S] F) (f g : M → E) (h : M → E')
    (hfh : ConvolutionExists L f h) (hgh : ConvolutionExists L g h) :
    (f + g) ⋆[L] h = f ⋆[L] h + g ⋆[L] h := by
  ext x; simp only [convolution_apply, Pi.add_apply, L.map_add, LinearMap.add_apply]
  exact (hfh x).tsum_add (hgh x)

end RingAxiomsDistrib

/-! ### Identity Laws -/

section IdentityLawsLeft

variable [Monoid M] [DecidableEq M] [CommSemiring S]
variable [AddCommMonoid E] [AddCommMonoid E'] [Module S E] [Module S E']
variable [TopologicalSpace E']

/-- Left identity: `delta e ⋆[L] f = L e ∘ f` when `L e` acts as identity. -/
theorem delta_convolution (L : E →ₗ[S] E' →ₗ[S] E') (e : E) (f : M → E')
    (hL : ∀ x, L e x = x) : delta e ⋆[L] f = f := by
  ext x
  simp only [convolution_apply, delta]
  rw [tsum_eq_single ⟨(1, x), by simp [mulFiber, mulMap]⟩]
  · simp only [Pi.single_eq_same, hL]
  · intro ⟨⟨a, b⟩, hab⟩ hne
    simp only [mem_mulFiber] at hab
    have ha : a ≠ 1 := by
      intro h; apply hne; ext
      · simp only [h, one_mul] at hab ⊢
      · simpa [h] using hab
    simp only [Pi.single_eq_of_ne ha, map_zero, LinearMap.zero_apply]

end IdentityLawsLeft

section IdentityLawsRight

variable [Monoid M] [DecidableEq M] [CommSemiring S]
variable [AddCommMonoid E] [AddCommMonoid E'] [Module S E] [Module S E']
variable [TopologicalSpace E]

/-- Right identity: `f ⋆[L] delta e = (fun x => L (f x) e)` when `(L · e)` acts as identity. -/
theorem convolution_delta (L : E →ₗ[S] E' →ₗ[S] E) (e : E') (f : M → E)
    (hL : ∀ x, L x e = x) : f ⋆[L] delta e = f := by
  ext x
  simp only [convolution_apply, delta]
  rw [tsum_eq_single ⟨(x, 1), by simp [mulFiber, mulMap]⟩]
  · simp only [Pi.single_eq_same, hL]
  · intro ⟨⟨a, b⟩, hab⟩ hne
    simp only [mem_mulFiber] at hab
    have hb : b ≠ 1 := by
      intro h; apply hne; ext
      · simpa [h] using hab
      · simp only [h, mul_one] at hab ⊢
    simp only [Pi.single_eq_of_ne hb, map_zero]

end IdentityLawsRight

/-! ### Commutativity -/

section Commutative

variable [CommMonoid M] [CommSemiring S]
variable [AddCommMonoid E] [Module S E]
variable [TopologicalSpace E]

/-- Commutativity for symmetric bilinear maps on commutative monoids. -/
theorem convolution_comm (L : E →ₗ[S] E →ₗ[S] E) (f g : M → E)
    (hL : ∀ x y, L x y = L y x) :
    f ⋆[L] g = g ⋆[L] f := by
  ext x
  simp only [convolution_apply]
  let e : mulFiber x ≃ mulFiber x :=
    ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨⟨b, a⟩, by simp_all [mulFiber, mulMap, mul_comm]⟩,
     fun ⟨⟨a, b⟩, h⟩ => ⟨⟨b, a⟩, by simp_all [mulFiber, mulMap, mul_comm]⟩,
     fun _ => by rfl,
     fun _ => by rfl⟩
  rw [← e.tsum_eq]
  congr 1
  funext ⟨⟨a, b⟩, hab⟩
  simp only [e, Equiv.coe_fn_mk, hL]

end Commutative

/-! ### Ring Axioms for mulConvolution -/

section MulConvolutionRingAxioms

variable [Monoid M] {R : Type*} [CommSemiring R] [TopologicalSpace R]

@[simp]
theorem zero_mulConvolution (f : M → R) : (0 : M → R) ⋆ₘ f = 0 :=
  zero_convolution (LinearMap.mul R R) f

@[simp]
theorem mulConvolution_zero (f : M → R) : f ⋆ₘ (0 : M → R) = 0 :=
  convolution_zero (LinearMap.mul R R) f

variable [T2Space R] [ContinuousAdd R]

theorem mulConvolution_add (f g h : M → R)
    (hfg : ConvolutionExists (LinearMap.mul R R) f g)
    (hfh : ConvolutionExists (LinearMap.mul R R) f h) :
    f ⋆ₘ (g + h) = f ⋆ₘ g + f ⋆ₘ h :=
  convolution_add (LinearMap.mul R R) f g h hfg hfh

theorem add_mulConvolution (f g h : M → R)
    (hfh : ConvolutionExists (LinearMap.mul R R) f h)
    (hgh : ConvolutionExists (LinearMap.mul R R) g h) :
    (f + g) ⋆ₘ h = f ⋆ₘ h + g ⋆ₘ h :=
  add_convolution (LinearMap.mul R R) f g h hfh hgh

end MulConvolutionRingAxioms

section MulConvolutionIdentity

variable [Monoid M] [DecidableEq M] {R : Type*} [CommSemiring R] [TopologicalSpace R]

theorem delta_mulConvolution (e : R) (f : M → R) : delta e ⋆ₘ f = e • f := by
  ext x
  simp only [mulConvolution_apply, delta, Pi.smul_apply, smul_eq_mul]
  rw [tsum_eq_single ⟨(1, x), by simp [mulFiber, mulMap]⟩]
  · simp only [Pi.single_eq_same]
  · intro ⟨⟨a, b⟩, hab⟩ hne
    simp only [mem_mulFiber] at hab
    have ha : a ≠ 1 := by
      intro h; apply hne; ext
      · simp only [h, one_mul] at hab ⊢
      · simpa [h] using hab
    simp only [Pi.single_eq_of_ne ha, zero_mul]

theorem mulConvolution_delta (e : R) (f : M → R) : f ⋆ₘ delta e = e • f := by
  ext x
  simp only [mulConvolution_apply, delta, Pi.smul_apply, smul_eq_mul]
  rw [tsum_eq_single ⟨(x, 1), by simp [mulFiber, mulMap]⟩]
  · simp only [Pi.single_eq_same, mul_comm]
  · intro ⟨⟨a, b⟩, hab⟩ hne
    simp only [mem_mulFiber] at hab
    have hb : b ≠ 1 := by
      intro h; apply hne; ext
      · simpa [h] using hab
      · simp only [h, mul_one] at hab ⊢
    simp only [Pi.single_eq_of_ne hb, mul_zero]

end MulConvolutionIdentity

section MulConvolutionComm

variable [CommMonoid M] {R : Type*} [CommSemiring R] [TopologicalSpace R]

theorem mulConvolution_comm (f g : M → R) : f ⋆ₘ g = g ⋆ₘ f :=
  convolution_comm (LinearMap.mul R R) f g (fun x y => mul_comm x y)

end MulConvolutionComm

/-! ### Triple Fiber and Associativity Equivalences

These pure monoid constructions support associativity proofs. The fiber equivalences
identify nested sums with sums over the triple fiber `{(a, b, c) | a * b * c = x}`. -/

section TripleFiber

variable [Monoid M]

/-- The triple multiplication map `(a, b, c) ↦ a * b * c`. -/
@[to_additive /-- The triple addition map `(a, b, c) ↦ a + b + c`. -/]
def tripleMulMap : M × M × M → M := fun ⟨a, b, c⟩ => a * b * c

/-- Fiber over `x` under triple multiplication: `{(a, b, c) | a * b * c = x}`. -/
@[to_additive tripleAddFiber
  /-- Fiber over `x` under triple addition: `{(a, b, c) | a + b + c = x}`. -/]
def tripleFiber (x : M) : Set (M × M × M) := tripleMulMap ⁻¹' {x}

@[to_additive (attr := simp) mem_tripleAddFiber]
theorem mem_tripleFiber {x : M} {abc : M × M × M} :
    abc ∈ tripleFiber x ↔ abc.1 * abc.2.1 * abc.2.2 = x := Set.mem_preimage

/-! #### Fiber Equivalences

These equivalences identify nested sigma types with the triple fiber. This enables
the Fubini-style reindexing needed to prove associativity:

`∑' cd : mulFiber x, ∑' ab : mulFiber cd.1.1, ... = ∑' p : tripleFiber x, ...`

The proofs use only `mul_assoc`, so they work for non-commutative monoids. -/

/-- Left association equivalence for associativity proof.
Maps `((c, d), (a, b))` where `c * d = x` and `a * b = c` to `(a, b, d)` where `a * b * d = x`.
This identifies the nested sum `∑' (cd : mulFiber x), ∑' (ab : mulFiber cd.1.1), f a * g b * h d`
with a sum over the triple fiber. -/
@[to_additive leftAddAssocEquiv /-- Left association equivalence for additive associativity. -/]
def leftAssocEquiv (x : M) : (Σ cd : mulFiber x, mulFiber cd.1.1) ≃ tripleFiber x where
  toFun := fun ⟨⟨⟨c, d⟩, hcd⟩, ⟨⟨a, b⟩, hab⟩⟩ =>
    ⟨⟨a, b, d⟩, by
      simp only [tripleFiber, tripleMulMap, Set.mem_preimage, Set.mem_singleton_iff]
      simp only [mulFiber, mulMap, Set.mem_preimage, Set.mem_singleton_iff,
        Function.uncurry_apply_pair] at hcd hab
      rw [← hcd, ← hab, mul_assoc]⟩
  invFun := fun ⟨⟨a, b, d⟩, habd⟩ =>
    ⟨⟨⟨a * b, d⟩, by
        simp only [mulFiber, mulMap, Set.mem_preimage, Set.mem_singleton_iff,
          Function.uncurry_apply_pair]
        simp only [tripleFiber, tripleMulMap, Set.mem_preimage, Set.mem_singleton_iff] at habd
        exact habd⟩,
     ⟨⟨a, b⟩, by
        simp only [mulFiber, mulMap, Set.mem_preimage, Set.mem_singleton_iff,
          Function.uncurry_apply_pair]⟩⟩
  left_inv := fun ⟨⟨⟨c, d⟩, hcd⟩, ⟨⟨a, b⟩, hab⟩⟩ => by
    simp only [mulFiber, mulMap, Set.mem_preimage, Set.mem_singleton_iff,
      Function.uncurry_apply_pair] at hab
    simp only [Sigma.mk.injEq, hab, true_and]
    subst hab
    simp_all only [heq_eq_eq]
  right_inv := fun ⟨⟨a, b, d⟩, habd⟩ => rfl

/-- Right association equivalence for associativity proof.
Maps `((a, e), (b, d))` where `a * e = x` and `b * d = e` to `(a, b, d)` where `a * b * d = x`.
This identifies the nested sum `∑' (ae : mulFiber x), ∑' (bd : mulFiber ae.1.2), f a * g b * h d`
with a sum over the triple fiber. -/
@[to_additive rightAddAssocEquiv /-- Right association equivalence for additive associativity. -/]
def rightAssocEquiv (x : M) : (Σ ae : mulFiber x, mulFiber ae.1.2) ≃ tripleFiber x where
  toFun := fun ⟨⟨⟨a, e⟩, hae⟩, ⟨⟨b, d⟩, hbd⟩⟩ =>
    ⟨⟨a, b, d⟩, by
      simp only [tripleFiber, tripleMulMap, Set.mem_preimage, Set.mem_singleton_iff]
      simp only [mulFiber, mulMap, Set.mem_preimage, Set.mem_singleton_iff,
        Function.uncurry_apply_pair] at hae hbd
      rw [← hae, ← hbd, mul_assoc]⟩
  invFun := fun ⟨⟨a, b, d⟩, habd⟩ =>
    ⟨⟨⟨a, b * d⟩, by
        simp only [mulFiber, mulMap, Set.mem_preimage, Set.mem_singleton_iff,
          Function.uncurry_apply_pair]
        simp only [tripleFiber, tripleMulMap, Set.mem_preimage, Set.mem_singleton_iff] at habd
        rw [← mul_assoc]; exact habd⟩,
     ⟨⟨b, d⟩, by
        simp only [mulFiber, mulMap, Set.mem_preimage, Set.mem_singleton_iff,
          Function.uncurry_apply_pair]⟩⟩
  left_inv := fun ⟨⟨⟨a, e⟩, hae⟩, ⟨⟨b, d⟩, hbd⟩⟩ => by
    simp only [mulFiber, mulMap, Set.mem_preimage, Set.mem_singleton_iff,
      Function.uncurry_apply_pair] at hbd
    simp only [Sigma.mk.injEq, hbd, true_and]
    subst hbd
    simp_all only [heq_eq_eq]
  right_inv := fun ⟨⟨a, b, d⟩, habd⟩ => rfl

end TripleFiber

/-! ### Connection to Finite Antidiagonals

For types with `HasAntidiagonal` (e.g., ℕ, ℕ × ℕ), the additive fiber `addFiber x` is finite
and equals `antidiagonal x`. Thus the `tsum` in `addConvolution` reduces to a `Finset.sum`,
matching the `CauchyProduct` formulation. -/

section Antidiagonal

open Finset

variable [AddMonoid M] [HasAntidiagonal M]

/-- For types with `HasAntidiagonal`, the additive fiber equals the antidiagonal. -/
theorem addFiber_eq_antidiagonal (x : M) :
    addFiber x = ↑(antidiagonal x) := by
  ext ⟨a, b⟩
  simp only [mem_coe, mem_antidiagonal, mem_addFiber]

/-- The additive fiber is finite when `HasAntidiagonal` is available. -/
theorem addFiber_finite (x : M) : (addFiber x).Finite := by
  rw [addFiber_eq_antidiagonal]
  exact (antidiagonal x).finite_toSet

variable {S : Type*} [CommSemiring S]
variable {E E' F : Type*} [AddCommMonoid E] [Module S E]
variable [AddCommMonoid E'] [Module S E'] [AddCommMonoid F] [Module S F]
variable [TopologicalSpace F]

/-- For `HasAntidiagonal` types, additive convolution equals a finite sum over the antidiagonal.
This bridges the `tsum`-based `addConvolution` with the `Finset.sum`-based `CauchyProduct`. -/
theorem addConvolution_eq_sum_antidiagonal (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E')
    (x : M) : addConvolution L f g x = ∑ ab ∈ antidiagonal x, L (f ab.1) (g ab.2) := by
  simp only [addConvolution_apply]
  rw [← (antidiagonal x).tsum_subtype fun ab => L (f ab.1) (g ab.2)]
  exact (Equiv.setCongr (addFiber_eq_antidiagonal x)).tsum_eq
    (fun ab => (L (f ab.1.1)) (g ab.1.2))

end Antidiagonal

/-! ## CauchyProduct: Finite Antidiagonal Convolution

For types with `HasAntidiagonal` (e.g., ℕ, ℕ × ℕ, List α), convolution is a finite sum
over the antidiagonal. This gives a purely algebraic ring structure without requiring
`CompleteSpace` or `tsum` convergence.

This is equivalent to `addConvolution` when applied to `LinearMap.mul`, but the finite-sum
formulation allows proving associativity via `sum_nbij'` rather than `tsum_sigma'`. -/

namespace CauchyProduct

variable {G : Type*} {R : Type*}

/-! ### Product Definition -/

section Product

variable [AddMonoid G] [HasAntidiagonal G] [Semiring R]

/-- Cauchy product (convolution) via finite antidiagonal sum. -/
def apply (a b : G → R) : G → R :=
  fun n => ∑ kl ∈ antidiagonal n, a kl.1 * b kl.2

/-- Notation for Cauchy product convolution. -/
scoped notation:70 a:70 " ⋆ " b:71 => apply a b

theorem apply_eq (a b : G → R) (n : G) :
    (a ⋆ b) n = ∑ kl ∈ antidiagonal n, a kl.1 * b kl.2 := rfl

/-! ### Ring Axioms -/

theorem left_distrib (a b c : G → R) : a ⋆ (b + c) = a ⋆ b + a ⋆ c := by
  ext n; simp only [Pi.add_apply, apply_eq, mul_add, Finset.sum_add_distrib]

theorem right_distrib (a b c : G → R) : (a + b) ⋆ c = a ⋆ c + b ⋆ c := by
  ext n; simp only [apply_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp]
theorem zero_mul (a : G → R) : (0 : G → R) ⋆ a = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.zero_mul, Finset.sum_const_zero]

@[simp]
theorem mul_zero (a : G → R) : a ⋆ (0 : G → R) = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.mul_zero, Finset.sum_const_zero]

/-! ### Associativity via bijection on triple sums -/

/-- Associativity of Cauchy product, proved via bijection on sigma types. -/
theorem assoc (a b c : G → R) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  ext n
  simp only [apply_eq, sum_mul, mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x => ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
    (fun x => ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩)
    ?_ ?_ ?_ ?_ ?_
  all_goals intro x hx
  all_goals simp_all only [Finset.mem_sigma, Finset.mem_antidiagonal, Prod.mk.eta, Sigma.eta]
  · exact ⟨by rw [← hx.1, ← hx.2, add_assoc], trivial⟩
  · exact ⟨by rw [← hx.1, ← hx.2, add_assoc], trivial⟩
  · exact mul_assoc _ _ _

theorem smul_mul (c : R) (a b : G → R) : (c • a) ⋆ b = c • (a ⋆ b) := by
  ext n; simp only [apply_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

end Product

/-! ### Identity Element -/

section Identity

variable [AddMonoid G] [DecidableEq G] [Semiring R]

/-- The multiplicative identity: `δ₀(0) = 1`, `δ₀(g) = 0` for `g ≠ 0`. -/
def one : G → R := Pi.single 0 1

@[simp]
theorem one_apply_zero : (one : G → R) 0 = 1 := Pi.single_eq_same 0 1

theorem one_apply_ne {g : G} (hg : g ≠ 0) : (one : G → R) g = 0 := Pi.single_eq_of_ne hg 1

end Identity

/-! ### Identity Laws -/

section IdentityAntidiagonal

variable [AddMonoid G] [DecidableEq G] [HasAntidiagonal G] [Semiring R]

theorem one_mul (a : G → R) : one ⋆ a = a := by
  ext n; simp only [apply_eq, one]
  rw [sum_eq_single (0, n)]
  · simp only [Pi.single_eq_same, _root_.one_mul]
  · intro ⟨x, y⟩ hxy hne
    simp_all only [mem_antidiagonal, Pi.single_apply]
    subst hxy
    simp_all only [ne_eq, Prod.mk.injEq, not_and, zero_add,
      not_true_eq_false, imp_false, ↓reduceIte, MulZeroClass.zero_mul]
  · simp [mem_antidiagonal]

theorem mul_one (a : G → R) : a ⋆ one = a := by
  ext n; simp only [apply_eq, one]
  rw [Finset.sum_eq_single (n, 0)]
  · simp only [Pi.single_eq_same, _root_.mul_one]
  · intro ⟨x, y⟩ hxy hne
    simp only [Finset.mem_antidiagonal] at hxy
    simp only [ne_eq, Prod.mk.injEq, not_and] at hne
    have : y ≠ 0 := fun h => hne (by simp [← hxy, h]) h
    simp [this]
  · simp [Finset.mem_antidiagonal]

end IdentityAntidiagonal

/-! ### Commutativity -/

section Comm

variable [AddCommMonoid G] [HasAntidiagonal G] [CommSemiring R]

theorem comm (a b : G → R) : a ⋆ b = b ⋆ a := by
  ext n; simp only [apply_eq]
  rw [← Finset.map_swap_antidiagonal (n := n), Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.fst_swap,
    Prod.snd_swap, map_swap_antidiagonal, mul_comm]

theorem mul_smul (c : R) (a b : G → R) : a ⋆ (c • b) = c • (a ⋆ b) := by
  ext n; simp only [apply_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro kl _; ring

end Comm

end CauchyProduct

end DiscreteConvolution

end

end
