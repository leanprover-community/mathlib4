/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.Set.MulAntidiagonal
public import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Discrete Convolution

Discrete convolution over monoids: `(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`
where `mulFiber x = {(a, b) | a * b = x}`. Additive monoids are also supported.

## Design

Uses bilinear map `L : E →ₗ[S] E' →ₗ[S] F` to combine values, following `MeasureTheory.convolution`.
For specializing to ring multiplication, use `ringConvolution` = `convolution (LinearMap.mul R R)`.

Index monoid `M` can be non-commutative (group algebras R[G] with non-abelian G).
Coefficient ring requires `[CommSemiring R]` for bilinearity of `LinearMap.mul`.
Example: `FreeMonoid α ≃ List α` enables convolution on lists.

`@[to_additive]` generates multiplicative and additive versions from a single definition.
The `mul/add` distinction refers to the index monoid `M`: multiplicative sums over
`mulFiber x = {(a,b) | a * b = x}`, additive sums over `addFiber x = {(a,b) | a + b = x}`.

## Relation to `MeasureTheory.convolution`

Related to `MeasureTheory.convolution` with counting measure μ:
- Discrete:      (f ⋆₊[L] g) x   = ∑' (a,b) : addFiber x, L (f a) (g b)
- MeasureTheory: (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ

Formally,
```
theorem addRingConvolution_eq_measureTheory_convolution [Countable M]
    (f g : M → R) (hfg : ∀ x, Integrable (fun t => f t * g (x - t)) .count) :
    (f ⋆₊ₘ g) = MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ R) .count
```

Parallel API:
- `ConvolutionExistsAt`, `convolution_zero`,
  `zero_convolution`, `convolution_add`, `convolution_assoc`.
- Convolution associativity has the same bilinearity hypothesis:
  `hL : ∀ x y z, L₂ (L x y) z = L₃ x (L₄ y z)`.

Differences (discrete ↔ MeasureTheory):
- Domain: `Monoid M` ↔ `AddGroup G`, no subtraction needed for discrete
- Bilinear map: `E →ₗ[S] E' →ₗ[S] F` ↔ `E →L[𝕜] E' →L[𝕜] F`, no continuity needed
- Associativity: `Summable` ↔ `AEStronglyMeasurable` + norm convolution conditions
- `@[to_additive]`: Discrete supports both mul/add versions; MeasureTheory is additive only

## Main Results

- `convolution_zero`, `convolution_add`: zero and distributivity laws
- Associativity:
  - `convolution_assoc_at`: pointwise, uses `assocEquiv`, derives compatibility from bilinearity
  - `convolution_assoc`: applies above with triple summability
  - `ringConvolution_assoc_at`, `ringConvolution_assoc`: for ring multiplication `f ⋆ₘ g`

## Notation

| Notation     | Operation                                       |
|--------------|-------------------------------------------------|
| `f ⋆[L] g`   | `∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)`   |
| `f ⋆₊[L] g`  | `∑' ab : addFiber x, L (f ab.1.1) (g ab.1.2)`   |
| `f ⋆ₘ g`     | `∑' ab : mulFiber x, f ab.1.1 * g ab.1.2`       |
| `f ⋆₊ₘ g`    | `∑' ab : addFiber x, f ab.1.1 * g ab.1.2`       |
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace DiscreteConvolution

variable {M : Type*} {S : Type*} {E E' F : Type*}

/-! ### Multiplication Fiber -/

section Fiber

variable [Monoid M]

/-- The fiber of multiplication at `x`: all pairs `(a, b)` with `a * b = x`.
This is `Set.mulAntidiagonal Set.univ Set.univ x`. -/
@[to_additive /-- The fiber of addition at `x`: all pairs `(a, b)` with `a + b = x`.
This is `Set.addAntidiagonal Set.univ Set.univ x`. -/]
abbrev mulFiber (x : M) : Set (M × M) := Set.mulAntidiagonal Set.univ Set.univ x

@[to_additive]
theorem mem_mulFiber {x : M} {ab : M × M} : ab ∈ mulFiber x ↔ ab.1 * ab.2 = x := by
  simp only [Set.mem_mulAntidiagonal, Set.mem_univ, true_and]

@[to_additive]
theorem mulFiber_one_mem : (1, 1) ∈ mulFiber (1 : M) := by
  simp only [Set.mem_mulAntidiagonal, Set.mem_univ, mul_one, and_self]

end Fiber

/-! ### Triple Antidiagonal and Fiber -/

-- Implementation details for triple fibers. Users should work with `tripleFiber` directly.
section TripleFiber

variable [Monoid M] [Mul S]

set_option backward.privateInPublic true in
/-- `mulTripleAntidiagonal s t u a` is the set of all triples `(x, y, z)` with `x ∈ s`, `y ∈ t`,
`z ∈ u`, and `x * y * z = a`. Triple analog of `Set.mulAntidiagonal`. -/
@[to_additive
  /-- `addTripleAntidiagonal s t u a` is the set of all triples `(x, y, z)` with `x ∈ s`, `y ∈ t`,
  `z ∈ u`, and `x + y + z = a`. Triple analog of `Set.addAntidiagonal`. -/]
private def mulTripleAntidiagonal (s t u : Set S) (a : S) : Set (S × S × S) :=
  {x | x.1 ∈ s ∧ x.2.1 ∈ t ∧ x.2.2 ∈ u ∧ x.1 * x.2.1 * x.2.2 = a}

set_option backward.privateInPublic true in
@[to_additive (attr := simp)]
private theorem mem_mulTripleAntidiagonal {s t u : Set S} {a : S} {x : S × S × S} :
    x ∈ mulTripleAntidiagonal s t u a ↔
      x.1 ∈ s ∧ x.2.1 ∈ t ∧ x.2.2 ∈ u ∧ x.1 * x.2.1 * x.2.2 = a :=
  Iff.rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The fiber of triple multiplication at `x`: all triples `(a, b, c)` with `a * b * c = x`. -/
@[to_additive (attr := irreducible) tripleAddFiber
  /-- The fiber of triple addition at `x`: all triples `(a, b, c)` with `a + b + c = x`. -/]
def tripleFiber (x : M) : Set (M × M × M) :=
  mulTripleAntidiagonal Set.univ Set.univ Set.univ x

@[to_additive mem_tripleAddFiber]
theorem mem_tripleFiber {x : M} {abc : M × M × M} :
    abc ∈ tripleFiber x ↔ abc.1 * abc.2.1 * abc.2.2 = x := by
  simp [tripleFiber, mulTripleAntidiagonal]

set_option backward.privateInPublic true in
/-- Left association equivalence for reindexing nested sums. -/
@[to_additive leftAddAssocEquiv /-- Left association equivalence for reindexing nested sums. -/]
private def leftAssocEquiv (x : M) : (Σ cd : mulFiber x, mulFiber cd.1.1) ≃ tripleFiber x where
  toFun := fun ⟨⟨⟨c, d⟩, hcd⟩, ⟨⟨a, b⟩, hab⟩⟩ =>
    ⟨⟨a, b, d⟩, by
      simp only [mem_tripleFiber, mem_mulFiber] at hcd hab ⊢
      rw [← hcd, ← hab, mul_assoc]⟩
  invFun := fun ⟨⟨a, b, d⟩, habd⟩ =>
    ⟨⟨⟨a * b, d⟩, by
      simp only [mem_mulFiber, mem_tripleFiber] at habd ⊢; exact habd⟩,
     ⟨⟨a, b⟩, by simp only [mem_mulFiber]⟩⟩
  left_inv := fun ⟨⟨⟨c, d⟩, hcd⟩, ⟨⟨a, b⟩, hab⟩⟩ => by
    simp only [mem_mulFiber] at hab; subst hab; rfl
  right_inv := fun ⟨⟨a, b, d⟩, habd⟩ => rfl

set_option backward.privateInPublic true in
/-- Right association equivalence for reindexing nested sums. -/
@[to_additive rightAddAssocEquiv
  /-- Right association equivalence for reindexing nested sums. -/]
private def rightAssocEquiv (x : M) : (Σ ae : mulFiber x, mulFiber ae.1.2) ≃ tripleFiber x where
  toFun := fun ⟨⟨⟨a, e⟩, hae⟩, ⟨⟨b, d⟩, hbd⟩⟩ =>
    ⟨⟨a, b, d⟩, by
      simp only [mem_tripleFiber, mem_mulFiber] at hae hbd ⊢
      rw [← hae, ← hbd, mul_assoc]⟩
  invFun := fun ⟨⟨a, b, d⟩, habd⟩ =>
    ⟨⟨⟨a, b * d⟩, by
      simp only [mem_mulFiber, mem_tripleFiber] at habd ⊢
      rw [← mul_assoc]; exact habd⟩,
     ⟨⟨b, d⟩, by simp only [mem_mulFiber]⟩⟩
  left_inv := fun ⟨⟨⟨a, e⟩, hae⟩, ⟨⟨b, d⟩, hbd⟩⟩ => by
    simp only [mem_mulFiber] at hbd; subst hbd; rfl
  right_inv := fun ⟨⟨a, b, d⟩, habd⟩ => rfl

set_option backward.privateInPublic true in
/-- Equivalence between left and right associated nested fiber sums. -/
@[to_additive addAssocEquiv
  /-- Equivalence between left and right associated nested fiber sums. -/]
private def assocEquiv (x : M) :
    (Σ cd : mulFiber x, mulFiber cd.1.1) ≃ (Σ ae : mulFiber x, mulFiber ae.1.2) :=
  (leftAssocEquiv x).trans (rightAssocEquiv x).symm

end TripleFiber

/-! ### Convolution Definition and Existence -/

section Definition

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

/-- The convolution of `f` and `g` with bilinear map `L` exists at `x` when the sum over
the fiber is summable. -/
@[to_additive (dont_translate := S E E' F) AddConvolutionExistsAt
  /-- Additive convolution exists at `x` when the fiber sum is summable. -/]
def ConvolutionExistsAt (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) : Prop :=
  Summable fun ab : mulFiber x => L (f ab.1.1) (g ab.1.2)

/-- The convolution of `f` and `g` with bilinear map `L` exists when it exists at every point. -/
@[to_additive (dont_translate := S E E' F) AddConvolutionExists
  /-- Additive convolution exists when it exists at every point. -/]
def ConvolutionExists (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : Prop :=
  ∀ x, ConvolutionExistsAt L f g x

/-- The discrete convolution of `f` and `g` using bilinear map `L`:
`(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`. -/
@[to_additive (dont_translate := S E E' F) addConvolution
  /-- Additive convolution: `(f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1) (g ab.2)`. -/]
def convolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : M → F :=
  fun x => ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)

/-- Notation for discrete convolution with explicit bilinear map. -/
scoped notation:70 f:70 " ⋆[" L:70 "] " g:71 => convolution L f g

/-- Notation for additive convolution. -/
scoped notation:70 f:70 " ⋆₊[" L "] " g:71 => addConvolution L f g

@[to_additive (dont_translate := S E E' F) (attr := simp) addConvolution_apply]
theorem convolution_apply (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2) := rfl

/-- Left zero: `0 ⋆[L] f = 0`. -/
@[to_additive (dont_translate := S E E' F) (attr := simp) zero_addConvolution]
theorem zero_convolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E') :
    (0 : M → E) ⋆[L] f = 0 := by
  ext x; simp only [convolution_apply, Pi.zero_apply, map_zero, LinearMap.zero_apply, tsum_zero]

/-- Right zero: `f ⋆[L] 0 = 0`. -/
@[to_additive (dont_translate := S E E' F) (attr := simp) addConvolution_zero]
theorem convolution_zero (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) :
    f ⋆[L] (0 : M → E') = 0 := by
  ext x; simp only [convolution_apply, Pi.zero_apply, map_zero, tsum_zero]

end Definition

/-! ### Ring Multiplication Specialization -/

section RingMul

variable [Monoid M] {R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- Convolution using ring multiplication. This is `convolution (LinearMap.mul R R)`. -/
@[to_additive (dont_translate := R) addRingConvolution
  /-- Additive convolution using ring multiplication. -/]
def ringConvolution (f g : M → R) : M → R := convolution (LinearMap.mul R R) f g

/-- Notation for ring multiplication convolution. -/
scoped notation:70 f:70 " ⋆ₘ " g:71 => ringConvolution f g

/-- Notation for additive ring multiplication convolution. -/
scoped notation:70 f:70 " ⋆₊ₘ " g:71 => addRingConvolution f g

@[to_additive (dont_translate := R) addRingConvolution_apply]
theorem ringConvolution_apply (f g : M → R) (x : M) :
    (f ⋆ₘ g) x = ∑' ab : mulFiber x, f ab.1.1 * g ab.1.2 := rfl

@[to_additive (dont_translate := R) (attr := simp) zero_addRingConvolution]
theorem zero_ringConvolution (f : M → R) : (0 : M → R) ⋆ₘ f = 0 := by
  ext x; simp only [ringConvolution_apply, Pi.zero_apply, zero_mul, tsum_zero]

@[to_additive (dont_translate := R) (attr := simp) addRingConvolution_zero]
theorem ringConvolution_zero (f : M → R) : f ⋆ₘ (0 : M → R) = 0 := by
  ext x; simp only [ringConvolution_apply, Pi.zero_apply, mul_zero, tsum_zero]

end RingMul

/-! ### Commutativity -/

section Commutative

variable [CommMonoid M] [CommSemiring S] [AddCommMonoid E] [Module S E] [TopologicalSpace E]

/-- Swap equivalence for `mulFiber`: `(a, b) ↦ (b, a)` is an equivalence on the fiber. -/
@[to_additive /-- Swap equivalence for `addFiber`. -/]
def mulFiber_swapEquiv (x : M) : mulFiber x ≃ mulFiber x where
  toFun := fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mul_comm]⟩
  invFun := fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mul_comm]⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

/-- Commutativity for symmetric bilinear maps on commutative monoids. -/
@[to_additive (dont_translate := S E) addConvolution_comm]
theorem convolution_comm (L : E →ₗ[S] E →ₗ[S] E) (f g : M → E) (hL : ∀ x y, L x y = L y x) :
    f ⋆[L] g = g ⋆[L] f := by
  ext x; simp only [convolution_apply]
  rw [← (mulFiber_swapEquiv x).tsum_eq]
  congr 1; funext ⟨⟨a, b⟩, _⟩
  exact hL (f b) (g a)

end Commutative

section RingConvolutionComm

variable [CommMonoid M] {R : Type*} [CommSemiring R] [TopologicalSpace R]

@[to_additive (dont_translate := R) addRingConvolution_comm]
theorem ringConvolution_comm (f g : M → R) : f ⋆ₘ g = g ⋆ₘ f :=
  convolution_comm (LinearMap.mul R R) f g (fun x y => mul_comm x y)

end RingConvolutionComm

/-! ### Associativity -/

section Associativity

variable [Monoid M] [CommSemiring S]

section TripleConvolutionExistence

variable {E E' E'' F' G : Type*}
variable [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid E'']
variable [AddCommMonoid F'] [AddCommMonoid G]
variable [Module S E] [Module S E'] [Module S E''] [Module S F'] [Module S G]
variable [TopologicalSpace G]

/-- Triple convolution exists at `x` when the sum over `tripleFiber x` is summable. -/
@[to_additive (dont_translate := S) TripleAddConvolutionExistsAt
  /-- Triple additive convolution exists at `x` when the sum over
  `tripleAddFiber x` is summable. -/]
def TripleConvolutionExistsAt
    (L₃ : E →ₗ[S] F' →ₗ[S] G) (L₄ : E' →ₗ[S] E'' →ₗ[S] F')
    (f : M → E) (g : M → E') (h : M → E'') (x : M) : Prop :=
  Summable fun p : tripleFiber x => L₃ (f p.1.1) (L₄ (g p.1.2.1) (h p.1.2.2))

/-- Triple convolution exists when it exists at every point. -/
@[to_additive (dont_translate := S) TripleAddConvolutionExists
  /-- Triple additive convolution exists when it exists at every point. -/]
def TripleConvolutionExists
    (L₃ : E →ₗ[S] F' →ₗ[S] G) (L₄ : E' →ₗ[S] E'' →ₗ[S] F')
    (f : M → E) (g : M → E') (h : M → E'') : Prop :=
  ∀ x, TripleConvolutionExistsAt L₃ L₄ f g h x

end TripleConvolutionExistence

section AssociativityTheorem

variable {E E' E'' F F' G : Type*}
variable [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid E'']
variable [AddCommMonoid F] [AddCommMonoid F'] [AddCommMonoid G]
variable [Module S E] [Module S E'] [Module S E''] [Module S F] [Module S F'] [Module S G]
variable [TopologicalSpace F] [TopologicalSpace F'] [TopologicalSpace G]
variable [T3Space G] [ContinuousAdd G]

/-- Convolution associativity at a point using `assocEquiv` as the bijection.

The bilinear compatibility follows from `hL : L₂ (L x y) z = L₃ x (L₄ y z)`. -/
@[to_additive (dont_translate := S M) addConvolution_assoc_at]
theorem convolution_assoc_at
    (L : E →ₗ[S] E' →ₗ[S] F) (L₂ : F →ₗ[S] E'' →ₗ[S] G)
    (L₃ : E →ₗ[S] F' →ₗ[S] G) (L₄ : E' →ₗ[S] E'' →ₗ[S] F')
    (hL : ∀ x y z, L₂ (L x y) z = L₃ x (L₄ y z))
    (f : M → E) (g : M → E') (h : M → E'') (x : M)
    (hSumL : Summable fun p : Σ cd : mulFiber x, mulFiber cd.1.1 =>
        L₂ (L (f p.2.1.1) (g p.2.1.2)) (h p.1.1.2))
    (hFiberL : ∀ cd : mulFiber x, Summable fun ab : mulFiber cd.1.1 =>
        L₂ (L (f ab.1.1) (g ab.1.2)) (h cd.1.2))
    (hFiberR : ∀ ae : mulFiber x, Summable fun bd : mulFiber ae.1.2 =>
        L₃ (f ae.1.1) (L₄ (g bd.1.1) (h bd.1.2)))
    (hcontL : ∀ cd : mulFiber x,
        L₂ (∑' ab : mulFiber cd.1.1, L (f ab.1.1) (g ab.1.2)) (h cd.1.2) =
        ∑' ab : mulFiber cd.1.1, L₂ (L (f ab.1.1) (g ab.1.2)) (h cd.1.2))
    (hcontR : ∀ ae : mulFiber x,
        L₃ (f ae.1.1) (∑' bd : mulFiber ae.1.2, L₄ (g bd.1.1) (h bd.1.2)) =
        ∑' bd : mulFiber ae.1.2, L₃ (f ae.1.1) (L₄ (g bd.1.1) (h bd.1.2))) :
    ((f ⋆[L] g) ⋆[L₂] h) x = (f ⋆[L₃] (g ⋆[L₄] h)) x := by
  simp only [convolution_apply]
  -- Derive hφ from bilinearity hL
  have hφ : ∀ (p : Σ cd : mulFiber x, mulFiber cd.1.1),
      L₂ (L (f p.2.1.1) (g p.2.1.2)) (h p.1.1.2) =
      L₃ (f (assocEquiv x p).1.1.1) (L₄ (g (assocEquiv x p).2.1.1) (h (assocEquiv x p).2.1.2)) :=
    fun ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩ => by simp [assocEquiv, leftAssocEquiv, rightAssocEquiv, hL]
  -- Derive right-sigma summability from left-sigma summability via assocEquiv
  have hSumR : Summable fun p : Σ ae : mulFiber x, mulFiber ae.1.2 =>
      L₃ (f p.1.1.1) (L₄ (g p.2.1.1) (h p.2.1.2)) := by
    rw [← (assocEquiv x).summable_iff]; convert hSumL using 1; funext p; exact (hφ p).symm
  -- Chain transformations: left-nested → left-sigma → right-sigma → right-nested
  have h1 : ∑' cd : mulFiber x, ∑' ab : mulFiber cd.1.1, L₂ (L (f ab.1.1) (g ab.1.2)) (h cd.1.2) =
        ∑' (p : Σ cd : mulFiber x, mulFiber cd.1.1),
          L₂ (L (f p.2.1.1) (g p.2.1.2)) (h p.1.1.2) := by
    symm; exact hSumL.tsum_sigma' hFiberL
  have h2 : ∑' (p : Σ cd : mulFiber x, mulFiber cd.1.1),
          L₂ (L (f p.2.1.1) (g p.2.1.2)) (h p.1.1.2) =
        ∑' (p : Σ ae : mulFiber x, mulFiber ae.1.2),
          L₃ (f p.1.1.1) (L₄ (g p.2.1.1) (h p.2.1.2)) := by
    rw [← (assocEquiv x).tsum_eq]; exact tsum_congr hφ
  have h3 : ∑' (p : Σ ae : mulFiber x, mulFiber ae.1.2),
          L₃ (f p.1.1.1) (L₄ (g p.2.1.1) (h p.2.1.2)) =
        ∑' ae : mulFiber x, ∑' bd : mulFiber ae.1.2,
          L₃ (f ae.1.1) (L₄ (g bd.1.1) (h bd.1.2)) := by
    exact hSumR.tsum_sigma' hFiberR
  rw [tsum_congr hcontL, h1, h2, h3, tsum_congr fun ae => (hcontR ae).symm]

/-- Convolution is associative: `(f ⋆[L] g) ⋆[L₂] h = f ⋆[L₃] (g ⋆[L₄] h)`.

Requires `hTriple : TripleConvolutionExists` (summability over `tripleFiber x`) and derives
sigma summability internally. -/
@[to_additive (dont_translate := S M) addConvolution_assoc]
theorem convolution_assoc
    (L : E →ₗ[S] E' →ₗ[S] F) (L₂ : F →ₗ[S] E'' →ₗ[S] G)
    (L₃ : E →ₗ[S] F' →ₗ[S] G) (L₄ : E' →ₗ[S] E'' →ₗ[S] F')
    (hL : ∀ x y z, L₂ (L x y) z = L₃ x (L₄ y z))
    (f : M → E) (g : M → E') (h : M → E'')
    (hTriple : TripleConvolutionExists L₃ L₄ f g h)
    (hFiberL : ∀ x (cd : mulFiber x), Summable fun ab : mulFiber cd.1.1 =>
        L₂ (L (f ab.1.1) (g ab.1.2)) (h cd.1.2))
    (hFiberR : ∀ x (ae : mulFiber x), Summable fun bd : mulFiber ae.1.2 =>
        L₃ (f ae.1.1) (L₄ (g bd.1.1) (h bd.1.2)))
    (hcontL : ∀ x (cd : mulFiber x),
        L₂ (∑' ab : mulFiber cd.1.1, L (f ab.1.1) (g ab.1.2)) (h cd.1.2) =
        ∑' ab : mulFiber cd.1.1, L₂ (L (f ab.1.1) (g ab.1.2)) (h cd.1.2))
    (hcontR : ∀ x (ae : mulFiber x),
        L₃ (f ae.1.1) (∑' bd : mulFiber ae.1.2, L₄ (g bd.1.1) (h bd.1.2)) =
        ∑' bd : mulFiber ae.1.2, L₃ (f ae.1.1) (L₄ (g bd.1.1) (h bd.1.2))) :
    (f ⋆[L] g) ⋆[L₂] h = f ⋆[L₃] (g ⋆[L₄] h) := by
  ext x
  have hSigmaL : Summable fun p : Σ cd : mulFiber x, mulFiber cd.1.1 =>
      L₂ (L (f p.2.1.1) (g p.2.1.2)) (h p.1.1.2) := by
    have : Summable ((fun p : tripleFiber x => L₃ (f p.1.1) (L₄ (g p.1.2.1) (h p.1.2.2))) ∘
        (leftAssocEquiv x)) := (leftAssocEquiv x).summable_iff.mpr (hTriple x)
    convert this using 1; ext ⟨⟨⟨c, d⟩, _⟩, ⟨⟨a, b⟩, _⟩⟩; simp [leftAssocEquiv, hL]
  exact convolution_assoc_at L L₂ L₃ L₄ hL f g h x hSigmaL (hFiberL x) (hFiberR x)
    (hcontL x) (hcontR x)

end AssociativityTheorem

section RingConvolutionAssoc

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [T3Space R] [ContinuousAdd R]

/-- Ring convolution associativity at a point: `((f ⋆ₘ g) ⋆ₘ h) x = (f ⋆ₘ (g ⋆ₘ h)) x`.

Specializes `convolution_assoc_at` to `LinearMap.mul R R`; bilinearity becomes `mul_assoc`. -/
@[to_additive (dont_translate := R M) addRingConvolution_assoc_at]
theorem ringConvolution_assoc_at (f g h : M → R) (x : M)
    (hSumL : Summable fun p : Σ cd : mulFiber x, mulFiber cd.1.1 =>
        f p.2.1.1 * g p.2.1.2 * h p.1.1.2)
    (hFiberL : ∀ cd : mulFiber x, Summable fun ab : mulFiber cd.1.1 =>
        f ab.1.1 * g ab.1.2 * h cd.1.2)
    (hFiberR : ∀ ae : mulFiber x, Summable fun bd : mulFiber ae.1.2 =>
        f ae.1.1 * (g bd.1.1 * h bd.1.2))
    (hcontL : ∀ cd : mulFiber x,
        (∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2) * h cd.1.2 =
        ∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2 * h cd.1.2)
    (hcontR : ∀ ae : mulFiber x,
        f ae.1.1 * (∑' bd : mulFiber ae.1.2, g bd.1.1 * h bd.1.2) =
        ∑' bd : mulFiber ae.1.2, f ae.1.1 * (g bd.1.1 * h bd.1.2)) :
    ((f ⋆ₘ g) ⋆ₘ h) x = (f ⋆ₘ (g ⋆ₘ h)) x :=
  convolution_assoc_at (LinearMap.mul R R) (LinearMap.mul R R) (LinearMap.mul R R)
    (LinearMap.mul R R) (fun x y z => mul_assoc x y z) f g h x hSumL hFiberL hFiberR hcontL hcontR

/-- Ring convolution associativity: `(f ⋆ₘ g) ⋆ₘ h = f ⋆ₘ (g ⋆ₘ h)`.

Specializes `convolution_assoc` to `LinearMap.mul R R`; bilinearity becomes `mul_assoc`. -/
@[to_additive (dont_translate := R M) addRingConvolution_assoc]
theorem ringConvolution_assoc (f g h : M → R)
    (hTriple : TripleConvolutionExists (LinearMap.mul R R) (LinearMap.mul R R) f g h)
    (hFiberL : ∀ x (cd : mulFiber x), Summable fun ab : mulFiber cd.1.1 =>
        f ab.1.1 * g ab.1.2 * h cd.1.2)
    (hFiberR : ∀ x (ae : mulFiber x), Summable fun bd : mulFiber ae.1.2 =>
        f ae.1.1 * (g bd.1.1 * h bd.1.2))
    (hcontL : ∀ x (cd : mulFiber x),
        (∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2) * h cd.1.2 =
        ∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2 * h cd.1.2)
    (hcontR : ∀ x (ae : mulFiber x),
        f ae.1.1 * (∑' bd : mulFiber ae.1.2, g bd.1.1 * h bd.1.2) =
        ∑' bd : mulFiber ae.1.2, f ae.1.1 * (g bd.1.1 * h bd.1.2)) :
    (f ⋆ₘ g) ⋆ₘ h = f ⋆ₘ (g ⋆ₘ h) :=
  convolution_assoc (LinearMap.mul R R) (LinearMap.mul R R) (LinearMap.mul R R) (LinearMap.mul R R)
    (fun x y z => mul_assoc x y z) f g h hTriple hFiberL hFiberR hcontL hcontR

end RingConvolutionAssoc

end Associativity

end DiscreteConvolution

end
