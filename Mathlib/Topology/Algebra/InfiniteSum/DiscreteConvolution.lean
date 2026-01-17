/-
Copyright (c) 2026 Fengyang Wang. All rights reserved.
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
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Algebra.BigOperators.CauchyProduct

/-!
# Discrete Convolution

Discrete convolution over monoids: `(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`
where `mulFiber x = {(a, b) | a * b = x}`. Additive monoids are also supported.

## Design

Uses a bilinear map `L : E →ₗ[S] E' →ₗ[S] F` to combine values, following
`MeasureTheory.convolution`. For specializing to ring multiplication,
use `ringConvolution` which is given by `convolution (LinearMap.mul ℕ R)`.

The index monoid `M` can be non-commutative (group algebras R[G] with non-abelian G).
Coefficient ring only requires `[Semiring R]` (commutativity needed for `ringConvolution_comm`).

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
    (f ⋆ᵣ₊ g) = MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ R) .count
```

Parallel API:
- `ConvolutionExistsAt`, `ConvolutionExists`, `convolution`,
  `convolution_zero`, `zero_convolution`, `convolution_assoc`.
- Convolution associativity has the same bilinearity hypothesis:
  `hL : ∀ x y z, L₂ (L x y) z = L₃ x (L₄ y z)`.

Differences (discrete ↔ MeasureTheory):
- Domain: `Monoid M` ↔ `AddGroup G`, no subtraction needed for discrete
- Bilinear map: `E →ₗ[S] E' →ₗ[S] F` ↔ `E →L[𝕜] E' →L[𝕜] F`, no continuity needed
- Associativity: `Summable` ↔ `AEStronglyMeasurable` + norm convolution conditions
- Commutativity: `convolution_comm` ↔ `convolution_flip` (needs `IsAddLeftInvariant`)
- `@[to_additive]`: Discrete supports both mul/add versions; MeasureTheory is additive only

## Main Results

- `zero_convolution`, `convolution_zero`: zero laws
- `convolution_comm`, `ringConvolution_comm`: commutativity for symmetric bilinear maps
- Associativity (three API layers with increasing specialization):
  - `convolution_assoc`: most general, arbitrary bilinear maps `L`, `L₂`, `L₃`, `L₄`
  - `ringConvolution_assoc`: specializes to `LinearMap.mul ℕ R`
  - `completeUniformRingConvolution_assoc`: derives fiber summabilities
- HasMulAntidiagonal / HasAntidiagonal bridge (for finite support, e.g., ℕ, ℕ × ℕ):
  - `mulFiber_eq_mulAntidiagonal` / `addFiber_eq_antidiagonal`: fiber equals antidiagonal
  - `convolution_eq_sum_mulAntidiagonal` / `addConvolution_eq_sum_antidiagonal`:
    `tsum` reduces to `Finset.sum`
  - `ringConvolution_eq_mulCauchyProduct` / `addRingConvolution_eq_cauchyProduct`:
    bridge to `MulCauchyProduct` / `CauchyProduct`
- MulCauchyProduct / CauchyProduct (see `Mathlib.Algebra.BigOperators.CauchyProduct`):
  - Purely algebraic finite-sum convolution (no topology needed)

## Notation

| Notation     | Operation                                       |
|--------------|-------------------------------------------------|
| `f ⋆[L] g`   | `∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)`   |
| `f ⋆₊[L] g`  | `∑' ab : addFiber x, L (f ab.1.1) (g ab.1.2)`   |
| `f ⋆ᵣ g`     | `∑' ab : mulFiber x, f ab.1.1 * g ab.1.2`       |
| `f ⋆ᵣ₊ g`    | `∑' ab : addFiber x, f ab.1.1 * g ab.1.2`       |

To use the simpler `⋆` notation, define a scoped notation in your file:
```
scoped notation:67 f:68 " ⋆ " g:67 => f ⋆ᵣ g   -- multiplicative
scoped notation:67 f:68 " ⋆ " g:67 => f ⋆ᵣ₊ g  -- additive
```

Precedence design: `f:68` and `g:67` gives right associativity (`f ⋆ g ⋆ h` parses as
`f ⋆ (g ⋆ h)`), matching function composition `∘` and `MeasureTheory.convolution`.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace DiscreteConvolution

variable {M S E E' E'' F F' G R : Type*}

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

/-- Useful for showing `mulFiber 1` is nonempty, e.g., when proving convolution has an identity. -/
@[to_additive /-- Useful for showing `addFiber 0` is nonempty,
e.g., when proving convolution has an identity. -/]
lemma mulFiber_one_mem : (1, 1) ∈ mulFiber (1 : M) := by
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

@[to_additive]
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
  simp only [tripleFiber, mem_mulTripleAntidiagonal, Set.mem_univ, true_and]

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
scoped notation:67 f:68 " ⋆[" L "] " g:67 => convolution L f g

/-- Notation for additive convolution. -/
scoped notation:67 f:68 " ⋆₊[" L "] " g:67 => addConvolution L f g

@[to_additive (dont_translate := S E E' F) (attr := simp) addConvolution_apply]
lemma convolution_apply (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2) := rfl

/-- Left zero: `0 ⋆[L] f = 0`. -/
@[to_additive (dont_translate := S E E' F) (attr := simp) zero_addConvolution]
lemma zero_convolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E') :
    (0 : M → E) ⋆[L] f = 0 := by
  ext x; simp only [convolution_apply, Pi.zero_apply, map_zero, LinearMap.zero_apply, tsum_zero]

/-- Right zero: `f ⋆[L] 0 = 0`. -/
@[to_additive (dont_translate := S E E' F) (attr := simp) addConvolution_zero]
lemma convolution_zero (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) :
    f ⋆[L] (0 : M → E') = 0 := by
  ext x; simp only [convolution_apply, Pi.zero_apply, map_zero, tsum_zero]

variable [T2Space F] [ContinuousAdd F]

/-- Right distributivity at a point: `(f ⋆[L] (g + g')) x = (f ⋆[L] g) x + (f ⋆[L] g') x`. -/
@[to_additive (dont_translate := S E E' F)]
theorem ConvolutionExistsAt.distrib_add {f : M → E} {g g' : M → E'} {x : M}
    (L : E →ₗ[S] E' →ₗ[S] F) (hfg : ConvolutionExistsAt L f g x)
    (hfg' : ConvolutionExistsAt L f g' x) :
    (f ⋆[L] (g + g')) x = (f ⋆[L] g) x + (f ⋆[L] g') x := by
  simp only [convolution_apply, Pi.add_apply, map_add]
  exact hfg.tsum_add hfg'

/-- Right distributivity: `f ⋆[L] (g + g') = f ⋆[L] g + f ⋆[L] g'`. -/
@[to_additive (dont_translate := S E E' F)]
theorem ConvolutionExists.distrib_add {f : M → E} {g g' : M → E'} (L : E →ₗ[S] E' →ₗ[S] F)
    (hfg : ConvolutionExists L f g) (hfg' : ConvolutionExists L f g') :
    f ⋆[L] (g + g') = f ⋆[L] g + f ⋆[L] g' := by
  ext x; exact (hfg x).distrib_add L (hfg' x)

/-- Left distributivity at a point: `((f + f') ⋆[L] g) x = (f ⋆[L] g) x + (f' ⋆[L] g) x`. -/
@[to_additive (dont_translate := S E E' F)]
theorem ConvolutionExistsAt.add_distrib {f f' : M → E} {g : M → E'} {x : M}
    (L : E →ₗ[S] E' →ₗ[S] F) (hfg : ConvolutionExistsAt L f g x)
    (hfg' : ConvolutionExistsAt L f' g x) :
    ((f + f') ⋆[L] g) x = (f ⋆[L] g) x + (f' ⋆[L] g) x := by
  simp only [convolution_apply, Pi.add_apply, LinearMap.map_add₂]
  exact hfg.tsum_add hfg'

/-- Left distributivity: `(f + f') ⋆[L] g = f ⋆[L] g + f' ⋆[L] g`. -/
@[to_additive (dont_translate := S E E' F)]
theorem ConvolutionExists.add_distrib {f f' : M → E} {g : M → E'} (L : E →ₗ[S] E' →ₗ[S] F)
    (hfg : ConvolutionExists L f g) (hfg' : ConvolutionExists L f' g) :
    (f + f') ⋆[L] g = f ⋆[L] g + f' ⋆[L] g := by
  ext x; exact (hfg x).add_distrib L (hfg' x)

end Definition

/-! ### Ring Multiplication Specialization -/

section RingMul

variable [Monoid M] [Semiring R] [TopologicalSpace R]

/-- Convolution using ring multiplication. This is `convolution (LinearMap.mul ℕ R)`. -/
@[to_additive (dont_translate := R) addRingConvolution
  /-- Additive convolution using ring multiplication. -/]
def ringConvolution (f g : M → R) : M → R := convolution (LinearMap.mul ℕ R) f g

/-- Notation `⋆ᵣ` for ring multiplication convolution (topological/infinite sum version).
Users who want the simplest `⋆` notation can define their own scoped notation. -/
scoped notation:67 f:68 " ⋆ᵣ " g:67 => ringConvolution f g

/-- Notation `⋆ᵣ₊` for additive ring multiplication convolution.
Users who want the simplest `⋆` notation can define their own scoped notation. -/
scoped notation:67 f:68 " ⋆ᵣ₊ " g:67 => addRingConvolution f g

@[to_additive (dont_translate := R) addRingConvolution_apply]
lemma ringConvolution_apply (f g : M → R) (x : M) :
    (f ⋆ᵣ g) x = ∑' ab : mulFiber x, f ab.1.1 * g ab.1.2 := rfl

@[to_additive (dont_translate := R) (attr := simp) zero_addRingConvolution]
lemma zero_ringConvolution (f : M → R) : (0 : M → R) ⋆ᵣ f = 0 := by
  ext x; simp only [ringConvolution_apply, Pi.zero_apply, zero_mul, tsum_zero]

@[to_additive (dont_translate := R) (attr := simp) addRingConvolution_zero]
lemma ringConvolution_zero (f : M → R) : f ⋆ᵣ (0 : M → R) = 0 := by
  ext x; simp only [ringConvolution_apply, Pi.zero_apply, mul_zero, tsum_zero]

end RingMul

/-! ### Commutativity -/

section CommMonoid

variable [CommMonoid M] [CommSemiring S] [AddCommMonoid E] [Module S E] [TopologicalSpace E]

/-- Swap equivalence for `mulFiber`: `(a, b) ↦ (b, a)` is an equivalence on the fiber. -/
@[to_additive /-- Swap equivalence for `addFiber`. -/]
private def mulFiber_swapEquiv (x : M) : mulFiber x ≃ mulFiber x where
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

end CommMonoid

section RingConvolutionComm

variable [CommMonoid M] [CommSemiring R] [TopologicalSpace R]

@[to_additive (dont_translate := R) addRingConvolution_comm]
theorem ringConvolution_comm (f g : M → R) : f ⋆ᵣ g = g ⋆ᵣ f :=
  convolution_comm (LinearMap.mul ℕ R) f g (fun x y => mul_comm x y)

end RingConvolutionComm

/-! ### Associativity -/

section Associativity

variable [Monoid M] [CommSemiring S]

/-! Only the right-associated form `L₃ (f a) (L₄ (g b) (h c))` is needed as a witness,
the left-associated form's summability is derived via `assocEquiv` and `hL` -/
section TripleConvolutionExistence

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

variable [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid E'']
variable [AddCommMonoid F] [AddCommMonoid F'] [AddCommMonoid G]
variable [Module S E] [Module S E'] [Module S E''] [Module S F] [Module S F'] [Module S G]
variable [TopologicalSpace F] [TopologicalSpace F'] [TopologicalSpace G]
variable [T3Space G] [ContinuousAdd G]

/-- Convolution associativity at a point using `TripleConvolutionExistsAt`.

The bilinear compatibility follows from `hL : L₂ (L x y) z = L₃ x (L₄ y z)`. -/
@[to_additive (dont_translate := S) addConvolution_assoc_at]
theorem convolution_assoc_at
    (L : E →ₗ[S] E' →ₗ[S] F) (L₂ : F →ₗ[S] E'' →ₗ[S] G)
    (L₃ : E →ₗ[S] F' →ₗ[S] G) (L₄ : E' →ₗ[S] E'' →ₗ[S] F')
    (hL : ∀ x y z, L₂ (L x y) z = L₃ x (L₄ y z))
    (f : M → E) (g : M → E') (h : M → E'') (x : M)
    (hTriple : TripleConvolutionExistsAt L₃ L₄ f g h x)
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
  -- Derive left-sigma summability from TripleConvolutionExistsAt via leftAssocEquiv
  have hSumL : Summable fun p : Σ cd : mulFiber x, mulFiber cd.1.1 =>
      L₂ (L (f p.2.1.1) (g p.2.1.2)) (h p.1.1.2) := by
    have : Summable ((fun p : tripleFiber x => L₃ (f p.1.1) (L₄ (g p.1.2.1) (h p.1.2.2))) ∘
        (leftAssocEquiv x)) := (leftAssocEquiv x).summable_iff.mpr hTriple
    convert this using 1; ext ⟨⟨⟨c, d⟩, _⟩, ⟨⟨a, b⟩, _⟩⟩; simp [leftAssocEquiv, hL]
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

Requires `hTriple : TripleConvolutionExists` (summability over `tripleFiber x`). -/
@[to_additive (dont_translate := S) addConvolution_assoc]
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
  exact convolution_assoc_at L L₂ L₃ L₄ hL f g h x (hTriple x) (hFiberL x) (hFiberR x)
    (hcontL x) (hcontR x)

end AssociativityTheorem

section RingConvolutionAssoc

variable [Semiring R] [TopologicalSpace R] [T3Space R] [ContinuousAdd R]

/-- Ring convolution associativity at a point: `((f ⋆ᵣ g) ⋆ᵣ h) x = (f ⋆ᵣ (g ⋆ᵣ h)) x`.

Specializes `convolution_assoc_at` to `LinearMap.mul ℕ R`; bilinearity becomes `mul_assoc`. -/
@[to_additive (dont_translate := R) addRingConvolution_assoc_at]
theorem ringConvolution_assoc_at (f g h : M → R) (x : M)
    (hTriple : TripleConvolutionExistsAt (LinearMap.mul ℕ R) (LinearMap.mul ℕ R) f g h x)
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
    ((f ⋆ᵣ g) ⋆ᵣ h) x = (f ⋆ᵣ (g ⋆ᵣ h)) x :=
  convolution_assoc_at (LinearMap.mul ℕ R) (LinearMap.mul ℕ R) (LinearMap.mul ℕ R)
    (LinearMap.mul ℕ R) (fun x y z => mul_assoc x y z) f g h x hTriple hFiberL hFiberR hcontL hcontR

/-- Ring convolution associativity: `(f ⋆ᵣ g) ⋆ᵣ h = f ⋆ᵣ (g ⋆ᵣ h)`.

Specializes `convolution_assoc` to `LinearMap.mul ℕ R`; bilinearity becomes `mul_assoc`. -/
@[to_additive (dont_translate := R) addRingConvolution_assoc]
theorem ringConvolution_assoc (f g h : M → R)
    (hTriple : TripleConvolutionExists (LinearMap.mul ℕ R) (LinearMap.mul ℕ R) f g h)
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
    (f ⋆ᵣ g) ⋆ᵣ h = f ⋆ᵣ (g ⋆ᵣ h) :=
  convolution_assoc (LinearMap.mul ℕ R) (LinearMap.mul ℕ R) (LinearMap.mul ℕ R) (LinearMap.mul ℕ R)
    (fun x y z => mul_assoc x y z) f g h hTriple hFiberL hFiberR hcontL hcontR

end RingConvolutionAssoc

section CompleteUniformRingConvolutionAssoc

variable [Ring R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalSemiring R]
variable [T2Space R] [CompleteSpace R]

/-- Ring convolution associativity for complete uniform rings at a point.
Derives `hFiberL`/`hFiberR` from `hTriple`; requires inner convolution summabilities. -/
@[to_additive (dont_translate := R) addCompleteUniformRingConvolution_assoc_at]
theorem completeUniformRingConvolution_assoc_at (f g h : M → R) (x : M)
    (hTriple : TripleConvolutionExistsAt (LinearMap.mul ℕ R) (LinearMap.mul ℕ R) f g h x)
    (hConvFG : ∀ c : M, Summable fun ab : mulFiber c => f ab.1.1 * g ab.1.2)
    (hConvGH : ∀ e : M, Summable fun bd : mulFiber e => g bd.1.1 * h bd.1.2) :
    ((f ⋆ᵣ g) ⋆ᵣ h) x = (f ⋆ᵣ (g ⋆ᵣ h)) x := by
  -- Derive left-sigma summability from hTriple via leftAssocEquiv
  have hSumL : Summable fun p : Σ cd : mulFiber x, mulFiber cd.1.1 =>
      f p.2.1.1 * g p.2.1.2 * h p.1.1.2 := by
    have : Summable ((fun p : tripleFiber x => f p.1.1 * (g p.1.2.1 * h p.1.2.2)) ∘
        (leftAssocEquiv x)) := (leftAssocEquiv x).summable_iff.mpr hTriple
    convert this using 1; ext ⟨⟨⟨c, d⟩, _⟩, ⟨⟨a, b⟩, _⟩⟩; simp [leftAssocEquiv, mul_assoc]
  -- Derive right-sigma summability from hTriple via rightAssocEquiv
  have hSumR : Summable fun p : Σ ae : mulFiber x, mulFiber ae.1.2 =>
      f p.1.1.1 * (g p.2.1.1 * h p.2.1.2) := by
    have : Summable ((fun p : tripleFiber x => f p.1.1 * (g p.1.2.1 * h p.1.2.2)) ∘
        (rightAssocEquiv x)) := (rightAssocEquiv x).summable_iff.mpr hTriple
    convert this using 1
  -- Derive fiber summabilities via sigma_factor (using CompleteSpace)
  have hFiberL : ∀ cd : mulFiber x, Summable fun ab : mulFiber cd.1.1 =>
      f ab.1.1 * g ab.1.2 * h cd.1.2 := fun cd => hSumL.sigma_factor cd
  have hFiberR : ∀ ae : mulFiber x, Summable fun bd : mulFiber ae.1.2 =>
      f ae.1.1 * (g bd.1.1 * h bd.1.2) := fun ae => hSumR.sigma_factor ae
  -- Derive continuity conditions via tsum_mul_right/tsum_mul_left (using ContinuousMul)
  have hcontL : ∀ cd : mulFiber x,
      (∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2) * h cd.1.2 =
      ∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2 * h cd.1.2 := fun cd =>
    ((hConvFG cd.1.1).tsum_mul_right (h cd.1.2)).symm
  have hcontR : ∀ ae : mulFiber x,
      f ae.1.1 * (∑' bd : mulFiber ae.1.2, g bd.1.1 * h bd.1.2) =
      ∑' bd : mulFiber ae.1.2, f ae.1.1 * (g bd.1.1 * h bd.1.2) := fun ae =>
    ((hConvGH ae.1.2).tsum_mul_left (f ae.1.1)).symm
  exact ringConvolution_assoc_at f g h x hTriple hFiberL hFiberR hcontL hcontR

/-- Ring convolution associativity for complete uniform rings.
Derives `hFiberL`/`hFiberR` from `hTriple`; requires inner convolution summabilities. -/
@[to_additive (dont_translate := R) addCompleteUniformRingConvolution_assoc]
theorem completeUniformRingConvolution_assoc (f g h : M → R)
    (hTriple : TripleConvolutionExists (LinearMap.mul ℕ R) (LinearMap.mul ℕ R) f g h)
    (hConvFG : ∀ c : M, Summable fun ab : mulFiber c => f ab.1.1 * g ab.1.2)
    (hConvGH : ∀ e : M, Summable fun bd : mulFiber e => g bd.1.1 * h bd.1.2) :
    (f ⋆ᵣ g) ⋆ᵣ h = f ⋆ᵣ (g ⋆ᵣ h) := by
  ext x; exact completeUniformRingConvolution_assoc_at f g h x (hTriple x) hConvFG hConvGH

end CompleteUniformRingConvolutionAssoc

end Associativity

/-! ### HasMulAntidiagonal / HasAntidiagonal Bridge

For types with `Finset.HasMulAntidiagonal` or `Finset.HasAntidiagonal`, the fiber is finite
and equals the (multiplicative or additive) antidiagonal. The `tsum` reduces to `Finset.sum`.

The multiplicative versions use `Finset.mulAntidiagonal`, and the additive versions
(generated via `@[to_additive]`) use `Finset.antidiagonal`.

This also provides the bridge to `MulCauchyProduct`/`CauchyProduct`: ring convolution equals
the corresponding CauchyProduct for these types.
See `Mathlib.Algebra.BigOperators.CauchyProduct`. -/

section MulAntidiagonal

open scoped MulCauchyProduct

variable [Monoid M] [Finset.HasMulAntidiagonal M]
variable [CommSemiring S] [AddCommMonoid E] [Module S E]

/-- For types with `HasMulAntidiagonal`, the multiplicative fiber equals the mulAntidiagonal. -/
@[to_additive addFiber_eq_antidiagonal
  /-- For types with `HasAntidiagonal`, the additive fiber equals the antidiagonal. -/]
lemma mulFiber_eq_mulAntidiagonal (x : M) : mulFiber x = ↑(Finset.mulAntidiagonal x) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_coe, Finset.mem_mulAntidiagonal, mem_mulFiber]

/-- The multiplicative fiber is finite when `HasMulAntidiagonal` is available. -/
@[to_additive /-- The additive fiber is finite when `HasAntidiagonal` is available. -/]
lemma mulFiber_finite (x : M) : (mulFiber x).Finite := by
  rw [mulFiber_eq_mulAntidiagonal]
  exact (Finset.mulAntidiagonal x).finite_toSet

variable [AddCommMonoid E'] [Module S E'] [AddCommMonoid F] [Module S F]
variable [TopologicalSpace F]

/-- For `HasMulAntidiagonal` types, convolution equals a finite sum over the mulAntidiagonal. -/
@[to_additive (dont_translate := S) addConvolution_eq_sum_antidiagonal
  /-- For `HasAntidiagonal` types, additive convolution equals a finite sum
  over the antidiagonal. -/]
lemma convolution_eq_sum_mulAntidiagonal (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E')
    (x : M) : (f ⋆[L] g) x = ∑ ab ∈ Finset.mulAntidiagonal x, L (f ab.1) (g ab.2) := by
  simp only [convolution_apply]
  rw [← (Finset.mulAntidiagonal x).tsum_subtype fun ab => L (f ab.1) (g ab.2)]
  exact (Equiv.setCongr (mulFiber_eq_mulAntidiagonal x)).tsum_eq
    (fun ab => (L (f ab.1.1)) (g ab.1.2))

variable [Semiring R] [TopologicalSpace R]

/-- For `HasMulAntidiagonal` types, ring convolution equals a finite sum over the
mulAntidiagonal. -/
@[to_additive (dont_translate := R) addRingConvolution_eq_sum_antidiagonal
  /-- For `HasAntidiagonal` types, ring convolution equals a finite sum over the antidiagonal. -/]
lemma ringConvolution_eq_sum_mulAntidiagonal (f g : M → R) (x : M) :
    (f ⋆ᵣ g) x = ∑ ab ∈ Finset.mulAntidiagonal x, f ab.1 * g ab.2 :=
  convolution_eq_sum_mulAntidiagonal (LinearMap.mul ℕ R) f g x

/-- `ringConvolution` (`⋆ᵣ`) equals `MulCauchyProduct.apply` (`⋆ᶜ`) for `HasMulAntidiagonal`. -/
@[to_additive (dont_translate := R) addRingConvolution_eq_cauchyProduct
  /-- `addRingConvolution` (`⋆ᵣ₊`) equals `CauchyProduct.apply` (`⋆ᶜ₊`) for `HasAntidiagonal`. -/]
lemma ringConvolution_eq_mulCauchyProduct (f g : M → R) (x : M) :
    (f ⋆ᵣ g) x = (f ⋆ᶜ g) x :=
  ringConvolution_eq_sum_mulAntidiagonal f g x

end MulAntidiagonal

end DiscreteConvolution

end
