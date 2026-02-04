/-
Copyright (c) 2026 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.Set.MulAntidiagonal

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
  `convolution_zero`, `zero_convolution`, `convolution_assoc`,
  `distrib_add`, `add_distrib`, `smul_convolution`, `convolution_smul`.
- Convolution associativity has the same bilinearity hypothesis:
  `hL : ∀ x y z, L₂ (L x y) z = L₃ x (L₄ y z)`.

Differences (discrete ↔ MeasureTheory):
- Domain: `Monoid M` ↔ `AddGroup G`, no subtraction needed for discrete
- Bilinear map: `E →ₗ[S] E' →ₗ[S] F` ↔ `E →L[𝕜] E' →L[𝕜] F`, no continuity needed
- Associativity: `Summable` ↔ `AEStronglyMeasurable` + norm convolution conditions
- Commutativity: `convolution_comm` ↔ `convolution_flip` (needs `IsAddLeftInvariant`)
- `@[to_additive]`: Discrete supports both mul/add versions; MeasureTheory is additive only

## Main Results

- `ConvolutionExistsAt`, `ConvolutionExists`: summability conditions
- `zero_convolution`, `convolution_zero`: zero laws
- `convolution_indicator_one_left`, `convolution_indicator_one_right`: identity element
  (the identity is `Set.indicator {1} (fun _ => e)` where `L e` is the identity map)
- `distrib_add`, `add_distrib`: distributivity over addition
- `smul_convolution`, `convolution_smul`: scalar multiplication
- `convolution_comm`, `ringConvolution_comm`: commutativity for symmetric bilinear maps
- Associativity (three API layers with increasing specialization):
  - `convolution_assoc`: most general, arbitrary bilinear maps `L`, `L₂`, `L₃`, `L₄`
  - `ringConvolution_assoc`: specializes to `LinearMap.mul ℕ R`
  - `completeUniformRingConvolution_assoc`: derives fiber summabilities
- HasMulAntidiagonal / HasAntidiagonal bridge (for finite support, e.g., ℕ, ℕ × ℕ):
  - `mulFiber_eq_mulAntidiagonal` / `addFiber_eq_antidiagonal`: fiber equals antidiagonal
  - `convolution_eq_sum_mulAntidiagonal` / `addConvolution_eq_sum_antidiagonal`:
    `tsum` reduces to `Finset.sum`
  - `ringConvolution_single_one_left/right`: identity via `Pi.single`

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

/-- The fiber of multiplication at `x`: all pairs `(a, b)` with `a * b = x`. -/
@[to_additive /-- The fiber of addition at `x`: all pairs `(a, b)` with `a + b = x`. -/]
def mulFiber (x : M) : Set (M × M) := Set.mulAntidiagonal Set.univ Set.univ x

@[to_additive (attr := grind =)]
lemma mem_mulFiber {x : M} {ab : M × M} : ab ∈ mulFiber x ↔ ab.1 * ab.2 = x := by simp [mulFiber]

@[to_additive]
lemma mulFiber_one_mem : (1, 1) ∈ mulFiber (1 : M) := by simp [mulFiber]

end Fiber

/-! ### Convolution Definition and Existence -/

section Definition

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

/-- The discrete convolution of `f` and `g` using bilinear map `L`:
`(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`. -/
@[to_additive (dont_translate := S E E' F) addConvolution
  /-- Additive convolution: `(f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1) (g ab.2)`. -/]
def convolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : M → F :=
  fun x => ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)

/-- Notation for discrete convolution with explicit bilinear map:
`(f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1) (g ab.2)`. -/
scoped notation:67 f:68 " ⋆[" L "] " g:67 => convolution L f g

/-- Notation for additive convolution with explicit bilinear map:
`(f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1) (g ab.2)`. -/
scoped notation:67 f:68 " ⋆₊[" L "] " g:67 => addConvolution L f g

end Definition

section BasicProperties

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

@[to_additive (dont_translate := S E E' F) (attr := simp) zero_addConvolution]
lemma zero_convolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E') :
    (0 : M → E) ⋆[L] f = 0 := by
  ext; simp [convolution]

@[to_additive (dont_translate := S E E' F) (attr := simp) addConvolution_zero]
lemma convolution_zero (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) :
    f ⋆[L] (0 : M → E') = 0 := by
  ext; simp [convolution]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_indicator_zero_left]
lemma convolution_indicator_one_left (L : E →ₗ[S] F →ₗ[S] F) (e : E) (f : M → F)
    (hL : ∀ y, L e y = y) :
    Set.indicator {1} (fun _ => e) ⋆[L] f = f := by
  classical
  ext x; simp only [convolution, Set.indicator_apply]
  rw [tsum_eq_single (⟨(1, x), by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_indicator_zero_right]
lemma convolution_indicator_one_right (L : F →ₗ[S] E →ₗ[S] F) (f : M → F) (e : E)
    (hL : ∀ y, L y e = y) :
    f ⋆[L] Set.indicator {1} (fun _ => e) = f := by
  classical
  ext x; simp only [convolution, Set.indicator_apply]
  rw [tsum_eq_single (⟨(x, 1), by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

end BasicProperties

section ExistenceProperties

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

variable [T2Space F] [ContinuousAdd F]

@[to_additive (dont_translate := S E E' F)]
lemma ConvolutionExistsAt.distrib_add {f : M → E} {g g' : M → E'} {x : M}
    (L : E →ₗ[S] E' →ₗ[S] F) (hfg : ConvolutionExistsAt L f g x)
    (hfg' : ConvolutionExistsAt L f g' x) :
    (f ⋆[L] (g + g')) x = (f ⋆[L] g) x + (f ⋆[L] g') x := by
  simpa [convolution] using hfg.tsum_add hfg'

@[to_additive (dont_translate := S E E' F)]
lemma ConvolutionExists.distrib_add {f : M → E} {g g' : M → E'} (L : E →ₗ[S] E' →ₗ[S] F)
    (hfg : ConvolutionExists L f g) (hfg' : ConvolutionExists L f g') :
    f ⋆[L] (g + g') = f ⋆[L] g + f ⋆[L] g' := by
  ext x; exact (hfg x).distrib_add L (hfg' x)

@[to_additive (dont_translate := S E E' F)]
lemma ConvolutionExistsAt.add_distrib {f f' : M → E} {g : M → E'} {x : M}
    (L : E →ₗ[S] E' →ₗ[S] F) (hfg : ConvolutionExistsAt L f g x)
    (hfg' : ConvolutionExistsAt L f' g x) :
    ((f + f') ⋆[L] g) x = (f ⋆[L] g) x + (f' ⋆[L] g) x := by
  simpa [convolution] using hfg.tsum_add hfg'

@[to_additive (dont_translate := S E E' F)]
lemma ConvolutionExists.add_distrib {f f' : M → E} {g : M → E'} (L : E →ₗ[S] E' →ₗ[S] F)
    (hfg : ConvolutionExists L f g) (hfg' : ConvolutionExists L f' g) :
    (f + f') ⋆[L] g = f ⋆[L] g + f' ⋆[L] g := by
  ext x; exact (hfg x).add_distrib L (hfg' x)

variable {F : Type*}
variable [AddCommMonoid F] [Module S F] [TopologicalSpace F] [ContinuousConstSMul S F] [T2Space F]

@[to_additive (dont_translate := S E E' F)]
lemma ConvolutionExistsAt.smul_convolution {c : S} {f : M → E} {g : M → E'} {x : M}
    (L : E →ₗ[S] E' →ₗ[S] F) (hfg : ConvolutionExistsAt L f g x) :
    ((c • f) ⋆[L] g) x = c • ((f ⋆[L] g) x) := by
  simpa [convolution] using hfg.tsum_const_smul c

@[to_additive (dont_translate := S E E' F)]
lemma ConvolutionExistsAt.convolution_smul {c : S} {f : M → E} {g : M → E'} {x : M}
    (L : E →ₗ[S] E' →ₗ[S] F) (hfg : ConvolutionExistsAt L f g x) :
    (f ⋆[L] (c • g)) x = c • ((f ⋆[L] g) x) := by
  simpa [convolution] using hfg.tsum_const_smul c

end ExistenceProperties

/-! ### Commutativity -/

section CommMonoid

variable [CommMonoid M] [CommSemiring S] [AddCommMonoid E] [Module S E] [TopologicalSpace E]

@[to_additive]
private def mulFiber_swapEquiv (x : M) : mulFiber x ≃ mulFiber x where
  toFun := fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mem_mulFiber, mul_comm]⟩
  invFun := fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mem_mulFiber, mul_comm]⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

@[to_additive (dont_translate := S E) addConvolution_comm]
theorem convolution_comm (L : E →ₗ[S] E →ₗ[S] E) (f g : M → E) (hL : ∀ x y, L x y = L y x) :
    f ⋆[L] g = g ⋆[L] f := by
  unfold convolution; ext x
  rw [← (mulFiber_swapEquiv x).tsum_eq]
  congr 1; funext ⟨⟨a, b⟩, _⟩; exact hL (f b) (g a)

end CommMonoid

end DiscreteConvolution

end
