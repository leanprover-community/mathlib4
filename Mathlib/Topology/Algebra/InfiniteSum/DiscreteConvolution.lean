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
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Data.Set.MulAntidiagonal
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Discrete Convolution

Discrete convolution over monoids: `(f ⋆[L] g) x` is the sum of `L (f a) (g b)` over all
pairs `(a, b)` with `a * b = x`, that is, over `mulFiber x`. Additive monoids are also
supported.

## Design

Uses a bilinear map `L : E →ₗ[S] E' →ₗ[S] F` to combine values, following
`MeasureTheory.convolution`.

The index monoid `M` can be non-commutative (group algebras R[G] with non-abelian G).

`@[to_additive]` generates multiplicative and additive versions from a single definition.
The `mul/add` distinction refers to the index monoid `M`: multiplicative sums over
`mulFiber x = {(a,b) | a * b = x}`, additive sums over `addFiber x = {(a,b) | a + b = x}`.

## Main Definitions

* `mulFiber x`: the fiber of multiplication at `x`, all pairs `(a, b)` with `a * b = x`.
* `convolution L f g`: the discrete convolution
  `(f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)`.
* `ringConvolution f g`: convolution using multiplication to combine the values of `f` and `g`.
* `ConvolutionExistsAt L f g x`: the family indexed by `mulFiber x` is summable.
* `ConvolutionExists L f g`: `ConvolutionExistsAt L f g x` holds for every `x`.

## Main Results

* `single_convolution`, `convolution_single`: identity element
  (`Pi.single 1 e` where `L e` is the identity map)
* `ConvolutionExists.distrib_add`, `ConvolutionExists.add_distrib`: distributivity over addition
* `ConvolutionExistsAt.smul_convolution`, `ConvolutionExistsAt.convolution_smul`:
  scalar multiplication
* `convolution_comm`: commutativity for symmetric bilinear maps over commutative monoids
* `convolution_eq_sum_mulAntidiagonal`: finite-sum formula when the index monoid has
  `Finset.HasMulAntidiagonal`
* `single_ringConvolution`, `ringConvolution_single`: identity laws for multiplication convolution
* `ringConvolution_add`, `add_ringConvolution`: distributivity over addition
* `smul_ringConvolution`, `ringConvolution_smul`: external scalar multiplication
* `ringConvolution_comm`: commutativity when both the indices and values are commutative

## Notation

| Notation     | Operation                                       |
|--------------|-------------------------------------------------|
| `f ⋆[L] g`   | `∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)`   |
| `f ⋆₊[L] g`  | `∑' ab : addFiber x, L (f ab.1.1) (g ab.1.2)`   |
| `f ⋆ᵣ g`     | `ringConvolution f g`                           |
| `f ⋆ᵣ₊ g`    | `addRingConvolution f g`                        |

Precedence design: `f:68` and `g:67` gives right associativity (`f ⋆ g ⋆ h` parses as
`f ⋆ (g ⋆ h)`), matching function composition `∘` and `MeasureTheory.convolution`.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace DiscreteConvolution

variable {M S E E' F F' R : Type*}

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

/-- The discrete convolution of `f` and `g` using bilinear map `L`: the value at `x` is the
sum of `L (f a) (g b)` over all pairs `(a, b)` with `a * b = x`. -/
@[to_additive (dont_translate := S E E' F) addConvolution
  /-- Additive convolution: the value at `x` is the sum of `L (f a) (g b)` over all pairs
  `(a, b)` with `a + b = x`. -/]
def convolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : M → F :=
  fun x => ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)

/-- Notation for discrete convolution with explicit bilinear map:
`(f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)`. -/
scoped notation:67 f:68 " ⋆[" L "] " g:67 => convolution L f g

/-- Notation for additive convolution with explicit bilinear map:
`(f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1.1) (g ab.1.2)`. -/
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

@[to_additive (dont_translate := S E F) (attr := simp) single_addConvolution]
lemma single_convolution [DecidableEq M] (L : E →ₗ[S] F →ₗ[S] F) (e : E) (f : M → F)
    (hL : ∀ y, L e y = y) :
    Pi.single 1 e ⋆[L] f = f := by
  ext x; simp only [convolution, Pi.single_apply]
  rw [tsum_eq_single (⟨(1, x), by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_single]
lemma convolution_single [DecidableEq M] (L : F →ₗ[S] E →ₗ[S] F) (e : E) (f : M → F)
    (hL : ∀ y, L y e = y) :
    f ⋆[L] Pi.single 1 e = f := by
  ext x; simp only [convolution, Pi.single_apply]
  rw [tsum_eq_single (⟨(x, 1), by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

end BasicProperties

section ExistenceProperties

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

/-- The convolution of `f` and `g` with bilinear map `L` exists at `x`: the family
`ab ↦ L (f ab.1.1) (g ab.1.2)` indexed by `mulFiber x` is summable. -/
@[to_additive (dont_translate := S E E' F) AddConvolutionExistsAt
  /-- The additive convolution of `f` and `g` with bilinear map `L` exists at `x`: the family
  `ab ↦ L (f ab.1.1) (g ab.1.2)` indexed by `addFiber x` is summable. -/]
def ConvolutionExistsAt (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) : Prop :=
  Summable fun ab : mulFiber x => L (f ab.1.1) (g ab.1.2)

/-- The convolution of `f` and `g` with bilinear map `L` exists at every point, that is,
`ConvolutionExistsAt L f g x` holds for every `x`.

This does not assert that the resulting function `convolution L f g` is summable over `M`. -/
@[to_additive (dont_translate := S E E' F) AddConvolutionExists
  /-- The additive convolution of `f` and `g` with bilinear map `L` exists at every point, that
  is, `AddConvolutionExistsAt L f g x` holds for every `x`.

  This does not assert that the resulting function `addConvolution L f g` is summable over `M`. -/]
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

/-! ### Finite Multiplication Fibers -/

section HasMulAntidiagonal

variable [Monoid M] [Finset.HasMulAntidiagonal M]

@[to_additive]
private lemma mulFiber_eq_mulAntidiagonal (x : M) :
    mulFiber x = ↑(Finset.mulAntidiagonal x) := by
  ext ab
  simp only [Finset.mem_coe, Finset.mem_mulAntidiagonal, mem_mulFiber]

/-- Multiplication fibers are finite when the index monoid has `Finset.HasMulAntidiagonal`. -/
@[to_additive
  /-- Addition fibers are finite when the index monoid has `Finset.HasAntidiagonal`. -/]
lemma mulFiber_finite (x : M) : (mulFiber x).Finite := by
  rw [mulFiber_eq_mulAntidiagonal]
  exact Finset.finite_toSet _

variable [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F] [TopologicalSpace F]

/-- Convolution is a finite sum when the index monoid has `Finset.HasMulAntidiagonal`. -/
@[to_additive (dont_translate := S E E' F) addConvolution_eq_sum_antidiagonal
  /-- Additive convolution is a finite sum when the index monoid has
  `Finset.HasAntidiagonal`. -/]
lemma convolution_eq_sum_mulAntidiagonal
    (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆[L] g) x = ∑ ab ∈ Finset.mulAntidiagonal x, L (f ab.1) (g ab.2) := by
  rw [convolution, ← Finset.tsum_subtype]
  exact (Set.equivOfEq (mulFiber_eq_mulAntidiagonal x)).tsum_eq
    (fun ab => L (f ab.1.1) (g ab.1.2))

/-- Convolution exists whenever the index monoid has `Finset.HasMulAntidiagonal`, since every
fiber is then finite. -/
@[to_additive (dont_translate := S E E' F) addConvolutionExists_of_hasAntidiagonal
  /-- Additive convolution exists whenever the index monoid has `Finset.HasAntidiagonal`, since
  every fiber is then finite. -/]
lemma convolutionExists_of_hasMulAntidiagonal
    (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') :
    ConvolutionExists L f g := fun x ↦ by
  simpa only [ConvolutionExistsAt, Function.comp_def] using
    (mulFiber_finite x).summable (fun ab : M × M => L (f ab.1) (g ab.2))

end HasMulAntidiagonal

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

/-! ### Convolution with Multiplication -/

section RingConvolution

variable [NonUnitalNonAssocSemiring R]

variable [Monoid M] [TopologicalSpace R]

/-- The discrete convolution of two functions using multiplication to combine their values. -/
@[to_additive (dont_translate := R) addRingConvolution
  /-- The additive-index convolution using multiplication to combine values. -/]
def ringConvolution (f g : M → R) : M → R :=
  convolution (.mul ℕ R) f g

/-- Notation for convolution using multiplication to combine values. -/
scoped notation:67 f:68 " ⋆ᵣ " g:67 => ringConvolution f g

/-- Notation for additive-index convolution using multiplication to combine values. -/
scoped notation:67 f:68 " ⋆ᵣ₊ " g:67 => addRingConvolution f g

@[to_additive (dont_translate := R) (attr := simp) addRingConvolution_apply]
lemma ringConvolution_apply (f g : M → R) (x : M) :
    (f ⋆ᵣ g) x = ∑' ab : mulFiber x, f ab.1.1 * g ab.1.2 := rfl

@[to_additive (dont_translate := R) (attr := simp) zero_addRingConvolution]
lemma zero_ringConvolution (f : M → R) :
    (0 : M → R) ⋆ᵣ f = 0 := by
  simpa only [ringConvolution] using zero_convolution (.mul ℕ R) f

@[to_additive (dont_translate := R) (attr := simp) addRingConvolution_zero]
lemma ringConvolution_zero (f : M → R) :
    f ⋆ᵣ (0 : M → R) = 0 := by
  simpa only [ringConvolution] using convolution_zero (.mul ℕ R) f

end RingConvolution

section RingConvolutionIdentity

variable [Monoid M] [NonAssocSemiring R] [TopologicalSpace R]

@[to_additive (dont_translate := R) (attr := simp) single_addRingConvolution]
lemma single_ringConvolution [DecidableEq M] (f : M → R) :
    (Pi.single 1 1) ⋆ᵣ f = f := by
  simpa only [ringConvolution] using single_convolution (.mul ℕ R) 1 f (by simp)

@[to_additive (dont_translate := R) (attr := simp) addRingConvolution_single]
lemma ringConvolution_single [DecidableEq M] (f : M → R) :
    f ⋆ᵣ (Pi.single 1 1) = f := by
  simpa only [ringConvolution] using convolution_single (.mul ℕ R) 1 f (by simp)

end RingConvolutionIdentity

section RingConvolutionDistributivity

variable [Monoid M] [NonUnitalNonAssocSemiring R]
variable [TopologicalSpace R] [T2Space R] [ContinuousAdd R]

@[to_additive (dont_translate := R) addRingConvolution_add]
lemma ringConvolution_add (f g h : M → R)
    (hfg : ConvolutionExists (.mul ℕ R) f g) (hfh : ConvolutionExists (.mul ℕ R) f h) :
    f ⋆ᵣ (g + h) = f ⋆ᵣ g + f ⋆ᵣ h := by
  simpa only [ringConvolution] using hfg.distrib_add (.mul ℕ R) hfh

@[to_additive (dont_translate := R) add_addRingConvolution]
lemma add_ringConvolution (f g h : M → R)
    (hfh : ConvolutionExists (.mul ℕ R) f h) (hgh : ConvolutionExists (.mul ℕ R) g h) :
    (f + g) ⋆ᵣ h = f ⋆ᵣ h + g ⋆ᵣ h := by
  simpa only [ringConvolution] using hfh.add_distrib (.mul ℕ R) hgh

end RingConvolutionDistributivity

section RingConvolutionScalar

variable [Monoid M] [NonUnitalNonAssocSemiring R] [DistribSMul S R]
variable [TopologicalSpace R] [T2Space R] [ContinuousConstSMul S R]

/-- External scalar multiplication in the first factor commutes with convolution. -/
@[to_additive (dont_translate := S R) smul_addRingConvolution]
lemma smul_ringConvolution [IsScalarTower S R R] (c : S) (f g : M → R)
    (hfg : ConvolutionExists (.mul ℕ R) f g) :
    (c • f) ⋆ᵣ g = c • (f ⋆ᵣ g) := by
  ext; simpa [smul_mul_assoc] using (hfg _).tsum_const_smul c

/-- External scalar multiplication in the second factor commutes with convolution. -/
@[to_additive (dont_translate := S R) addRingConvolution_smul]
lemma ringConvolution_smul [SMulCommClass S R R] (c : S) (f g : M → R)
    (hfg : ConvolutionExists (.mul ℕ R) f g) :
    f ⋆ᵣ (c • g) = c • (f ⋆ᵣ g) := by
  ext; simpa [mul_smul_comm] using (hfg _).tsum_const_smul c

end RingConvolutionScalar

section RingConvolutionCommutativity

variable [CommMonoid M] [NonUnitalNonAssocCommSemiring R] [TopologicalSpace R]

@[to_additive (dont_translate := R) addRingConvolution_comm]
lemma ringConvolution_comm (f g : M → R) :
    f ⋆ᵣ g = g ⋆ᵣ f := by
  simpa only [ringConvolution] using convolution_comm (.mul ℕ R) f g (by simp [mul_comm])

end RingConvolutionCommutativity

section RingConvolutionFinite

variable [Monoid M] [NonUnitalNonAssocSemiring R] [TopologicalSpace R]
variable [Finset.HasMulAntidiagonal M]

/-- Multiplication convolution as a finite sum over the mulAntidiagonal. -/
@[to_additive (dont_translate := R) addRingConvolution_eq_sum_antidiagonal
  /-- Additive-index multiplication convolution as a finite sum over the antidiagonal. -/]
lemma ringConvolution_eq_sum_mulAntidiagonal (f g : M → R) (x : M) :
    (f ⋆ᵣ g) x = ∑ ab ∈ Finset.mulAntidiagonal x, f ab.1 * g ab.2 := by
  simpa [ringConvolution] using convolution_eq_sum_mulAntidiagonal (.mul ℕ R) f g x

end RingConvolutionFinite

end DiscreteConvolution

end
