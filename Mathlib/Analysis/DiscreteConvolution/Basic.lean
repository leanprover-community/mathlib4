/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.Set.MulAntidiagonal

/-!
# Discrete Convolution

Discrete convolution of `f : M → E` and `g : M → E'` over a monoid `M`:
`(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)` where `mulFiber x = {(a, b) | a * b = x}`.

## Main Definitions

* `mulFiber x`: the set `{(a, b) | a * b = x}`, an abbreviation for `Set.mulAntidiagonal`
* `tripleFiber x`: the set `{(a, b, c) | a * b * c = x}`
* `leftAssocEquiv`: equivalence `(Σ cd : mulFiber x, mulFiber cd.1.1) ≃ tripleFiber x`
* `rightAssocEquiv`: equivalence `(Σ ae : mulFiber x, mulFiber ae.1.2) ≃ tripleFiber x`
* `convolution L f g`: convolution `f ⋆[L] g`
* `mulConvolution f g`: ring multiplication convolution `f ⋆ₘ g`
* `delta e`: identity element for convolution

## Notation

* `f ⋆[L] g`, `f ⋆₊[L] g`: convolution with bilinear map `L`
* `f ⋆ₘ g`, `f ⋆₊ₘ g`: ring multiplication convolution
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

@[to_additive (attr := simp)]
theorem mem_mulFiber {x : M} {ab : M × M} : ab ∈ mulFiber x ↔ ab.1 * ab.2 = x := by simp

@[to_additive]
theorem mulFiber_one_mem : (1, 1) ∈ mulFiber (1 : M) := by simp

end Fiber

/-! ### Triple Fiber and Associativity Equivalences -/

section TripleFiber

variable [Monoid M]

/-- Fiber over `x` under triple multiplication: `{(a, b, c) | a * b * c = x}`. -/
@[to_additive tripleAddFiber
  /-- Fiber over `x` under triple addition: `{(a, b, c) | a + b + c = x}`. -/]
def tripleFiber (x : M) : Set (M × M × M) := {abc | abc.1 * abc.2.1 * abc.2.2 = x}

@[to_additive (attr := simp) mem_tripleAddFiber]
theorem mem_tripleFiber {x : M} {abc : M × M × M} :
    abc ∈ tripleFiber x ↔ abc.1 * abc.2.1 * abc.2.2 = x := Iff.rfl

/-- Left association equivalence for associativity proof.
Maps `((c, d), (a, b))` where `c * d = x` and `a * b = c` to `(a, b, d)` where `a * b * d = x`.
This identifies the nested sum `∑' (cd : mulFiber x), ∑' (ab : mulFiber cd.1.1), f a * g b * h d`
with a sum over the triple fiber. -/
@[to_additive leftAddAssocEquiv /-- Left association equivalence for additive associativity. -/]
def leftAssocEquiv (x : M) : (Σ cd : mulFiber x, mulFiber cd.1.1) ≃ tripleFiber x where
  toFun := fun ⟨⟨⟨c, d⟩, hcd⟩, ⟨⟨a, b⟩, hab⟩⟩ =>
    ⟨⟨a, b, d⟩, by rw [mem_tripleFiber]; rw [mem_mulFiber] at hcd hab; rw [← hcd, ← hab, mul_assoc]⟩
  invFun := fun ⟨⟨a, b, d⟩, habd⟩ =>
    ⟨⟨⟨a * b, d⟩, by rw [mem_mulFiber]; rw [mem_tripleFiber] at habd; exact habd⟩,
     ⟨⟨a, b⟩, by rw [mem_mulFiber]⟩⟩
  left_inv := fun ⟨⟨⟨c, d⟩, hcd⟩, ⟨⟨a, b⟩, hab⟩⟩ => by
    simp only [mem_mulFiber] at hab; subst hab; rfl
  right_inv := fun ⟨⟨a, b, d⟩, habd⟩ => rfl

/-- Right association equivalence for associativity proof.
Maps `((a, e), (b, d))` where `a * e = x` and `b * d = e` to `(a, b, d)` where `a * b * d = x`.
This identifies the nested sum `∑' (ae : mulFiber x), ∑' (bd : mulFiber ae.1.2), f a * g b * h d`
with a sum over the triple fiber. -/
@[to_additive rightAddAssocEquiv /-- Right association equivalence for additive associativity. -/]
def rightAssocEquiv (x : M) : (Σ ae : mulFiber x, mulFiber ae.1.2) ≃ tripleFiber x where
  toFun := fun ⟨⟨⟨a, e⟩, hae⟩, ⟨⟨b, d⟩, hbd⟩⟩ =>
    ⟨⟨a, b, d⟩, by rw [mem_tripleFiber]; rw [mem_mulFiber] at hae hbd; rw [← hae, ← hbd, mul_assoc]⟩
  invFun := fun ⟨⟨a, b, d⟩, habd⟩ =>
    ⟨⟨⟨a, b * d⟩, by rw [mem_mulFiber]; rw [mem_tripleFiber] at habd; rw [← mul_assoc]; exact habd⟩,
     ⟨⟨b, d⟩, by rw [mem_mulFiber]⟩⟩
  left_inv := fun ⟨⟨⟨a, e⟩, hae⟩, ⟨⟨b, d⟩, hbd⟩⟩ => by
    simp only [mem_mulFiber] at hbd; subst hbd; rfl
  right_inv := fun ⟨⟨a, b, d⟩, habd⟩ => rfl

end TripleFiber

/-! ### Convolution Definition -/

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

/-- Notation for discrete convolution with explicit bilinear map. -/
scoped notation:70 f:70 " ⋆[" L:70 "] " g:71 => convolution L f g

/-- Notation for additive convolution. -/
scoped notation:70 f:70 " ⋆₊[" L "] " g:71 => addConvolution L f g

@[to_additive (attr := simp) (dont_translate := S E E' F) addConvolution_apply]
theorem convolution_apply (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2) := rfl

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

end Definition

/-! ### Ring Multiplication Specialization -/

section RingMul

variable [Monoid M] {R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- Convolution using ring multiplication. This is `convolution (LinearMap.mul R R)`. -/
@[to_additive (dont_translate := R) addMulConvolution
  /-- Additive convolution using ring multiplication. -/]
def mulConvolution (f g : M → R) : M → R := convolution (LinearMap.mul R R) f g

/-- Notation for ring multiplication convolution. -/
scoped notation:70 f:70 " ⋆ₘ " g:71 => mulConvolution f g

/-- Notation for additive ring multiplication convolution. -/
scoped notation:70 f:70 " ⋆₊ₘ " g:71 => addMulConvolution f g

@[to_additive (dont_translate := R) addMulConvolution_apply]
theorem mulConvolution_apply (f g : M → R) (x : M) :
    (f ⋆ₘ g) x = ∑' ab : mulFiber x, f ab.1.1 * g ab.1.2 := rfl

@[to_additive (attr := simp) (dont_translate := R) zero_addMulConvolution]
theorem zero_mulConvolution (f : M → R) : (0 : M → R) ⋆ₘ f = 0 := by
  ext x; simp only [mulConvolution_apply, Pi.zero_apply, zero_mul, tsum_zero]

@[to_additive (attr := simp) (dont_translate := R) addMulConvolution_zero]
theorem mulConvolution_zero (f : M → R) : f ⋆ₘ (0 : M → R) = 0 := by
  ext x; simp only [mulConvolution_apply, Pi.zero_apply, mul_zero, tsum_zero]

end RingMul

/-! ### Identity Element -/

section Identity

variable [Monoid M] [DecidableEq M] [Semiring S] [AddCommMonoid E] [Module S E]

/-- The identity for convolution: `δ₁(x) = e` if `x = 1`, else `0`. -/
@[to_additive addDelta /-- The identity for additive convolution: `δ₀(x) = e` if `x = 0`,
else `0`. -/]
def delta (e : E) : M → E := Pi.single 1 e

@[to_additive (attr := simp) addDelta_zero]
theorem delta_one (e : E) : delta e 1 = e := rfl

@[to_additive addDelta_ne]
theorem delta_ne (e : E) {x : M} (hx : x ≠ 1) : delta e x = 0 :=
  Pi.single_eq_of_ne (M := fun _ => E) hx e

end Identity

/-! ### Commutativity -/

section Commutative

variable [CommMonoid M] [CommSemiring S] [AddCommMonoid E] [Module S E] [TopologicalSpace E]

/-- Commutativity for symmetric bilinear maps on commutative monoids. -/
@[to_additive (dont_translate := S E) addConvolution_comm]
theorem convolution_comm (L : E →ₗ[S] E →ₗ[S] E) (f g : M → E) (hL : ∀ x y, L x y = L y x) :
    f ⋆[L] g = g ⋆[L] f := by
  ext x
  simp only [convolution_apply]
  let e : mulFiber x ≃ mulFiber x :=
    ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨⟨b, a⟩, by simp_all [Set.mem_mulAntidiagonal, mul_comm]⟩,
     fun ⟨⟨a, b⟩, h⟩ => ⟨⟨b, a⟩, by simp_all [Set.mem_mulAntidiagonal, mul_comm]⟩,
     fun _ => by rfl, fun _ => by rfl⟩
  rw [← e.tsum_eq]; congr 1; funext ⟨⟨a, b⟩, _⟩; simp only [e, Equiv.coe_fn_mk, hL]

end Commutative

section MulConvolutionComm

variable [CommMonoid M] {R : Type*} [CommSemiring R] [TopologicalSpace R]

@[to_additive (dont_translate := R) addMulConvolution_comm]
theorem mulConvolution_comm (f g : M → R) : f ⋆ₘ g = g ⋆ₘ f :=
  convolution_comm (LinearMap.mul R R) f g (fun x y => mul_comm x y)

end MulConvolutionComm

end DiscreteConvolution

end
