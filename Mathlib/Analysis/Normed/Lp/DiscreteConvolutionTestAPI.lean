/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Discrete Convolution of Functions

This file defines the discrete convolution on two functions `f g : M → R` where `M` is a monoid:

  `(f ⋆ g) x = ∑' (a, b) : mulFiber x, f a * g b`

where `mulFiber x = {(a, b) | a * b = x}` is the fiber of the multiplication map.

This is analogous to `MeasureTheory.convolution` but for the discrete (counting measure) setting.
The measure-theoretic convolution uses `(f ⋆ g) x = ∫ t, f(t) * g(x - t) ∂μ` which requires
a group structure for subtraction; our definition sums over multiplicative fibers and works
for `[Monoid M]`.

## Main Definitions

* `DiscreteConvolution.mulFiber x`: the set `{(a, b) | a * b = x}`
* `DiscreteConvolution.ConvolutionExistsAt f g x`: the convolution sum converges at `x`
* `DiscreteConvolution.ConvolutionExists f g`: the convolution exists everywhere
* `DiscreteConvolution.convolution f g`: the convolution `f ⋆ g`
* `DiscreteConvolution.delta`: the identity element `δ₁` for convolution

## Main Results

### Algebraic Properties
* `DiscreteConvolution.convolution_assoc`: associativity `(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)`
* `DiscreteConvolution.delta_convolution`: left identity `δ₁ ⋆ f = f`
* `DiscreteConvolution.convolution_delta`: right identity `f ⋆ δ₁ = f`
* `DiscreteConvolution.convolution_comm`: commutativity for `[CommMonoid M] [CommSemiring R]`

### Banach Algebra Structure for ℓ¹(M, R)
* `DiscreteConvolution.lp.one_convolution_memℓp`: ℓ¹ is closed under convolution
* `DiscreteConvolution.lp.one_norm_mul_le`: submultiplicativity `‖f ⋆ g‖₁ ≤ ‖f‖₁ · ‖g‖₁`
* `DiscreteConvolution.lp.one_delta_memℓp`: the identity `δ₁` is in ℓ¹

## Design Notes

The associativity proof uses fiber equivalences `leftAssocEquiv` and `rightAssocEquiv` to
identify nested sums with sums over the triple fiber `{(a, b, d) | a * b * d = x}`. This
avoids explicit manipulation of indices and leverages `Equiv.tsum_eq` for reindexing.

For types with `HasAntidiagonal` (e.g., `ℕ`, `ℕ × ℕ`), the fiber `mulFiber x` is finite
and the `tsum` reduces to a finite sum. This connects to the formulation in polynomial
ring convolutions.

## Notation

* `f ⋆ g` for discrete convolution (scoped in `DiscreteConvolution`)

## References

* Analogous to `MeasureTheory.convolution` but for discrete sums
* Used for Banach algebra structure on ℓ¹ spaces

## TODO

* Connection to `HasAntidiagonal` for finite fibers
* Convolution with measures (generalization?)
* Ring/algebra instances for `lp (fun _ : M => R) 1`
-/

@[expose] public section

open scoped BigOperators NNReal ENNReal
open Finset

noncomputable section

namespace DiscreteConvolution

variable {M : Type*} {R : Type*}

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

variable [Monoid M] [Semiring R] [TopologicalSpace R]

/-- The convolution of `f` and `g` exists at `x` when the sum over the fiber is summable. -/
def ConvolutionExistsAt (f g : M → R) (x : M) : Prop :=
  Summable fun ab : mulFiber x => f ab.1.1 * g ab.1.2

/-- The convolution of `f` and `g` exists when it exists at every point. -/
def ConvolutionExists (f g : M → R) : Prop :=
  ∀ x, ConvolutionExistsAt f g x

end Existence

/-! ### Convolution Definition -/

section Definition

variable [Monoid M] [Semiring R] [TopologicalSpace R]

/-- The discrete convolution of `f` and `g`:
`(f ⋆ g) x = ∑' (a, b) : mulFiber x, f a * g b`. -/
def convolution (f g : M → R) : M → R :=
  fun x => ∑' ab : mulFiber x, f ab.1.1 * g ab.1.2

/-- Notation for discrete convolution. -/
scoped notation:70 f:70 " ⋆ " g:71 => convolution f g

@[simp]
theorem convolution_apply (f g : M → R) (x : M) :
    (f ⋆ g) x = ∑' ab : mulFiber x, f ab.1.1 * g ab.1.2 := rfl

end Definition

/-! ### Identity Element -/

section Identity

variable [Monoid M] [DecidableEq M] [Semiring R]

/-- The identity for convolution: `δ₁(x) = 1` if `x = 1`, else `0`. -/
def delta : M → R := Pi.single 1 1

@[simp]
theorem delta_one : (delta : M → R) 1 = 1 := Pi.single_eq_same 1 1

theorem delta_ne {x : M} (hx : x ≠ 1) : (delta : M → R) x = 0 := Pi.single_eq_of_ne hx 1

end Identity

/-! ### Banach Algebra Structure for ℓ¹(M, R)

The following lemmas specialize the general `lp` API to `p = 1`:
* `lp.one_summable_norm` is `Memℓp.summable` with `p = 1`
* `lp.one_norm_eq_tsum` is `lp.norm_eq_tsum_rpow` with `p = 1`

The lemma `lp.one_summable_norm_mul` (product summability over `M × M`) is new;
the existing `lp.summable_mul` handles Hölder conjugates, not two ℓ¹ functions. -/

section LpOneSummability

variable [NormedRing R]

/-- ℓ¹ membership gives summable norms.

This is `Memℓp.summable` specialized to `p = 1`. -/
theorem lp.one_summable_norm (f : lp (fun _ : M => R) 1) : Summable (fun m => ‖f m‖) := by
  have hf := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)] at hf
  simpa using hf

/-- The ℓ¹ norm equals the sum of norms.

This is `lp.norm_eq_tsum_rpow` specialized to `p = 1`. -/
theorem lp.one_norm_eq_tsum (f : lp (fun _ : M => R) 1) :
    ‖f‖ = ∑' m, ‖f m‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]

/-- Product of ℓ¹ norms is summable over M × M.

This is used for convolution bounds. Note: `lp.summable_mul` handles Hölder conjugates
(1/p + 1/q = 1), not two ℓ¹ functions. -/
theorem lp.one_summable_norm_mul (f g : lp (fun _ : M => R) 1) :
    Summable (fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖) :=
  (lp.one_summable_norm f).mul_of_nonneg (lp.one_summable_norm g)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

end LpOneSummability

section LpOneMembership

variable [Monoid M] [NormedRing R]

/-- The convolution of ℓ¹ functions is in ℓ¹. -/
theorem lp.one_convolution_memℓp (f g : lp (fun _ : M => R) 1) :
    Memℓp (convolution (⇑f) (⇑g)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have hprod := lp.one_summable_norm_mul f g
  have hfiber : ∀ x, Summable fun ab : mulFiber x => ‖f ab.1.1‖ * ‖g ab.1.2‖ :=
    fun x => hprod.subtype _
  have hbound :
      ∀ x, ‖(convolution (⇑f) (⇑g)) x‖ ≤
        ∑' ab : mulFiber x, ‖f ab.1.1‖ * ‖g ab.1.2‖ := by
    intro x
    have hx := hfiber x
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ab => norm_mul_le _ _) hx
    · exact Summable.tsum_le_tsum (fun ab => norm_mul_le _ _)
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ab => norm_mul_le _ _) hx) hx
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact ((Equiv.sigmaFiberEquiv mulMap).summable_iff.mpr hprod).sigma

/-- Cauchy product multiplication on ℓ¹. -/
def lp.oneMul (f g : lp (fun _ : M => R) 1) : lp (fun _ : M => R) 1 :=
  ⟨convolution (⇑f) (⇑g), lp.one_convolution_memℓp f g⟩

/-- The identity element δ₁ is in ℓ¹. -/
theorem lp.one_delta_memℓp [DecidableEq M] : Memℓp (delta : M → R) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have h : (fun m => ‖(delta : M → R) m‖) = fun m => if m = 1 then ‖(1 : R)‖ else 0 := by
    ext m; simp only [delta, Pi.single_apply]
    split_ifs <;> simp
  rw [h]
  exact summable_of_ne_finset_zero (s := {1})
    (by simp_all only [Finset.mem_singleton, ↓reduceIte, implies_true])

/-- Identity element for ℓ¹ convolution algebra. -/
def lp.oneOne [DecidableEq M] : lp (fun _ : M => R) 1 :=
  ⟨delta, lp.one_delta_memℓp⟩

/-- Submultiplicativity of the ℓ¹ norm under convolution: `‖f ⋆ g‖₁ ≤ ‖f‖₁ · ‖g‖₁`.

This is the key inequality for the Banach algebra structure on ℓ¹(M, R).

Strategy: Use fiber partition `M × M ≃ Σ x, mulFiber x` to relate
`∑' ab, ‖f ab.1‖ * ‖g ab.2‖` to `∑' x, ∑' (ab : mulFiber x), ...`. -/
theorem lp.one_norm_mul_le (f g : lp (fun _ : M => R) 1) :
    ‖lp.oneMul f g‖ ≤ ‖f‖ * ‖g‖ := by
  simp only [lp.one_norm_eq_tsum]
  have hprod := lp.one_summable_norm_mul f g
  -- Transport summability across fiber equivalence
  have hsigma : Summable fun p : Σ x, mulFiber x => ‖f p.2.1.1‖ * ‖g p.2.1.2‖ :=
    (Equiv.sigmaFiberEquiv mulMap).summable_iff.mpr hprod
  have h1 : ∀ m, Summable fun ab : mulFiber m => ‖(f : M → R) ab.1.1‖ * ‖g ab.1.2‖ :=
    fun m => hprod.subtype _
  -- Pointwise bound: ‖(f ⋆ g) x‖ ≤ ∑' (ab : mulFiber x), ‖f ab.1.1‖ * ‖g ab.1.2‖
  have hbound : ∀ x, ‖(lp.oneMul f g) x‖ ≤ ∑' ab : mulFiber x, ‖f ab.1.1‖ * ‖g ab.1.2‖ := fun x =>
    (norm_tsum_le_tsum_norm (Summable.of_norm_bounded (h1 x)
      (fun _ => by simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_mul_le _ _))).trans
    (Summable.tsum_le_tsum (fun _ => norm_mul_le _ _)
      (Summable.of_norm_bounded (h1 x)
        (fun _ =>
          by simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_mul_le _ _)) (h1 x))
  -- Fubini: ∑' (p : Σ x, mulFiber x), ... = ∑' x, ∑' (ab : mulFiber x), ...
  have h2 : ∑' (p : Σ x, mulFiber x), ‖f p.2.1.1‖ * ‖g p.2.1.2‖ =
      ∑' x, ∑' ab : mulFiber x, ‖f ab.1.1‖ * ‖g ab.1.2‖ := hsigma.tsum_sigma' h1
  refine (Summable.tsum_le_tsum hbound (lp.one_summable_norm _) hsigma.sigma).trans (le_of_eq ?_)
  -- Chain equalities via ▸ (avoids rw timeout issues with tsum_sigma')
  exact (lp.one_summable_norm f).tsum_mul_tsum (lp.one_summable_norm g) hprod ▸
    h2.symm.trans ((Equiv.sigmaFiberEquiv mulMap).tsum_eq (fun ab => ‖(f : M → R) ab.1‖ * ‖g ab.2‖))

end LpOneMembership

section LpOneComplete

/-! Properties requiring completeness of the codomain.

The `CompleteSpace R` assumption aligns with `MeasureTheory.convolution`, which requires
`CompleteSpace F` for results like `convolution_assoc`. This is necessary because absolute
convergence of a series implies convergence only in complete spaces. -/

variable [Monoid M] [NormedRing R] [CompleteSpace R]

/-- The convolution exists for ℓ¹ functions. -/
theorem lp.convolutionExists (f g : lp (fun _ : M => R) 1) :
    ConvolutionExists (⇑f) (⇑g) := fun x =>
  Summable.of_norm_bounded ((lp.one_summable_norm_mul f g).subtype (mulFiber x))
    (fun _ => norm_mul_le _ _)

end LpOneComplete

/-! ### Algebraic Properties -/

section Algebraic

variable [Monoid M] [Semiring R] [TopologicalSpace R] [T3Space R] [IsTopologicalSemiring R]

/-! #### Triple Fiber for Associativity -/

/-- Triple multiplication map. -/
def tripleMulMap : M × M × M → M := fun ⟨a, b, d⟩ => a * b * d

/-- Fiber over x under triple multiplication. -/
def tripleFiber (x : M) : Set (M × M × M) := tripleMulMap ⁻¹' {x}

/-- Left association equivalence for associativity proof.

Maps `((c, d), (a, b))` where `c * d = x` and `a * b = c` to `(a, b, d)` where `a * b * d = x`.
This identifies the nested sum `∑' (cd : mulFiber x), ∑' (ab : mulFiber cd.1.1), f a * g b * h d`
with a sum over the triple fiber. -/
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

/-- Summability over triple fiber for associativity. -/
def tripleConvolutionExistsAt (f g h : M → R) (x : M) : Prop :=
  Summable fun p : tripleFiber x => f p.1.1 * g p.1.2.1 * h p.1.2.2

/-- Left-associated convolution sum as a triple fiber sum. -/
theorem convolution_assoc_left_sum (f g h : M → R)
    (hfg : ConvolutionExists f g) (htriple : ∀ x, tripleConvolutionExistsAt f g h x) (x : M) :
    ∑' cd : mulFiber x, (∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2) * h cd.1.2 =
      ∑' p : tripleFiber x, f p.1.1 * g p.1.2.1 * h p.1.2.2 := by
  -- Step 1: Distribute h into inner sum
  have h1 : ∑' cd : mulFiber x, (∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2) * h cd.1.2 =
      ∑' cd : mulFiber x, ∑' ab : mulFiber cd.1.1, (f ab.1.1 * g ab.1.2) * h cd.1.2 := by
    congr 1; ext cd; exact ((hfg cd.1.1).tsum_mul_right (h cd.1.2)).symm
  -- Step 2: Summability
  have hsigmaL : Summable fun p : Σ cd : mulFiber x, mulFiber cd.1.1 =>
      (f p.2.1.1 * g p.2.1.2) * h p.1.1.2 := by
    convert (leftAssocEquiv x).summable_iff.mpr (htriple x) using 1
  have hfiberL : ∀ cd : mulFiber x, Summable fun ab : mulFiber cd.1.1 =>
      (f ab.1.1 * g ab.1.2) * h cd.1.2 := fun cd => (hfg cd.1.1).mul_right (h cd.1.2)
  -- Step 3: Equivalence tsum
  have h2 := (leftAssocEquiv x).tsum_eq (fun p => f p.1.1 * g p.1.2.1 * h p.1.2.2)
  -- Step 4: Fubini
  have h3 : ∑' (p : Σ cd : mulFiber x, mulFiber cd.1.1), (f p.2.1.1 * g p.2.1.2) * h p.1.1.2 =
      ∑' cd : mulFiber x, ∑' ab : mulFiber cd.1.1, (f ab.1.1 * g ab.1.2) * h cd.1.2 :=
    hsigmaL.tsum_sigma' hfiberL
  rw [h1, ← h2, ← h3]; rfl

/-- Right-associated convolution sum as a triple fiber sum. -/
theorem convolution_assoc_right_sum (f g h : M → R)
    (hgh : ConvolutionExists g h) (htriple : ∀ x, tripleConvolutionExistsAt f g h x) (x : M) :
    ∑' ae : mulFiber x, f ae.1.1 * (∑' bd : mulFiber ae.1.2, g bd.1.1 * h bd.1.2) =
      ∑' p : tripleFiber x, f p.1.1 * g p.1.2.1 * h p.1.2.2 := by
  -- Step 1: Distribute f into inner sum
  have h1 : ∑' ae : mulFiber x, f ae.1.1 * (∑' bd : mulFiber ae.1.2, g bd.1.1 * h bd.1.2) =
      ∑' ae : mulFiber x, ∑' bd : mulFiber ae.1.2, f ae.1.1 * (g bd.1.1 * h bd.1.2) := by
    congr 1; ext ae; exact ((hgh ae.1.2).tsum_mul_left (f ae.1.1)).symm
  -- Step 2: Summability
  have hsigmaR : Summable fun p : Σ ae : mulFiber x, mulFiber ae.1.2 =>
      f p.1.1.1 * (g p.2.1.1 * h p.2.1.2) := by
    simp_rw [← mul_assoc]
    convert (rightAssocEquiv x).summable_iff.mpr (htriple x) using 1
  have hfiberR : ∀ ae : mulFiber x, Summable fun bd : mulFiber ae.1.2 =>
      f ae.1.1 * (g bd.1.1 * h bd.1.2) := fun ae => (hgh ae.1.2).mul_left (f ae.1.1)
  -- Step 3: Equivalence tsum
  have h2 := (rightAssocEquiv x).tsum_eq (fun p => f p.1.1 * g p.1.2.1 * h p.1.2.2)
  -- Step 4: Fubini
  have h3 : ∑' (p : Σ ae : mulFiber x, mulFiber ae.1.2), f p.1.1.1 * (g p.2.1.1 * h p.2.1.2) =
      ∑' ae : mulFiber x, ∑' bd : mulFiber ae.1.2, f ae.1.1 * (g bd.1.1 * h bd.1.2) :=
    hsigmaR.tsum_sigma' hfiberR
  rw [h1, ← h2, ← h3]
  simp_rw [← mul_assoc]; rfl

/-- Convolution is associative: `(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)`.

Both sides reduce to `∑' (a,b,d) : tripleFiber x, f a * g b * h d` via the
`leftAssocEquiv` and `rightAssocEquiv` fiber equivalences. -/
theorem convolution_assoc (f g h : M → R)
    (hfg : ConvolutionExists f g) (hgh : ConvolutionExists g h)
    (htriple : ∀ x, tripleConvolutionExistsAt f g h x) :
    (f ⋆ g) ⋆ h = f ⋆ (g ⋆ h) := by
  ext x
  simp only [convolution]
  have hleft := convolution_assoc_left_sum (f := f) (g := g) (h := h) hfg htriple x
  have hright := convolution_assoc_right_sum (f := f) (g := g) (h := h) hgh htriple x
  rw [hleft, hright]

end Algebraic

section Identity

variable [Monoid M] [Semiring R] [TopologicalSpace R] [DecidableEq M]

/-- Left identity for convolution: `δ₁ ⋆ f = f`.

Only the pair `(1, x) ∈ mulFiber x` contributes since `δ₁` is supported at `1`. -/
theorem delta_convolution (f : M → R) : delta ⋆ f = f := by
  ext x; simp only [convolution]
  -- Only (1, x) ∈ mulFiber x contributes since delta is supported at 1
  rw [← tsum_subtype_eq_of_support_subset (s := {⟨(1, x), by simp [mulFiber, mulMap]⟩})]
  · simp_all only [tsum_fintype, univ_unique,
      Set.default_coe_singleton, sum_singleton, delta_one, one_mul]
  · intro ⟨⟨a, b⟩, hab⟩ hne
    simp_all only [Function.mem_support, ne_eq,
      Set.mem_singleton_iff, Subtype.mk.injEq, Prod.mk.injEq]
    simp_all only [mem_mulFiber]
    subst hab
    by_cases ha : a = 1
    · subst ha
      simp_all only [delta_one, one_mul, and_self]
    · simp_all only [false_and]
      exact hne (by rw [delta_ne ha, zero_mul])

/-- Right identity for convolution: `f ⋆ δ₁ = f`.

Only the pair `(x, 1) ∈ mulFiber x` contributes since `δ₁` is supported at `1`. -/
theorem convolution_delta (f : M → R) : f ⋆ delta = f := by
  ext x; simp only [convolution]
  -- Only (x, 1) ∈ mulFiber x contributes since delta is supported at 1
  rw [← tsum_subtype_eq_of_support_subset (s := {⟨(x, 1), by simp [mulFiber, mulMap]⟩})]
  · simp_all only [tsum_fintype, univ_unique,
      Set.default_coe_singleton, sum_singleton, delta_one, mul_one]
  · intro ⟨⟨a, b⟩, hab⟩ hne
    simp_all only [Function.mem_support, ne_eq,
      Set.mem_singleton_iff, Subtype.mk.injEq, Prod.mk.injEq]
    simp_all only [mem_mulFiber]
    subst hab
    by_cases hb : b = 1
    · subst hb
      simp_all only [mul_one, delta_one, and_self]
    · simp_all only [and_false]
      exact hne (by rw [delta_ne hb, mul_zero])

end Identity

section Commutative

variable [CommMonoid M] [CommSemiring R] [TopologicalSpace R]

/-- Commutativity of convolution for commutative monoids and semirings: `f ⋆ g = g ⋆ f`.

Uses the swap equivalence `(a, b) ↔ (b, a)` on fibers, which preserves membership
since `a * b = b * a` in a commutative monoid. -/
theorem convolution_comm (f g : M → R) : f ⋆ g = g ⋆ f := by
  ext x; simp only [convolution]
  -- Swap equivalence: (a, b) ↦ (b, a) preserves fiber since a * b = b * a
  let e : mulFiber x ≃ mulFiber x :=
    ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨⟨b, a⟩, by simp_all [mulFiber, mulMap, mul_comm]⟩,
     fun ⟨⟨a, b⟩, h⟩ => ⟨⟨b, a⟩, by simp_all [mulFiber, mulMap, mul_comm]⟩,
     fun _ => by rfl,
     fun _ => by rfl⟩
  rw [← e.tsum_eq]
  congr 1
  funext ⟨⟨a, b⟩, hab⟩
  simp only [e, Equiv.coe_fn_mk, mul_comm]

end Commutative

end DiscreteConvolution

end
