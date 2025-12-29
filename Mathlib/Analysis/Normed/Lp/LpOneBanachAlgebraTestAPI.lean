/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Lp.DiscreteConvolutionTestAPI
public import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# Banach Algebra Structure on ℓ¹ via Discrete Convolution

This file establishes the Banach algebra structure on `lp (fun _ : M => R) 1` using
discrete convolution from `DiscreteConvolutionTestAPI`. For a monoid `M` and normed ring `R`,
the convolution `(f ⋆ₘ g)(x) = ∑' (a,b) : a * b = x, f(a) * g(b)` makes ℓ¹(M → R) into a
normed ring with submultiplicative norm.

## Main Definitions

* `TripleConvolutionSummable f g h x`: summability of `f(a) * g(b) * h(c)` over `a * b * c = x`
* `AddLp M R`: newtype wrapper for ℓ¹ with additive convolution (fibers `a + b = x`)

## Main Results

### Summability and Membership
* `lp.one_summable_norm`: ℓ¹ membership implies `Summable (‖f ·‖)`
* `lp.one_norm_eq_tsum`: ℓ¹ norm equals `∑' m, ‖f m‖`
* `lp.one_summable_norm_mul`: `Summable (fun (a,b) => ‖f a‖ * ‖g b‖)` for ℓ¹ functions
* `lp.one_mulConvolution_memℓp`: ℓ¹ is closed under convolution
* `lp.one_norm_mulConvolution_le`: submultiplicativity `‖f ⋆ₘ g‖ ≤ ‖f‖ * ‖g‖`
* `lp.one_delta_memℓp`: the delta function `δ₁` is in ℓ¹

### Associativity (requires `[CompleteSpace R]`)
* `lp.one_tripleConvolutionSummable`: triple products are summable over fibers
* `lp.one_convolutionSummable`: pairwise products are summable over fibers
* `lp.one_mulConvolution_assoc`: `(f ⋆ₘ g) ⋆ₘ h = f ⋆ₘ (g ⋆ₘ h)`

### lp Instances (Multiplicative Convolution)
* `lp.oneMul`: `Mul` via convolution
* `lp.oneOne`: `One` via delta function
* `lp.oneRing`: `Ring` (requires `[CompleteSpace R]`)
* `lp.oneNormedRing`: `NormedRing`
* `lp.oneNormOneClass`: `NormOneClass` (when `[NormOneClass R]`)
* `lp.oneCommRing`: `CommRing` (when `[CommMonoid M]`)
* `lp.oneNormedCommRing`: `NormedCommRing` (when `[CommMonoid M]`)
* `lp.one_isScalarTower`, `lp.one_smulCommClass`: scalar tower and commutativity
* `lp.oneAlgebra`, `lp.oneNormedAlgebra`: algebra instances

### AddLp Instances (Additive Convolution)
* `AddLp M R`: newtype for ℓ¹ with `addMulConvolution` (fibers `a + b = x`)
* `AddLp.instRing`: `Ring` (requires `[AddMonoid M]`, `[CompleteSpace R]`)
* `AddLp.instNormedRing`: `NormedRing`
* `AddLp.instNormOneClass`: `NormOneClass` (when `[NormOneClass R]`)
* `AddLp.instCommRing`: `CommRing` (when `[AddCommMonoid M]`)
* `AddLp.instNormedCommRing`: `NormedCommRing`
* `AddLp.instModule`: `Module 𝕜` for scalar fields
* `AddLp.instIsBoundedSMul`: `IsBoundedSMul 𝕜` for bounded scalar multiplication
* `AddLp.instIsScalarTower`, `AddLp.instSMulCommClass`: scalar tower and commutativity
* `AddLp.instAlgebra`, `AddLp.instNormedAlgebra`: algebra instances

## Design Notes

### Multiplicative vs Additive Convolution

This file uses `mulConvolution` (notation `⋆ₘ`) for `[Monoid M]`, appropriate for group
algebras R[G]. For additive indices (ℤ, polynomials), use `AddLp` with `addMulConvolution`.

### @[to_additive] Usage Notes

The `@[to_additive]`-generated lemmas (e.g., `lp.one_addMulConvolution_memℓp`) are used
directly in `AddLp` instance definitions.

**Root cause of timeouts**: Having both `[NormedAddCommGroup R]` and `[NormedCommRing R]`
in scope creates two different paths to `NormedAddCommGroup R`. The instance hierarchy is:
`NormedCommRing → NormedRing → NonUnitalNormedRing → NormedAddCommGroup`. When both are
present, Lean must unify two distinct instance terms during elaboration, which is expensive.

```lean
-- BAD: causes timeout (two paths to NormedAddCommGroup R)
variable [NormedAddCommGroup R] [AddMonoid M] [NormedCommRing R]

-- GOOD: works (single path to NormedAddCommGroup R via NormedCommRing)
variable [AddMonoid M] [NormedCommRing R]
```

See `AddLpTimeoutTest.lean` for a demonstration of this issue.

Key techniques for reliable elaboration:

1. **Avoid redundant instance assumptions**: Don't add `[NormedAddCommGroup R]` when
   `[NormedCommRing R]` is already present - the former is derived from the latter.

2. **Context-driven elaboration in subtype constructors**: When constructing `lp` subtypes
   via `⟨val, proof⟩`, Lean knows the expected type for `proof` from context before
   elaborating the proof term. This acts as a natural type barrier.

3. **Explicit type parameters**: `(M := M) (R := R)` annotations help Lean resolve types
   without expensive unification through `Memℓp` predicates.

4. **Explicit instance references**: Ring proofs reference `instOne.1` explicitly rather
   than `(1 : AddLp M R)` to avoid ambiguity with the `Zero` inherited from `AddCommGroup`.

5. **Type barriers for `tsum_sigma'`**: The `Summable.tsum_sigma'` lemma causes timeouts
   when used with `rw`. Workaround: compute the result via `have` with explicit type
   signature first, then use `▸` substitution.

### Runtime Optimization

Proofs in this file are optimized for elaboration speed. Key principles:

1. **Use `convert ... using 1` for deferred unification**: Direct term-mode proofs for
   `Summable` over sigma types can timeout due to expensive type class searches. The
   `convert` tactic defers unification, avoiding these searches during initial elaboration.

2. **Use function argument syntax for `have`**: Write `have hfoo (x : T) : P x := ...`
   instead of `have hfoo : ∀ x : T, P x := fun x => ...` for cleaner syntax.

-/

@[expose] public section

open scoped BigOperators NNReal ENNReal DiscreteConvolution

noncomputable section

namespace DiscreteConvolution

variable {M : Type*} {R : Type*}

/-! ### ℓ¹ Summability and Membership -/

section LpOneSummability

variable [NormedRing R]

/-- ℓ¹ membership gives summable norms. -/
theorem lp.one_summable_norm (f : lp (fun _ : M => R) 1) : Summable (fun m => ‖f m‖) := by
  have hf := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)] at hf
  simpa using hf

/-- The ℓ¹ norm equals the sum of norms. -/
theorem lp.one_norm_eq_tsum (f : lp (fun _ : M => R) 1) :
    ‖f‖ = ∑' m, ‖f m‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]

/-- Product of ℓ¹ norms is summable over M × M. -/
theorem lp.one_summable_norm_mul (f g : lp (fun _ : M => R) 1) :
    Summable (fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖) :=
  (lp.one_summable_norm f).mul_of_nonneg (lp.one_summable_norm g)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

end LpOneSummability

section LpOneMembership

variable [Monoid M] [NormedCommRing R]

/-- The ring multiplication convolution of ℓ¹ functions is in ℓ¹. -/
@[to_additive (dont_translate := R) (relevant_arg := 1) lp.one_addMulConvolution_memℓp
  /-- The additive ring multiplication convolution of ℓ¹ functions is in ℓ¹. -/]
theorem lp.one_mulConvolution_memℓp (f g : lp (fun _ : M => R) 1) :
    Memℓp (mulConvolution (⇑f) (⇑g)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have hprod := lp.one_summable_norm_mul f g
  have hfiber : ∀ x, Summable fun ab : mulFiber x => ‖f ab.1.1‖ * ‖g ab.1.2‖ :=
    fun x => hprod.subtype _
  have hbound :
      ∀ x, ‖(mulConvolution (⇑f) (⇑g)) x‖ ≤
        ∑' ab : mulFiber x, ‖f ab.1.1‖ * ‖g ab.1.2‖ := by
    intro x
    have hx := hfiber x
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ab => norm_mul_le _ _) hx
    · exact Summable.tsum_le_tsum (fun ab => norm_mul_le _ _)
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ab => norm_mul_le _ _) hx) hx
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact ((Equiv.sigmaFiberEquiv mulMap).summable_iff.mpr hprod).sigma

/-- Submultiplicativity of the ℓ¹ norm under ring convolution. -/
@[to_additive (dont_translate := R) (relevant_arg := 1) lp.one_norm_addMulConvolution_le
  /-- Submultiplicativity of the ℓ¹ norm under additive ring convolution. -/]
theorem lp.one_norm_mulConvolution_le (f g : lp (fun _ : M => R) 1) :
    ‖(⟨mulConvolution (⇑f) (⇑g), lp.one_mulConvolution_memℓp f g⟩ :
      lp (fun _ : M => R) 1)‖ ≤ ‖f‖ * ‖g‖ := by
  rw [lp.one_norm_eq_tsum, lp.one_norm_eq_tsum, lp.one_norm_eq_tsum]
  have hprod : Summable fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖ := lp.one_summable_norm_mul f g
  have hsigma := (Equiv.sigmaFiberEquiv mulMap).summable_iff.mpr hprod
  have hbound (x : M) : ‖(mulConvolution (⇑f) (⇑g)) x‖ ≤
      ∑' ab : mulFiber x, ‖f ab.1.1‖ * ‖g ab.1.2‖ :=
    (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun _ => norm_mul_le _ _) (hprod.subtype _))).trans
    (Summable.tsum_le_tsum (fun _ => norm_mul_le _ _) (Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun _ => norm_mul_le _ _) (hprod.subtype _)) (hprod.subtype _))
  have hmemℓp : Summable fun m => ‖mulConvolution (⇑f) (⇑g) m‖ := by
    simpa using (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mp
      (lp.one_mulConvolution_memℓp f g)
  refine (Summable.tsum_le_tsum hbound hmemℓp hsigma.sigma).trans (le_of_eq ?_)
  exact (hsigma.tsum_sigma' hsigma.sigma_factor) ▸
    (lp.one_summable_norm f).tsum_mul_tsum (lp.one_summable_norm g) hprod ▸
    (Equiv.sigmaFiberEquiv mulMap).tsum_eq (fun p => ‖f p.1‖ * ‖g p.2‖)

/-- The identity element `delta 1` is in ℓ¹. -/
@[to_additive (dont_translate := R) (relevant_arg := 1) lp.one_addDelta_memℓp
  /-- The identity element `addDelta 1` is in ℓ¹. -/]
theorem lp.one_delta_memℓp [DecidableEq M] : Memℓp (delta (M := M) (1 : R)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have h : (fun m => ‖delta (M := M) (1 : R) m‖) =
      fun m => if m = 1 then ‖(1 : R)‖ else 0 := by
    ext m
    by_cases hm : m = 1
    · simp only [hm, ↓reduceIte]
      rw [delta, Pi.single_eq_same]
    · rw [if_neg hm, delta_ne 1 hm, norm_zero]
  rw [h]
  exact summable_of_ne_finset_zero (s := {1})
    (by intro b hb; simp_all only [Finset.mem_singleton, ↓reduceIte])

end LpOneMembership

/-! ### ℓ¹ Associativity -/

section LpOneAssociativity

variable [Monoid M] [NormedCommRing R] [CompleteSpace R]

/-- Summability over triple fiber for associativity. -/
@[to_additive (dont_translate := R) (relevant_arg := 1) TripleAddConvolutionSummable
  /-- Summability over triple additive fiber for associativity. -/]
def TripleConvolutionSummable (f g h : M → R) (x : M) : Prop :=
  Summable fun p : tripleFiber x => f p.1.1 * g p.1.2.1 * h p.1.2.2

/-- ℓ¹ functions have summable triple convolution. -/
@[to_additive (dont_translate := R) (relevant_arg := 1) lp.one_tripleAddConvolutionSummable
  /-- ℓ¹ functions have summable triple additive convolution. -/]
theorem lp.one_tripleConvolutionSummable (f g h : lp (fun _ : M => R) 1) (x : M) :
    TripleConvolutionSummable (⇑f) (⇑g) (⇑h) x := by
  unfold TripleConvolutionSummable
  have hfg := lp.one_summable_norm_mul f g
  have hfgh : Summable fun abc : M × M × M => ‖f abc.1‖ * ‖g abc.2.1‖ * ‖h abc.2.2‖ :=
    (Equiv.prodAssoc M M M).symm.summable_iff.mpr (hfg.mul_of_nonneg (lp.one_summable_norm h)
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun _ => norm_nonneg _))
  exact (hfgh.subtype _).of_norm_bounded fun ⟨⟨a, b, c⟩, _⟩ =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

/-- ℓ¹ functions have summable convolutions at each point. -/
@[to_additive (dont_translate := R) (relevant_arg := 1) lp.one_addConvolutionSummable
  /-- ℓ¹ functions have summable additive convolutions at each point. -/]
theorem lp.one_convolutionSummable (f g : lp (fun _ : M => R) 1) (x : M) :
    Summable fun ab : mulFiber x => f ab.1.1 * g ab.1.2 :=
  ((lp.one_summable_norm_mul f g).subtype _).of_norm_bounded fun ⟨⟨_, _⟩, _⟩ => norm_mul_le _ _

/-- Left-associated convolution sum as a triple fiber sum. -/
@[to_additive (dont_translate := R) (relevant_arg := 1) lp.one_addConvolution_assoc_left_sum
  /-- Left-associated additive convolution sum as a triple fiber sum. -/]
theorem lp.one_convolution_assoc_left_sum (f g h : lp (fun _ : M => R) 1) (x : M) :
    ∑' cd : mulFiber x, (∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2) * h cd.1.2 =
      ∑' p : tripleFiber x, f p.1.1 * g p.1.2.1 * h p.1.2.2 := by
  have h1 : ∑' cd : mulFiber x,
      (∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2) * h cd.1.2 =
      ∑' cd : mulFiber x, ∑' ab : mulFiber cd.1.1, (f ab.1.1 * g ab.1.2) * h cd.1.2 :=
    tsum_congr fun cd => ((lp.one_convolutionSummable f g cd.1.1).tsum_mul_right (h cd.1.2)).symm
  have hsigmaL : Summable fun p : Σ cd : mulFiber x, mulFiber cd.1.1 =>
      (f p.2.1.1 * g p.2.1.2) * h p.1.1.2 := by
    convert (leftAssocEquiv x).summable_iff.mpr (lp.one_tripleConvolutionSummable f g h x) using 1
  have hfiberL (cd : mulFiber x) : Summable fun ab : mulFiber cd.1.1 =>
      (f ab.1.1 * g ab.1.2) * h cd.1.2 :=
    (lp.one_convolutionSummable f g cd.1.1).mul_right (h cd.1.2)
  have h2 := (leftAssocEquiv x).tsum_eq (fun p => f p.1.1 * g p.1.2.1 * h p.1.2.2)
  have h3 : ∑' (p : Σ cd : mulFiber x, mulFiber cd.1.1),
      (f p.2.1.1 * g p.2.1.2) * h p.1.1.2 =
      ∑' cd : mulFiber x, ∑' ab : mulFiber cd.1.1, (f ab.1.1 * g ab.1.2) * h cd.1.2 :=
    hsigmaL.tsum_sigma' hfiberL
  rw [h1, ← h2, ← h3]; rfl

/-- Right-associated convolution sum as a triple fiber sum. -/
@[to_additive (dont_translate := R) (relevant_arg := 1) lp.one_addConvolution_assoc_right_sum
  /-- Right-associated additive convolution sum as a triple fiber sum. -/]
theorem lp.one_convolution_assoc_right_sum (f g h : lp (fun _ : M => R) 1) (x : M) :
    ∑' ae : mulFiber x, f ae.1.1 * (∑' bd : mulFiber ae.1.2, g bd.1.1 * h bd.1.2) =
      ∑' p : tripleFiber x, f p.1.1 * g p.1.2.1 * h p.1.2.2 := by
  have h1 : ∑' ae : mulFiber x,
      f ae.1.1 * (∑' bd : mulFiber ae.1.2, g bd.1.1 * h bd.1.2) =
      ∑' ae : mulFiber x, ∑' bd : mulFiber ae.1.2, f ae.1.1 * (g bd.1.1 * h bd.1.2) :=
    tsum_congr fun ae => ((lp.one_convolutionSummable g h ae.1.2).tsum_mul_left (f ae.1.1)).symm
  have hsigmaR : Summable fun p : Σ ae : mulFiber x, mulFiber ae.1.2 =>
      f p.1.1.1 * (g p.2.1.1 * h p.2.1.2) := by
    simp_rw [← mul_assoc]
    convert (rightAssocEquiv x).summable_iff.mpr (lp.one_tripleConvolutionSummable f g h x) using 1
  have hfiberR (ae : mulFiber x) : Summable fun bd : mulFiber ae.1.2 =>
      f ae.1.1 * (g bd.1.1 * h bd.1.2) :=
    (lp.one_convolutionSummable g h ae.1.2).mul_left (f ae.1.1)
  have h2 := (rightAssocEquiv x).tsum_eq (fun p => f p.1.1 * g p.1.2.1 * h p.1.2.2)
  have h3 : ∑' (p : Σ ae : mulFiber x, mulFiber ae.1.2),
      f p.1.1.1 * (g p.2.1.1 * h p.2.1.2) =
      ∑' ae : mulFiber x, ∑' bd : mulFiber ae.1.2, f ae.1.1 * (g bd.1.1 * h bd.1.2) :=
    hsigmaR.tsum_sigma' hfiberR
  rw [h1, ← h2, ← h3]; simp_rw [← mul_assoc]; rfl

/-- Convolution is associative for ℓ¹ functions: `(f ⋆ₘ g) ⋆ₘ h = f ⋆ₘ (g ⋆ₘ h)`. -/
@[to_additive (dont_translate := R) (relevant_arg := 1) lp.one_addMulConvolution_assoc
  /-- Additive convolution is associative for ℓ¹ functions. -/]
theorem lp.one_mulConvolution_assoc (f g h : lp (fun _ : M => R) 1) :
    mulConvolution (mulConvolution (⇑f) (⇑g)) (⇑h) =
    mulConvolution (⇑f) (mulConvolution (⇑g) (⇑h)) := by
  ext x
  simp only [mulConvolution_apply]
  have hleft := lp.one_convolution_assoc_left_sum f g h x
  have hright := lp.one_convolution_assoc_right_sum f g h x
  rw [hleft, hright]

end LpOneAssociativity

/-! ### ℓ¹ Mul Instance -/

section LpOneMul

variable [Monoid M] [NormedCommRing R]

namespace lp

/-- Multiplication on `lp (fun _ : M => R) 1` via discrete convolution. -/
instance oneMul : Mul (lp (fun _ : M => R) 1) where
  mul f g := ⟨mulConvolution (⇑f) (⇑g), one_mulConvolution_memℓp f g⟩

@[simp]
theorem one_mul_coe (f g : lp (fun _ : M => R) 1) :
    ⇑(f * g) = mulConvolution (⇑f) (⇑g) := rfl

/-- Submultiplicativity for the ring multiplication. -/
theorem one_norm_mul_le (f g : lp (fun _ : M => R) 1) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ :=
  one_norm_mulConvolution_le f g

end lp

end LpOneMul

/-! ### ℓ¹ One Instance -/

section LpOneOne

variable [Monoid M] [DecidableEq M] [NormedCommRing R]

namespace lp

/-- The multiplicative identity on `lp (fun _ : M => R) 1` is `delta 1`. -/
instance oneOne : One (lp (fun _ : M => R) 1) where
  one := ⟨delta 1, one_delta_memℓp⟩

@[simp]
theorem one_one_coe : ⇑(1 : lp (fun _ : M => R) 1) = delta (1 : R) := rfl

end lp

end LpOneOne

/-! ### ℓ¹ Ring and NormedRing Instances -/

section LpOneRing

variable [Monoid M] [DecidableEq M] [NormedCommRing R] [CompleteSpace R]

namespace lp

/-- `lp (fun _ : M => R) 1` is a ring under discrete convolution. -/
instance oneRing : Ring (lp (fun _ : M => R) 1) where
  mul_assoc f g h := lp.ext <| one_mulConvolution_assoc f g h
  one_mul f := lp.ext <| (delta_mulConvolution (1 : R) (⇑f)).trans (one_smul R (⇑f))
  mul_one f := lp.ext <| (mulConvolution_delta (1 : R) (⇑f)).trans (one_smul R (⇑f))
  left_distrib f g h := lp.ext <| mulConvolution_add (⇑f) (⇑g) (⇑h)
      (fun x => one_convolutionSummable f g x) (fun x => one_convolutionSummable f h x)
  right_distrib f g h := lp.ext <| add_mulConvolution (⇑f) (⇑g) (⇑h)
      (fun x => one_convolutionSummable f h x) (fun x => one_convolutionSummable g h x)
  zero_mul f := lp.ext <| zero_mulConvolution (⇑f)
  mul_zero f := lp.ext <| mulConvolution_zero (⇑f)

/-- `lp (fun _ : M => R) 1` is a normed ring. -/
instance oneNormedRing : NormedRing (lp (fun _ : M => R) 1) :=
  { lp.normedAddCommGroup, lp.oneRing with
    dist_eq := fun _ _ => rfl
    norm_mul_le := one_norm_mul_le }

end lp

end LpOneRing

/-! ### ℓ¹ NormOneClass -/

section LpOneNormOneClass

variable [Monoid M] [DecidableEq M]
variable [NormedCommRing R] [NormOneClass R]

namespace lp

theorem one_norm_one : ‖(1 : lp (fun _ : M => R) 1)‖ = 1 := by
  rw [one_norm_eq_tsum]
  have h : (fun m => ‖(1 : lp (fun _ : M => R) 1) m‖) = fun m => if m = 1 then 1 else 0 := by
    ext m
    by_cases hm : m = 1
    · simp only [hm, ↓reduceIte, one_one_coe]
      rw [delta, Pi.single_eq_same, norm_one]
    · rw [if_neg hm, one_one_coe, delta_ne _ hm, norm_zero]
  rw [h, tsum_ite_eq]

instance oneNormOneClass : NormOneClass (lp (fun _ : M => R) 1) where
  norm_one := one_norm_one

end lp

end LpOneNormOneClass

/-! ### ℓ¹ CommRing -/

section LpOneCommRing

variable [CommMonoid M] [DecidableEq M] [NormedCommRing R] [CompleteSpace R]

namespace lp

/-- `lp (fun _ : M => R) 1` is a commutative ring when M is a commutative monoid. -/
instance oneCommRing : CommRing (lp (fun _ : M => R) 1) where
  mul_comm f g := lp.ext <| mulConvolution_comm (⇑f) (⇑g)

end lp

end LpOneCommRing

/-! ### ℓ¹ NormedCommRing -/

section LpOneNormedCommRing

variable [CommMonoid M] [DecidableEq M] [NormedCommRing R] [CompleteSpace R]

namespace lp

/-- `lp (fun _ : M => R) 1` is a normed commutative ring when M is commutative. -/
instance oneNormedCommRing : NormedCommRing (lp (fun _ : M => R) 1) where
  mul_comm f g := lp.ext <| mulConvolution_comm (⇑f) (⇑g)

end lp

end LpOneNormedCommRing

/-! ### ℓ¹ Algebra -/

section LpOneAlgebra

variable [CommMonoid M] [DecidableEq M]
variable {𝕜 : Type*}
variable [NormedField 𝕜] [NormedCommRing R] [CompleteSpace R] [NormedAlgebra 𝕜 R]

namespace lp

/-- Scalar multiplication satisfies `(c • f) * g = c • (f * g)`. -/
theorem one_smul_mul_assoc (c : 𝕜) (f g : lp (fun _ : M => R) 1) :
    (c • f) * g = c • (f * g) := lp.ext <| funext fun x => by
  simp only [one_mul_coe, lp.coeFn_smul, Pi.smul_apply, mulConvolution_apply]
  simp_rw [smul_mul_assoc]
  exact Summable.tsum_const_smul c (lp.one_convolutionSummable f g x)

/-- Scalar multiplication satisfies `f * (c • g) = c • (f * g)`. -/
theorem one_mul_smul_comm (c : 𝕜) (f g : lp (fun _ : M => R) 1) :
    f * (c • g) = c • (f * g) := lp.ext <| funext fun x => by
  simp only [one_mul_coe, lp.coeFn_smul, Pi.smul_apply, mulConvolution_apply]
  simp_rw [mul_smul_comm]
  exact Summable.tsum_const_smul c (lp.one_convolutionSummable f g x)

instance one_isScalarTower :
    IsScalarTower 𝕜 (lp (fun _ : M => R) 1) (lp (fun _ : M => R) 1) :=
  ⟨fun c f g => one_smul_mul_assoc c f g⟩

instance one_smulCommClass :
    SMulCommClass 𝕜 (lp (fun _ : M => R) 1) (lp (fun _ : M => R) 1) :=
  ⟨fun c f g => (one_mul_smul_comm c f g).symm⟩

instance oneAlgebra : Algebra 𝕜 (lp (fun _ : M => R) 1) :=
  Algebra.ofModule one_smul_mul_assoc one_mul_smul_comm

instance oneNormedAlgebra : NormedAlgebra 𝕜 (lp (fun _ : M => R) 1) where
  norm_smul_le := norm_smul_le

end lp

end LpOneAlgebra

/-! ## AddLp: ℓ¹ with Additive Convolution

`AddLp M R` wraps `lp (fun _ : M => R) 1` with multiplication via `addMulConvolution`:
`(f * g)(x) = ∑' (a,b) : a + b = x, f(a) * g(b)`. Appropriate for polynomial-like structures
where the index type has additive structure (e.g., ℤ, ℕ).

See the "Timeout Workarounds" section in the module docstring for implementation details. -/

/-! ### AddLp Type and Instances -/

section AddLp

/-- Newtype wrapper for ℓ¹ with additive convolution.
`AddLp M R` is `lp (fun _ : M => R) 1` with multiplication via `addMulConvolution`. -/
structure AddLp (M : Type*) (R : Type*) [NormedAddCommGroup R] where
  /-- The underlying lp element. -/
  toLp : lp (fun _ : M => R) 1

namespace AddLp

variable {M : Type*} {R : Type*} [NormedAddCommGroup R]

/-- Equivalence between `AddLp M R` and the underlying `lp` type. -/
protected def equiv : AddLp M R ≃ lp (fun _ : M => R) 1 where
  toFun := toLp
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coercion from the underlying lp type. -/
def ofLp (f : lp (fun _ : M => R) 1) : AddLp M R := ⟨f⟩

-- Transfer instances via equiv
instance : AddCommGroup (AddLp M R) := AddLp.equiv.addCommGroup
instance : NormedAddCommGroup (AddLp M R) := AddLp.equiv.normedAddCommGroup

instance : CoeFun (AddLp M R) (fun _ => M → R) where
  coe f := f.toLp

@[simp] theorem toLp_ofLp (f : lp (fun _ : M => R) 1) : (ofLp f).toLp = f := rfl
@[simp] theorem ofLp_toLp (f : AddLp M R) : ofLp f.toLp = f := rfl
theorem mk_toLp (f : lp (fun _ : M => R) 1) : (⟨f⟩ : AddLp M R).toLp = f := rfl

theorem ext {f g : AddLp M R} (h : ∀ m, f m = g m) : f = g := by
  cases f; cases g; simp only [mk.injEq]; exact lp.ext (funext h)

-- Helper lemmas for AddLp zero/one coercions (no additional instances needed)
private theorem zero_toLp : (0 : AddLp M R).toLp = 0 := rfl
private theorem add_toLp (f g : AddLp M R) : (f + g).toLp = f.toLp + g.toLp := rfl

end AddLp

section AddLpInstances

variable {M : Type*} {R : Type*} [AddMonoid M] [NormedCommRing R]

namespace AddLp

section Mul

instance instMul : Mul (AddLp M R) where
  mul f g := ⟨(⇑f.toLp) ⋆₊ₘ (⇑g.toLp), lp.one_addMulConvolution_memℓp f.toLp g.toLp⟩

@[simp] theorem mul_apply (f g : AddLp M R) (x : M) :
    (f * g) x = (f.toLp ⋆₊ₘ g.toLp) x := rfl

end Mul

section One

variable [DecidableEq M]

instance instOne : One (AddLp M R) where
  one := ⟨addDelta 1, lp.one_addDelta_memℓp⟩

@[simp] theorem one_apply (x : M) :
    (1 : AddLp M R) x = addDelta (1 : R) x := rfl

end One

section Ring

variable [CompleteSpace R] [DecidableEq M]

instance instRing : Ring (AddLp M R) where
  mul_assoc f g h := AddLp.ext fun _ =>
    congr_fun (lp.one_addMulConvolution_assoc (M := M) (R := R) f.toLp g.toLp h.toLp) _
  one_mul f := AddLp.ext fun x => by
    change (instOne.1.toLp ⋆₊ₘ f.toLp) x = f x
    simp only [instOne, addDelta_addMulConvolution' 1 f.toLp x, one_mul]
  mul_one f := AddLp.ext fun x => by
    change (f.toLp ⋆₊ₘ instOne.1.toLp) x = f x
    simp only [instOne, addMulConvolution_addDelta' f.toLp 1 x, mul_one]
  left_distrib f g h := AddLp.ext fun x => by
    change (f.toLp ⋆₊ₘ (g.toLp + h.toLp)) x = ((f * g).toLp + (f * h).toLp) x
    rw [lp.coeFn_add, Pi.add_apply]
    exact congr_fun (addMulConvolution_add f.toLp g.toLp h.toLp
      (lp.one_addConvolutionSummable (M := M) (R := R) f.toLp g.toLp)
      (lp.one_addConvolutionSummable (M := M) (R := R) f.toLp h.toLp)) x
  right_distrib f g h := AddLp.ext fun x => by
    change ((f.toLp + g.toLp) ⋆₊ₘ h.toLp) x = (f * h) x + (g * h) x
    rw [mul_apply, mul_apply]
    exact congr_fun (add_addMulConvolution f.toLp g.toLp h.toLp
      (lp.one_addConvolutionSummable (M := M) (R := R) f.toLp h.toLp)
      (lp.one_addConvolutionSummable (M := M) (R := R) g.toLp h.toLp)) x
  zero_mul f := AddLp.ext fun x => by
    change ((0 : AddLp M R).toLp ⋆₊ₘ f.toLp) x = (0 : AddLp M R) x
    simp only [zero_toLp, lp.coeFn_zero, zero_addMulConvolution, Pi.zero_apply]
  mul_zero f := AddLp.ext fun x => by
    change (f.toLp ⋆₊ₘ (0 : AddLp M R).toLp) x = (0 : AddLp M R) x
    simp only [zero_toLp, lp.coeFn_zero, addMulConvolution_zero, Pi.zero_apply]

instance instNormedRing : NormedRing (AddLp M R) :=
  { AddLp.instNormedAddCommGroup, AddLp.instRing with
    dist_eq := fun _ _ => rfl
    norm_mul_le := fun f g =>
      lp.one_norm_addMulConvolution_le (M := M) (R := R) f.toLp g.toLp }

end Ring

section NormOneClass

variable [CompleteSpace R] [DecidableEq M] [NormOneClass R]

theorem norm_one : ‖(1 : AddLp M R)‖ = 1 := by
  have h : ‖(1 : AddLp M R)‖ = ‖instOne.1.toLp‖ := rfl
  rw [h, lp.one_norm_eq_tsum]
  have heq : (fun m => ‖(instOne (M := M) (R := R)).1.toLp m‖) =
      fun m => if m = 0 then 1 else 0 := by
    ext m
    simp only [instOne]
    by_cases hm : m = 0
    · subst hm
      simp only [↓reduceIte, addDelta, Pi.single_eq_same]
      exact NormOneClass.norm_one
    · rw [if_neg hm, addDelta_ne 1 hm, norm_zero]
  rw [heq, tsum_ite_eq]

instance instNormOneClass : NormOneClass (AddLp M R) where
  norm_one := norm_one

end NormOneClass

end AddLp

/-! ### AddLp CommRing -/

section AddLpCommRing

variable {M : Type*} {R : Type*} [AddCommMonoid M] [DecidableEq M]
variable [NormedCommRing R] [CompleteSpace R]

namespace AddLp

/-- `AddLp M R` is a commutative ring when M is an additive commutative monoid. -/
instance instCommRing : CommRing (AddLp M R) where
  mul_comm f g := AddLp.ext fun _ => congr_fun (addMulConvolution_comm (⇑f.toLp) (⇑g.toLp)) _

end AddLp

end AddLpCommRing

/-! ### AddLp NormedCommRing -/

section AddLpNormedCommRing

variable {M : Type*} {R : Type*} [AddCommMonoid M] [DecidableEq M]
variable [NormedCommRing R] [CompleteSpace R]

namespace AddLp

/-- `AddLp M R` is a normed commutative ring when M is an additive commutative monoid. -/
instance instNormedCommRing : NormedCommRing (AddLp M R) where
  mul_comm f g := AddLp.ext fun _ => congr_fun (addMulConvolution_comm (⇑f.toLp) (⇑g.toLp)) _

end AddLp

end AddLpNormedCommRing

/-! ### AddLp Module -/

section AddLpModule

variable {M : Type*} {R : Type*} [NormedAddCommGroup R]
variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 R]

namespace AddLp

instance instModule : Module 𝕜 (AddLp M R) := AddLp.equiv.module 𝕜

theorem smul_toLp (c : 𝕜) (f : AddLp M R) : (c • f).toLp = c • f.toLp := rfl

instance instIsBoundedSMul : IsBoundedSMul 𝕜 (AddLp M R) where
  dist_smul_pair' c f g := by
    simp only [dist_eq_norm, ← smul_sub, sub_zero]
    exact norm_smul_le (β := lp (fun _ : M => R) 1) c (f - g).toLp
  dist_pair_smul' c₁ c₂ f := by
    simp only [dist_eq_norm, ← sub_smul, sub_zero]
    exact norm_smul_le (β := lp (fun _ : M => R) 1) (c₁ - c₂) f.toLp

end AddLp

end AddLpModule

/-! ### AddLp Algebra -/

section AddLpAlgebra

variable {M : Type*} {R : Type*} [AddCommMonoid M] [DecidableEq M]
variable {𝕜 : Type*}
variable [NormedField 𝕜] [NormedCommRing R] [CompleteSpace R] [NormedAlgebra 𝕜 R]

namespace AddLp

/-- Scalar multiplication satisfies `(c • f) * g = c • (f * g)`. -/
theorem one_smul_mul_assoc (c : 𝕜) (f g : AddLp M R) :
    (c • f) * g = c • (f * g) := AddLp.ext fun x => by
  simp only [mul_apply, smul_toLp, addMulConvolution_apply, lp.coeFn_smul, Pi.smul_apply]
  simp_rw [smul_mul_assoc]
  exact Summable.tsum_const_smul c
    (lp.one_addConvolutionSummable (M := M) (R := R) f.toLp g.toLp x)

/-- Scalar multiplication satisfies `f * (c • g) = c • (f * g)`. -/
theorem one_mul_smul_comm (c : 𝕜) (f g : AddLp M R) :
    f * (c • g) = c • (f * g) := AddLp.ext fun x => by
  simp only [mul_apply, smul_toLp, addMulConvolution_apply, lp.coeFn_smul, Pi.smul_apply]
  simp_rw [mul_smul_comm]
  exact Summable.tsum_const_smul c
    (lp.one_addConvolutionSummable (M := M) (R := R) f.toLp g.toLp x)

instance instIsScalarTower : IsScalarTower 𝕜 (AddLp M R) (AddLp M R) :=
  ⟨fun c f g => one_smul_mul_assoc c f g⟩

instance instSMulCommClass : SMulCommClass 𝕜 (AddLp M R) (AddLp M R) :=
  ⟨fun c f g => (one_mul_smul_comm c f g).symm⟩

instance instAlgebra : Algebra 𝕜 (AddLp M R) :=
  Algebra.ofModule one_smul_mul_assoc one_mul_smul_comm

instance instNormedAlgebra : NormedAlgebra 𝕜 (AddLp M R) where
  norm_smul_le := norm_smul_le

end AddLp


end AddLpAlgebra

end AddLpInstances

end AddLp

end DiscreteConvolution

end

end
