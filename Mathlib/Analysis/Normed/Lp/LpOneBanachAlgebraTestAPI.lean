/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Lp.DiscreteConvolutionTestAPI

/-!
# Banach Algebra Structure on ℓ¹ via Discrete Convolution

This file establishes the Banach algebra structure on `lp (fun _ : M => R) 1` using
the discrete convolution from `DiscreteConvolution.lean`.

## Main Definitions

* `TripleConvolutionSummable f g h x`: summability predicate for triple products

## Main Results

### Summability and Membership
* `lp.one_summable_norm`: ℓ¹ membership gives summable norms
* `lp.one_norm_eq_tsum`: ℓ¹ norm as tsum
* `lp.one_summable_norm_mul`: product summability over `M × M`
* `lp.one_mulConvolution_memℓp`: ℓ¹ closed under convolution
* `lp.one_norm_mulConvolution_le`: submultiplicativity `‖f ⋆ₘ g‖₁ ≤ ‖f‖₁ * ‖g‖₁`
* `lp.one_delta_memℓp`: delta is in ℓ¹

### Associativity (requires `[CompleteSpace R]`)
* `lp.one_tripleConvolutionSummable`: triple product summability
* `lp.one_convolutionSummable`: pairwise product summability
* `lp.one_convolution_assoc_left_sum`, `lp.one_convolution_assoc_right_sum`: fiber reindexing
* `lp.one_mulConvolution_assoc`: associativity `(f ⋆ₘ g) ⋆ₘ h = f ⋆ₘ (g ⋆ₘ h)`

### Instances
* `lp.oneMul`: `Mul` instance via convolution
* `lp.oneOne`: `One` instance via delta
* `lp.oneRing`: `Ring` instance (requires `[CompleteSpace R]`)
* `lp.oneNormedRing`: `NormedRing` instance
* `lp.oneNormOneClass`: `NormOneClass` (when `[NormOneClass R]`)
* `lp.oneCommRing`: `CommRing` (when `[CommMonoid M]`)
* `lp.oneNormedCommRing`: `NormedCommRing` (when `[CommMonoid M]`)
* `lp.oneAlgebra`: `Algebra 𝕜` instance
* `lp.oneNormedAlgebra`: `NormedAlgebra 𝕜` instance

## Design Notes

This file builds on `DiscreteConvolution.lean` which provides:
* `mulConvolution`: the convolution operation `f ⋆ₘ g`
* `delta`: the identity element
* Ring axioms: `mulConvolution_add`, `delta_mulConvolution`, etc.
* Fiber equivalences: `leftAssocEquiv`, `rightAssocEquiv` for associativity

The ℓ¹ properties (summability, norm bounds) and typeclass instances are separated here
to follow Mathlib conventions of keeping core theory distinct from specific instances.
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
theorem lp.one_norm_mulConvolution_le (f g : lp (fun _ : M => R) 1) :
    ‖(⟨mulConvolution (⇑f) (⇑g), lp.one_mulConvolution_memℓp f g⟩ :
      lp (fun _ : M => R) 1)‖ ≤ ‖f‖ * ‖g‖ := by
  simp only [lp.one_norm_eq_tsum]
  have hprod := lp.one_summable_norm_mul f g
  have hsigma : Summable fun p : Σ x : M, mulFiber x => ‖f p.2.1.1‖ * ‖g p.2.1.2‖ := by
    convert (Equiv.sigmaFiberEquiv mulMap).summable_iff.mpr hprod using 1
  have hbound : ∀ x, ‖(mulConvolution (⇑f) (⇑g)) x‖ ≤
      ∑' ab : mulFiber x, ‖f ab.1.1‖ * ‖g ab.1.2‖ := by
    intro x
    have hx := hprod.subtype (mulFiber x)
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ab => norm_mul_le _ _) hx
    · exact Summable.tsum_le_tsum (fun ab => norm_mul_le _ _)
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ab => norm_mul_le _ _) hx) hx
  refine (Summable.tsum_le_tsum hbound ?_ hsigma.sigma).trans (le_of_eq ?_)
  · have := lp.one_mulConvolution_memℓp f g
    simpa using (memℓp_gen_iff (by norm_num)).mp this
  · rw [← hsigma.tsum_sigma']
    · exact (lp.one_summable_norm f).tsum_mul_tsum (lp.one_summable_norm g) hprod ▸
        (Equiv.sigmaFiberEquiv mulMap).tsum_eq (fun p => ‖f p.1‖ * ‖g p.2‖)
    · exact fun b => hsigma.sigma_factor b

/-- The identity element `delta 1` is in ℓ¹. -/
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
def TripleConvolutionSummable (f g h : M → R) (x : M) : Prop :=
  Summable fun p : tripleFiber x => f p.1.1 * g p.1.2.1 * h p.1.2.2

/-- ℓ¹ functions have summable triple convolution. -/
theorem lp.one_tripleConvolutionSummable (f g h : lp (fun _ : M => R) 1) (x : M) :
    TripleConvolutionSummable (⇑f) (⇑g) (⇑h) x := by
  unfold TripleConvolutionSummable
  have hf : Summable fun m : M => ‖f m‖ := lp.one_summable_norm f
  have hg : Summable fun m : M => ‖g m‖ := lp.one_summable_norm g
  have hh : Summable fun m : M => ‖h m‖ := lp.one_summable_norm h
  have hfg : Summable fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖ :=
    hf.mul_of_nonneg hg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hfg' : Summable fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖ := hfg
  have hfgh : Summable fun abc : (M × M) × M => (‖f abc.1.1‖ * ‖g abc.1.2‖) * ‖h abc.2‖ :=
    hfg'.mul_of_nonneg hh
      (fun ab => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun _ => norm_nonneg _)
  have hfgh' : Summable fun abc : M × M × M => ‖f abc.1‖ * ‖g abc.2.1‖ * ‖h abc.2.2‖ :=
    (Equiv.prodAssoc M M M).symm.summable_iff.mpr hfgh |>.congr fun _ => by rfl
  have hsub : Summable fun p : tripleFiber x => ‖f p.1.1‖ * ‖g p.1.2.1‖ * ‖h p.1.2.2‖ :=
    hfgh'.subtype (tripleFiber x)
  exact Summable.of_norm_bounded hsub (fun ⟨⟨a, b, c⟩, _⟩ =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))

/-- ℓ¹ functions have summable convolutions at each point. -/
theorem lp.one_convolutionSummable (f g : lp (fun _ : M => R) 1) (x : M) :
    Summable fun ab : mulFiber x => f ab.1.1 * g ab.1.2 := by
  have hprod : Summable (fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖) :=
    (lp.one_summable_norm f).mul_of_nonneg (lp.one_summable_norm g)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact Summable.of_norm_bounded (hprod.subtype (mulFiber x))
    fun ⟨⟨a, b⟩, _⟩ => norm_mul_le _ _

/-- Left-associated convolution sum as a triple fiber sum. -/
theorem lp.one_convolution_assoc_left_sum (f g h : lp (fun _ : M => R) 1) (x : M) :
    ∑' cd : mulFiber x, (∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2) * h cd.1.2 =
      ∑' p : tripleFiber x, f p.1.1 * g p.1.2.1 * h p.1.2.2 := by
  have h1 : ∑' cd : mulFiber x,
      (∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2) * h cd.1.2 =
      ∑' cd : mulFiber x, ∑' ab : mulFiber cd.1.1, (f ab.1.1 * g ab.1.2) * h cd.1.2 := by
    congr 1; ext cd
    exact ((lp.one_convolutionSummable f g cd.1.1).tsum_mul_right (h cd.1.2)).symm
  have hsigmaL : Summable fun p : Σ cd : mulFiber x, mulFiber cd.1.1 =>
      (f p.2.1.1 * g p.2.1.2) * h p.1.1.2 := by
    convert (leftAssocEquiv x).summable_iff.mpr
      (lp.one_tripleConvolutionSummable f g h x) using 1
  have hfiberL : ∀ cd : mulFiber x, Summable fun ab : mulFiber cd.1.1 =>
      (f ab.1.1 * g ab.1.2) * h cd.1.2 :=
    fun cd => (lp.one_convolutionSummable f g cd.1.1).mul_right (h cd.1.2)
  have h2 := (leftAssocEquiv x).tsum_eq (fun p => f p.1.1 * g p.1.2.1 * h p.1.2.2)
  have h3 : ∑' (p : Σ cd : mulFiber x, mulFiber cd.1.1),
      (f p.2.1.1 * g p.2.1.2) * h p.1.1.2 =
      ∑' cd : mulFiber x, ∑' ab : mulFiber cd.1.1, (f ab.1.1 * g ab.1.2) * h cd.1.2 :=
    hsigmaL.tsum_sigma' hfiberL
  rw [h1, ← h2, ← h3]; rfl

/-- Right-associated convolution sum as a triple fiber sum. -/
theorem lp.one_convolution_assoc_right_sum (f g h : lp (fun _ : M => R) 1) (x : M) :
    ∑' ae : mulFiber x, f ae.1.1 * (∑' bd : mulFiber ae.1.2, g bd.1.1 * h bd.1.2) =
      ∑' p : tripleFiber x, f p.1.1 * g p.1.2.1 * h p.1.2.2 := by
  have h1 : ∑' ae : mulFiber x,
      f ae.1.1 * (∑' bd : mulFiber ae.1.2, g bd.1.1 * h bd.1.2) =
      ∑' ae : mulFiber x, ∑' bd : mulFiber ae.1.2, f ae.1.1 * (g bd.1.1 * h bd.1.2) := by
    congr 1; ext ae
    exact ((lp.one_convolutionSummable g h ae.1.2).tsum_mul_left (f ae.1.1)).symm
  have hsigmaR : Summable fun p : Σ ae : mulFiber x, mulFiber ae.1.2 =>
      f p.1.1.1 * (g p.2.1.1 * h p.2.1.2) := by
    simp_rw [← mul_assoc]
    convert (rightAssocEquiv x).summable_iff.mpr
      (lp.one_tripleConvolutionSummable f g h x) using 1
  have hfiberR : ∀ ae : mulFiber x, Summable fun bd : mulFiber ae.1.2 =>
      f ae.1.1 * (g bd.1.1 * h bd.1.2) :=
    fun ae => (lp.one_convolutionSummable g h ae.1.2).mul_left (f ae.1.1)
  have h2 := (rightAssocEquiv x).tsum_eq (fun p => f p.1.1 * g p.1.2.1 * h p.1.2.2)
  have h3 : ∑' (p : Σ ae : mulFiber x, mulFiber ae.1.2),
      f p.1.1.1 * (g p.2.1.1 * h p.2.1.2) =
      ∑' ae : mulFiber x, ∑' bd : mulFiber ae.1.2, f ae.1.1 * (g bd.1.1 * h bd.1.2) :=
    hsigmaR.tsum_sigma' hfiberR
  rw [h1, ← h2, ← h3]
  simp_rw [← mul_assoc]; rfl

/-- Convolution is associative for ℓ¹ functions: `(f ⋆ₘ g) ⋆ₘ h = f ⋆ₘ (g ⋆ₘ h)`. -/
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

end DiscreteConvolution

end

end
