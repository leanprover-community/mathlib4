/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Banach Algebra Structure on ℓ¹ via Cauchy Product

This file establishes that `lp E 1` (the ℓ¹ space) is a commutative unital Banach algebra
when equipped with the Cauchy product (discrete convolution).

## Main Results

### Ring Structure
* `lp.oneRing`: For `NormedRing R`, `lp (fun _ : ℕ => R) 1` is a `Ring`
* `lp.oneNormedCommRing`: For `NormedCommRing R`, `lp (fun _ : ℕ => R) 1` is a `NormedCommRing`

### Normed Algebra Structure
* `lp.oneNormedRing`: `lp (fun _ : ℕ => R) 1` is a `NormedRing`
* `lp.oneNormOneClass`: `‖1‖ = 1`
* `lp.oneNormedAlgebra`: `lp (fun _ : ℕ => R) 1` is a `NormedAlgebra 𝕜` for `NormedField 𝕜`

### Key Lemmas
* `Memℓp.one_mul`: Cauchy product preserves ℓ¹ membership
* `one_memℓp_one`: The identity element is in ℓ¹
* `lp.one_norm_mul_le`: Submultiplicativity `‖f * g‖ ≤ ‖f‖ * ‖g‖`

## Design Philosophy

### Transport from PowerSeries

Ring axioms (associativity, commutativity, distributivity) are **transported** from
`PowerSeries R` rather than proven via direct sum manipulations. The key insight is:

  `(a ⋆ b)_n = Σ_{k+l=n} a_k * b_l`

is exactly the coefficient of `X^n` in `(Σ a_k X^k) * (Σ b_l X^l)`. Since Mathlib already
proves `CommSemiring (PowerSeries R)`, we inherit all ring axioms for free.

### Separation of Concerns

```
┌──────────────────────────────────────────────────────────────────┐
│ Pure Algebra (CauchyProduct namespace)                           │
│ • CauchyProduct definition and PowerSeries connection            │
│ • Ring axioms transported from PowerSeries                       │
└──────────────────────────────────────────────────────────────────┘
                              ↓
┌──────────────────────────────────────────────────────────────────┐
│ Analysis (lp namespace)                                          │
│ • Membership closure: f, g ∈ ℓ¹ ⟹ f ⋆ g ∈ ℓ¹                    │
│ • Submultiplicativity: ‖f ⋆ g‖ ≤ ‖f‖ · ‖g‖                       │
│ • Norm of identity: ‖1‖ = 1                                      │
└──────────────────────────────────────────────────────────────────┘
```

## References

* [Katznelson, *An Introduction to Harmonic Analysis*], Chapter I
-/

open scoped BigOperators NNReal ENNReal

noncomputable section

/-! ## Cauchy Product (Pure Algebra)

The Cauchy product of sequences `a, b : ℕ → R` is defined as:

  `(a ⋆ b)_n = Σ_{k+l=n} a_k * b_l`

Ring axioms are transported from `PowerSeries R` via the identification
`toPowerSeries (a ⋆ b) = toPowerSeries a * toPowerSeries b`.
-/

namespace CauchyProduct

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- Cauchy product (convolution) of sequences: `(a ⋆ b)_n = Σ_{k+l=n} a_k * b_l`. -/
def apply (a b : ℕ → R) : ℕ → R :=
  fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

scoped notation:70 a:70 " ⋆ " b:71 => apply a b

lemma apply_eq (a b : ℕ → R) (n : ℕ) :
    (a ⋆ b) n = ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2 := rfl

/-! ### PowerSeries Connection

This is the heart of the "transport from PowerSeries" approach.
We show that `CauchyProduct` is definitionally the same as `PowerSeries`
multiplication, then use this to import all ring axioms. -/

/-- Convert a sequence to a formal power series. -/
def toPowerSeries (a : ℕ → R) : PowerSeries R := PowerSeries.mk a

@[simp]
lemma coeff_toPowerSeries (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeries a) = a n := PowerSeries.coeff_mk n a

/-- **Key theorem**: Cauchy product equals PowerSeries multiplication.

    This is the bridge that lets us transport all ring axioms from
    `CommSemiring (PowerSeries R)` without reproving them.

    Proof: Both are defined as `Σ_{k+l=n} a_k b_l`. -/
theorem toPowerSeries_mul (a b : ℕ → R) :
    toPowerSeries (a ⋆ b) = toPowerSeries a * toPowerSeries b := by
  ext n; simp only [apply_eq, toPowerSeries, PowerSeries.coeff_mul, PowerSeries.coeff_mk]

/-! ### Ring Axioms (Transported from PowerSeries)

Each axiom follows the same pattern:
1. State the property for `PowerSeries` (which Mathlib proves)
2. Convert both sides using `toPowerSeries_mul`
3. Extract coefficients to get the sequence equality -/

theorem assoc (a b c : ℕ → R) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  funext n
  have h := congrArg (PowerSeries.coeff n)
    (mul_assoc (toPowerSeries a) (toPowerSeries b) (toPowerSeries c))
  simp only [← toPowerSeries_mul, coeff_toPowerSeries] at h; exact h

theorem left_distrib (a b c : ℕ → R) : a ⋆ (b + c) = a ⋆ b + a ⋆ c := by
  ext n; simp only [Pi.add_apply, apply_eq, mul_add, Finset.sum_add_distrib]

theorem right_distrib (a b c : ℕ → R) : (a + b) ⋆ c = a ⋆ c + b ⋆ c := by
  ext n; simp only [apply_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem zero_mul (a : ℕ → R) : (0 : ℕ → R) ⋆ a = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.zero_mul, Finset.sum_const_zero]

theorem mul_zero (a : ℕ → R) : a ⋆ (0 : ℕ → R) = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.mul_zero, Finset.sum_const_zero]

/-! ### Identity Element

The multiplicative identity is the Kronecker delta: `e_0 = 1, e_n = 0` for `n ≥ 1`.
This corresponds to the power series `1 = 1 + 0·X + 0·X² + ...`. -/

/-- The multiplicative identity sequence: `e_0 = 1, e_n = 0` for `n ≥ 1`. -/
def one : ℕ → R := fun n => if n = 0 then 1 else 0

@[simp] lemma one_zero : (one : ℕ → R) 0 = 1 := rfl
@[simp] lemma one_succ (n : ℕ) : (one : ℕ → R) (n + 1) = 0 := rfl

theorem toPowerSeries_one : toPowerSeries (one : ℕ → R) = 1 := by
  ext n; simp only [coeff_toPowerSeries, one, PowerSeries.coeff_one]

theorem one_mul (a : ℕ → R) : one ⋆ a = a := by
  funext n
  have h := congrArg (PowerSeries.coeff n) (_root_.one_mul (toPowerSeries a))
  rw [coeff_toPowerSeries, ← toPowerSeries_one, ← toPowerSeries_mul, coeff_toPowerSeries] at h
  exact h

theorem mul_one (a : ℕ → R) : a ⋆ one = a := by
  funext n
  have h := congrArg (PowerSeries.coeff n) (_root_.mul_one (toPowerSeries a))
  rw [coeff_toPowerSeries, ← toPowerSeries_one, ← toPowerSeries_mul, coeff_toPowerSeries] at h
  exact h

/-! ### Scalar Multiplication -/

theorem smul_mul (c : R) (a b : ℕ → R) : (c • a) ⋆ b = c • (a ⋆ b) := by
  ext n; simp only [apply_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem comm (a b : ℕ → R) : a ⋆ b = b ⋆ a := by
  funext n
  have h := congrArg (PowerSeries.coeff n)
    (_root_.mul_comm (toPowerSeries a) (toPowerSeries b))
  simp only [← toPowerSeries_mul, coeff_toPowerSeries] at h; exact h

theorem mul_smul (c : R) (a b : ℕ → R) : a ⋆ (c • b) = c • (a ⋆ b) := by
  ext n
  simp only [apply_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro kl _; ring

end CommSemiring

end CauchyProduct


/-! ## ℓ¹ Banach Algebra Structure

This section establishes the Banach algebra structure on `lp (fun _ : ℕ => R) 1`
where R is a NormedRing. The key analytic results are:

1. **Membership closure**: If `f, g ∈ ℓ¹`, then `f ⋆ g ∈ ℓ¹`
2. **Submultiplicativity**: `‖f ⋆ g‖ ≤ ‖f‖ · ‖g‖`
3. **Norm of identity**: `‖1‖ = 1`
-/

section OneNormedRing

variable {R : Type*} [NormedRing R]

instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_refl 1⟩

/-! ### Norm Characterization for ℓ¹ -/

namespace lp

/-- The ℓ¹ norm is `‖f‖ = Σ_n ‖f_n‖`. -/
lemma one_norm_eq_tsum (f : lp (fun _ : ℕ => R) 1) : ‖f‖ = ∑' n, ‖f n‖ := by
  have h := lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) f
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one] at h; exact h

/-- The sum `Σ_n ‖f_n‖` is summable for `f ∈ ℓ¹`. -/
lemma one_summable_norm (f : lp (fun _ : ℕ => R) 1) : Summable (fun n => ‖f n‖) := by
  have := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)] at this
  simpa using this

end lp

/-! ### Cauchy Product Membership

This is the first analytic result: the Cauchy product of two ℓ¹ sequences
is again in ℓ¹. The proof uses Mertens' theorem and the product structure
of summable nonnegative sequences. -/

/-- **Membership closure**: Cauchy product preserves ℓ¹ membership.

    **Proof sketch**:
    1. Apply `Summable.mul_of_nonneg` to get summability on ℕ × ℕ
    2. Use `summable_sum_mul_antidiagonal_of_summable_mul` for antidiagonal sums
    3. Bound Cauchy product norm by product of norms via triangle inequality -/
theorem _root_.Memℓp.one_mul {f g : ∀ _ : ℕ, R} (hf : Memℓp f 1) (hg : Memℓp g 1) :
    Memℓp (CauchyProduct.apply f g) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  -- Extract summability from membership
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)] at hf hg
  simp only [ENNReal.toReal_one, Real.rpow_one] at hf hg
  -- Define the norm sequences
  let φ := fun k => ‖f k‖
  let ψ := fun l => ‖g l‖
  have hφ_nn : ∀ k, 0 ≤ φ k := fun k => norm_nonneg _
  have hψ_nn : ∀ l, 0 ≤ ψ l := fun l => norm_nonneg _
  -- The product of summable nonneg sequences is summable on ℕ × ℕ
  have hprod : Summable (fun x : ℕ × ℕ => φ x.1 * ψ x.2) :=
    Summable.mul_of_nonneg hf hg hφ_nn hψ_nn
  -- And so is its sum over antidiagonals
  have hsum := summable_sum_mul_antidiagonal_of_summable_mul hprod
  apply Summable.of_nonneg_of_le
  · intro n; exact norm_nonneg _
  · intro n
    calc ‖CauchyProduct.apply f g n‖
        = ‖∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2‖ := rfl
      _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1 * g kl.2‖ := norm_sum_le _ _
      _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by
          apply Finset.sum_le_sum; intro kl _; exact norm_mul_le _ _
      _ = ∑ kl ∈ Finset.antidiagonal n, φ kl.1 * ψ kl.2 := rfl
  · exact hsum

/-- The identity element has finite ℓ¹ norm. -/
theorem _root_.one_memℓp_one : Memℓp (CauchyProduct.one : ℕ → R) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have h : (fun n => ‖(CauchyProduct.one : ℕ → R) n‖) =
      fun n => if n = 0 then ‖(1 : R)‖ else 0 := by
    ext n; cases n with
    | zero => simp only [CauchyProduct.one_zero, ↓reduceIte]
    | succ n =>
        simp only [CauchyProduct.one_succ, norm_zero,
          Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  rw [h]
  exact summable_of_ne_finset_zero (s := {0}) (fun n hn => by simp at hn; simp [hn])

/-! ### Multiplication and Ring Structure -/

namespace lp

instance oneMul : Mul (lp (fun _ : ℕ => R) 1) where
  mul f g := ⟨CauchyProduct.apply (⇑f) (⇑g), f.property.one_mul g.property⟩

instance oneOne : One (lp (fun _ : ℕ => R) 1) where
  one := ⟨CauchyProduct.one, one_memℓp_one⟩

@[simp]
theorem one_coeFn_mul (f g : lp (fun _ : ℕ => R) 1) :
    ⇑(f * g) = CauchyProduct.apply (⇑f) (⇑g) := rfl

@[simp]
theorem one_coeFn_one : ⇑(1 : lp (fun _ : ℕ => R) 1) = CauchyProduct.one := rfl

instance oneRing : Ring (lp (fun _ : ℕ => R) 1) where
  mul_assoc := fun f g h => lp.ext <| CauchyProduct.assoc (⇑f) (⇑g) (⇑h)
  one_mul := fun f => lp.ext <| CauchyProduct.one_mul (⇑f)
  mul_one := fun f => lp.ext <| CauchyProduct.mul_one (⇑f)
  left_distrib := fun f g h => lp.ext <| CauchyProduct.left_distrib (⇑f) (⇑g) (⇑h)
  right_distrib := fun f g h => lp.ext <| CauchyProduct.right_distrib (⇑f) (⇑g) (⇑h)
  zero_mul := fun f => lp.ext <| CauchyProduct.zero_mul (⇑f)
  mul_zero := fun f => lp.ext <| CauchyProduct.mul_zero (⇑f)

-- Note: The power operation `f ^ n` is automatically defined by the `Ring` instance
-- as repeated Cauchy product multiplication. Unlike the `p = ∞` case where multiplication
-- is pointwise, here `f ^ 0 = 1` is the Kronecker delta `[1, 0, 0, ...]`, not the
-- constant sequence `[1, 1, 1, ...]`. There is no coercion lemma `⇑(f ^ n) = (⇑f) ^ n`
-- because Pi-power and Cauchy-power are fundamentally different operations.

/-! ### Submultiplicativity (Key Analytic Property)

This is the defining property of a Banach algebra: `‖f * g‖ ≤ ‖f‖ * ‖g‖`.
The proof uses Mertens' theorem to exchange sum order. -/

/-- **Submultiplicativity**: `‖f * g‖_1 ≤ ‖f‖_1 · ‖g‖_1`

    This makes ℓ¹ a Banach algebra. The proof uses:
    1. Mertens' theorem (`tsum_mul_tsum_eq_tsum_sum_antidiagonal`) to exchange sum order
    2. Triangle inequality to bound Cauchy product by product of norms -/
theorem one_norm_mul_le (f g : lp (fun _ : ℕ => R) 1) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [one_norm_eq_tsum, one_norm_eq_tsum f, one_norm_eq_tsum g]
  -- Define the norm sequences
  let φ := fun k => ‖f k‖
  let ψ := fun l => ‖g l‖
  have hφ_nn : ∀ k, 0 ≤ φ k := fun k => norm_nonneg _
  have hψ_nn : ∀ l, 0 ≤ ψ l := fun l => norm_nonneg _
  have hφ : Summable φ := one_summable_norm f
  have hψ : Summable ψ := one_summable_norm g
  -- The product of summable nonneg sequences is summable on ℕ × ℕ
  have hprod : Summable (fun x : ℕ × ℕ => φ x.1 * ψ x.2) :=
    Summable.mul_of_nonneg hφ hψ hφ_nn hψ_nn
  -- Rewrite product of tsum as tsum over antidiagonals (Mertens)
  rw [hφ.tsum_mul_tsum_eq_tsum_sum_antidiagonal hψ hprod]
  -- Now compare term-by-term
  refine Summable.tsum_le_tsum ?_ ?_ (summable_sum_mul_antidiagonal_of_summable_mul hprod)
  · intro n
    calc ‖(f * g) n‖
        = ‖∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2‖ := rfl
      _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1 * g kl.2‖ := norm_sum_le _ _
      _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by
          apply Finset.sum_le_sum; intro kl _; exact norm_mul_le _ _
      _ = ∑ kl ∈ Finset.antidiagonal n, φ kl.1 * ψ kl.2 := rfl
  · -- Summability of ‖(f*g)_n‖
    have hmem := f.property.one_mul g.property
    rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)] at hmem
    simpa using hmem

instance oneNormedRing : NormedRing (lp (fun _ : ℕ => R) 1) :=
  { lp.normedAddCommGroup, lp.oneRing with
    dist_eq := fun _ _ => rfl
    norm_mul_le := one_norm_mul_le }

/-! ### NormOneClass -/

variable [NormOneClass R]

theorem one_norm_one : ‖(1 : lp (fun _ : ℕ => R) 1)‖ = 1 := by
  rw [one_norm_eq_tsum]
  have h : (fun n => ‖(1 : lp (fun _ : ℕ => R) 1) n‖) = fun n => if n = 0 then 1 else 0 := by
    ext n; cases n with
    | zero => rw [one_coeFn_one, CauchyProduct.one_zero, norm_one]; simp only [↓reduceIte]
    | succ n =>
        rw [one_coeFn_one, CauchyProduct.one_succ, _root_.norm_zero]
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  rw [h, tsum_ite_eq]

instance oneNormOneClass : NormOneClass (lp (fun _ : ℕ => R) 1) where
  norm_one := one_norm_one

end lp

end OneNormedRing

section OneNormedCommRing

variable {R : Type*} [NormedCommRing R] [NormOneClass R]

namespace lp

instance oneNormedCommRing : NormedCommRing (lp (fun _ : ℕ => R) 1) where
  mul_comm f g := lp.ext <| CauchyProduct.comm (⇑f) (⇑g)

/-! ### Scalar Multiplication Compatibility

These instances establish that scalar multiplication by R is compatible with
ring multiplication. The full algebra structure over a NormedField 𝕜 is
established in the `OneAlgebra` section. -/

instance one_isScalarTower : IsScalarTower R (lp (fun _ : ℕ => R) 1) (lp (fun _ : ℕ => R) 1) :=
  ⟨fun r f g => lp.ext <| CauchyProduct.smul_mul r (⇑f) (⇑g)⟩

instance one_smulCommClass : SMulCommClass R (lp (fun _ : ℕ => R) 1) (lp (fun _ : ℕ => R) 1) :=
  ⟨fun r f g => lp.ext <| (CauchyProduct.mul_smul r (⇑f) (⇑g)).symm⟩

end lp

end OneNormedCommRing

section OneAlgebra

variable {𝕜 : Type*} {R : Type*}
variable [NormedField 𝕜] [NormedCommRing R] [NormOneClass R] [NormedAlgebra 𝕜 R]

namespace lp

/-! ### Algebra Structure

For a NormedField 𝕜 acting on R via NormedAlgebra 𝕜 R, we establish the algebra
structure on ℓ¹. The key is that scalar multiplication by 𝕜 commutes with the
Cauchy product multiplication. -/

omit [NormOneClass R] in
/-- Scalar multiplication satisfies `(c • f) * g = c • (f * g)` for Cauchy product. -/
theorem one_smul_mul_assoc (c : 𝕜) (f g : lp (fun _ : ℕ => R) 1) :
    (c • f) * g = c • (f * g) := Subtype.ext <| funext fun n => by
  simp only [lp.coeFn_smul, one_coeFn_mul, Pi.smul_apply, CauchyProduct.apply_eq, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro kl _
  exact smul_mul_assoc c (f kl.1) (g kl.2)

omit [NormOneClass R] in
/-- Scalar multiplication satisfies `f * (c • g) = c • (f * g)` for Cauchy product. -/
theorem one_mul_smul_comm (c : 𝕜) (f g : lp (fun _ : ℕ => R) 1) :
    f * (c • g) = c • (f * g) := Subtype.ext <| funext fun n => by
  simp only [lp.coeFn_smul, one_coeFn_mul, Pi.smul_apply, CauchyProduct.apply_eq, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro kl _
  exact mul_smul_comm c (f kl.1) (g kl.2)

/-- Scalar multiplication by 𝕜 is associative with Cauchy product multiplication. -/
instance one_isScalarTower' : IsScalarTower 𝕜 (lp (fun _ : ℕ => R) 1) (lp (fun _ : ℕ => R) 1) :=
  ⟨fun c f g => one_smul_mul_assoc c f g⟩

/-- Scalar multiplication by 𝕜 commutes with Cauchy product multiplication. -/
instance one_smulCommClass' : SMulCommClass 𝕜 (lp (fun _ : ℕ => R) 1) (lp (fun _ : ℕ => R) 1) :=
  ⟨fun c f g => (one_mul_smul_comm c f g).symm⟩

instance oneAlgebra : Algebra 𝕜 (lp (fun _ : ℕ => R) 1) :=
  Algebra.ofModule one_smul_mul_assoc one_mul_smul_comm

instance oneNormedAlgebra : NormedAlgebra 𝕜 (lp (fun _ : ℕ => R) 1) where
  norm_smul_le := norm_smul_le

end lp

end OneAlgebra

end

/-!
## Implementation Notes

### Proofs Complete

All analytic proofs are complete. The key techniques are:

1. **`Memℓp.one_mul`**: Membership closure for Cauchy product
   - Uses `Summable.mul_of_nonneg` for product of summable sequences
   - Uses `summable_sum_mul_antidiagonal_of_summable_mul` for antidiagonal sums
   - Triangle inequality bounds Cauchy product by product of norms

2. **`lp.one_norm_mul_le`**: Submultiplicativity
   - Uses `tsum_mul_tsum_eq_tsum_sum_antidiagonal` (Mertens)
   - Compares term-by-term via `Summable.tsum_le_tsum`

### Generalization Axes

This file handles the unweighted case. Potential generalizations:

1. **Index set**: ℕ → general additive monoid G (group algebra completion)
2. **Coefficient ring**: NormedRing → general seminormed ring
3. **Weight function**: Add submultiplicative weight ν : G → ℝ≥0 with ν(a+b) ≤ ν(a)·ν(b)

### Integration with Mathlib

This file is designed as a drop-in extension to `Mathlib.Analysis.Normed.Lp.lpSpace`.
The naming conventions follow the existing `infty*` instances (e.g., `inftyNormedRing`),
using the `one*` prefix for p = 1 instances.

### Dependencies

Required imports beyond `lpSpace`:
- `Mathlib.RingTheory.PowerSeries.Basic` (for ring axiom transport)
- `Mathlib.Algebra.BigOperators.NatAntidiagonal` (for antidiagonal sums)

The key lemmas from Mathlib used:
- `Summable.mul_of_nonneg`: Product of summable nonneg sequences is summable
- `summable_sum_mul_antidiagonal_of_summable_mul`: Antidiagonal sum is summable
- `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`: Mertens theorem
-/
