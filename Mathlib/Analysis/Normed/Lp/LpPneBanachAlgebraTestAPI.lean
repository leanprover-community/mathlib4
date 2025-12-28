/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Analysis.Normed.Lp.DiscreteConvolutionTestAPI
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Banach Algebra Structure on ℓ¹ via Discrete Convolution

This file establishes typeclass instances for the Banach algebra structure on
`lp (fun _ : M => R) 1` using the discrete convolution from `DiscreteConvolution.lean`.

## Main Instances

### Ring Structure
* `lp.oneRing`: `lp (fun _ : M => R) 1` is a `Ring`
* `lp.oneNormedRing`: `lp (fun _ : M => R) 1` is a `NormedRing`

### Algebra Structure
* `lp.oneNormOneClass`: `‖1‖ = 1` (requires `NormOneClass R`)
* `lp.oneNormedCommRing`: `lp (fun _ : M => R) 1` is a `NormedCommRing` (when R, M commutative)
* `lp.oneNormedAlgebra`: `lp (fun _ : M => R) 1` is a `NormedAlgebra 𝕜`

## Design Notes

This file builds on `DiscreteConvolution.lean` which provides:
* `DiscreteConvolution.convolution`: the convolution operation `f ⋆ g`
* `DiscreteConvolution.delta`: the identity element `δ₁`
* Algebraic properties: `convolution_assoc`, `delta_convolution`,
                        `convolution_delta`, `convolution_comm`
* ℓ¹ properties: `lp.one_convolution_memℓp`, `lp.one_norm_mul_le`, `lp.one_delta_memℓp`

The ring axioms follow directly from the algebraic properties of discrete convolution.

## Connection to Finite Antidiagonals

For types with `HasAntidiagonal` (e.g., `ℕ`, `ℕ × ℕ`), the fiber `mulFiber x` is finite
and the `tsum` in discrete convolution reduces to a finite sum over the antidiagonal.
See `CauchyProduct` namespace for the finite-sum formulation.
-/

@[expose] public section

open scoped BigOperators NNReal ENNReal DiscreteConvolution

open Finset DiscreteConvolution

noncomputable section

/-! ## CauchyProduct: Finite Antidiagonal Convolution

For types with `HasAntidiagonal`, convolution is a finite sum. This is equivalent to
`DiscreteConvolution.convolution` when fibers are finite. -/

namespace CauchyProduct

variable {G : Type*} {R : Type*}

section Product

variable [AddCommMonoid G] [HasAntidiagonal G] [Semiring R]

/-- Cauchy product (convolution) via finite antidiagonal sum. -/
def apply (a b : G → R) : G → R :=
  fun n => ∑ kl ∈ antidiagonal n, a kl.1 * b kl.2

/-- Notation for Cauchy product convolution. -/
scoped notation:70 a:70 " ⋆ " b:71 => apply a b

lemma apply_eq (a b : G → R) (n : G) :
    (a ⋆ b) n = ∑ kl ∈ antidiagonal n, a kl.1 * b kl.2 := rfl

/-! #### Ring Axioms -/

lemma left_distrib (a b c : G → R) : a ⋆ (b + c) = a ⋆ b + a ⋆ c := by
  ext n; simp only [Pi.add_apply, apply_eq, mul_add, sum_add_distrib]

lemma right_distrib (a b c : G → R) : (a + b) ⋆ c = a ⋆ c + b ⋆ c := by
  ext n; simp only [apply_eq, Pi.add_apply, add_mul, sum_add_distrib]

@[simp] lemma zero_mul (a : G → R) : (0 : G → R) ⋆ a = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.zero_mul, sum_const_zero]

@[simp] lemma mul_zero (a : G → R) : a ⋆ (0 : G → R) = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.mul_zero, sum_const_zero]

/-! #### Associativity via bijection on triple sums -/

theorem assoc (a b c : G → R) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  ext n
  simp only [apply_eq, sum_mul, mul_sum]
  rw [sum_sigma', sum_sigma']
  refine sum_nbij'
    (fun x => ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
    (fun x => ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩)
    ?_ ?_ ?_ ?_ ?_
  all_goals (intro x hx; simp_all only [mem_sigma, mem_antidiagonal, Prod.mk.eta, Sigma.eta])
  iterate 2 exact ⟨by rw [← hx.1, ← hx.2, add_assoc], trivial⟩
  obtain ⟨⟨fst, snd_1⟩, ⟨fst_1, snd⟩⟩ := x
  exact mul_assoc _ _ _

theorem smul_mul (c : R) (a b : G → R) : (c • a) ⋆ b = c • (a ⋆ b) := by
  ext n; simp only [apply_eq, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

end Product

/-! ### Identity Laws -/

section Identity

variable [AddCommMonoid G] [DecidableEq G] [Semiring R]

/-- The multiplicative identity: `e_0 = 1, e_g = 0` for `g ≠ 0`. -/
def one : G → R := Pi.single 0 1

@[simp] lemma one_apply_zero : (one : G → R) 0 = 1 := Pi.single_eq_same 0 1

lemma one_apply_ne {g : G} (hg : g ≠ 0) : (one : G → R) g = 0 := Pi.single_eq_of_ne hg 1

end Identity

section IdentityIntidiagonal

variable [AddCommMonoid G] [DecidableEq G] [HasAntidiagonal G] [Semiring R]

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
  rw [sum_eq_single (n, 0)]
  · simp only [Pi.single_eq_same, _root_.mul_one]
  · intro ⟨a, b⟩ hab1 hab2
    simp_all only [mem_antidiagonal, Pi.single_apply]
    simp_all only [ne_eq, Prod.mk.injEq, not_and, mul_ite,
      _root_.mul_one, MulZeroClass.mul_zero, ite_eq_right_iff]
    intro; simp_all only [add_zero, not_true_eq_false, imp_false]
  · simp only [mem_antidiagonal, add_zero, not_true_eq_false,
      Pi.single_eq_same, _root_.mul_one, IsEmpty.forall_iff]

end IdentityIntidiagonal

/-! ### Commutativity -/

section Comm

variable [AddCommMonoid G] [HasAntidiagonal G] [CommSemiring R]

theorem comm (a b : G → R) : a ⋆ b = b ⋆ a := by
  ext n; simp only [apply_eq]
  rw [← Finset.map_swap_antidiagonal (n := n), Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.fst_swap, Prod.snd_swap,
      map_swap_antidiagonal, mul_comm]

theorem mul_smul (c : R) (a b : G → R) : a ⋆ (c • b) = c • (a ⋆ b) := by
  ext n; simp only [apply_eq, Pi.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl; intro kl _; ring

end Comm

end CauchyProduct


/-! ## ℓ¹ Ring Instances (ℕ-specific)

Ring and NormedRing instances for `lp (fun _ : ℕ => R) 1` using CauchyProduct
(finite antidiagonal sums). -/

section LpOneNormedRing

variable {R : Type*} [NormedRing R]

/-! ### Membership Closure under Cauchy Product -/

lemma Memℓp.summable_norm {f : ℕ → R} (hf : Memℓp f 1) : Summable (‖f ·‖) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)] at hf; simpa using hf

/-- Cauchy product of ℓ¹ functions is in ℓ¹. -/
theorem Memℓp.one_mul {f g : ℕ → R} (hf : Memℓp f 1) (hg : Memℓp g 1) :
    Memℓp (CauchyProduct.apply f g) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  let φ := fun k => ‖f k‖
  let ψ := fun l => ‖g l‖
  have hprod : Summable (fun x : ℕ × ℕ => φ x.1 * ψ x.2) :=
    hf.summable_norm.mul_of_nonneg hg.summable_norm
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (summable_sum_mul_antidiagonal_of_summable_mul hprod)
  intro n
  exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_mul_le _ _)

/-- The identity element `Pi.single 0 1` is in ℓ¹. -/
theorem one_memℓp_one : Memℓp (CauchyProduct.one : ℕ → R) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have h : (fun n => ‖(CauchyProduct.one : ℕ → R) n‖) =
      fun n => if n = 0 then ‖(1 : R)‖ else 0 := by
    ext n; cases n with
    | zero => simp [CauchyProduct.one_apply_zero]
    | succ n => simp [CauchyProduct.one_apply_ne (Nat.succ_ne_zero n), norm_zero]
  rw [h]
  exact summable_of_ne_finset_zero (s := {0})
    (by simp_all only [mem_singleton, ↓reduceIte, implies_true])

/-! ### lp Instances -/

namespace lp

/-- The ℓ¹ norm equals the sum of norms (as a tsum). -/
theorem one_norm_eq_tsum' (f : lp (fun _ : ℕ => R) 1) :
    ‖f‖ = ∑' n, ‖f n‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) f]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]

/-- The norm sequence of an ℓ¹ function is summable. -/
theorem one_summable_norm' (f : lp (fun _ : ℕ => R) 1) : Summable (fun n => ‖f n‖) := by
  have := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)] at this
  simpa using this

instance oneMul : Mul (lp (fun _ : ℕ => R) 1) where
  mul f g := ⟨CauchyProduct.apply (⇑f) (⇑g), f.property.one_mul g.property⟩

@[simp]
theorem one_coeFn_mul (f g : lp (fun _ : ℕ => R) 1) :
    ⇑(f * g) = CauchyProduct.apply (⇑f) (⇑g) := rfl

/-- **Submultiplicativity**: `‖f * g‖_1 ≤ ‖f‖_1 · ‖g‖_1` -/
theorem one_norm_mul_le' (f g : lp (fun _ : ℕ => R) 1) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [one_norm_eq_tsum', one_norm_eq_tsum' f, one_norm_eq_tsum' g]
  let φ := fun k => ‖f k‖
  let ψ := fun l => ‖g l‖
  have hφ : Summable φ := one_summable_norm' f
  have hψ : Summable ψ := one_summable_norm' g
  have hprod : Summable (fun x : ℕ × ℕ => φ x.1 * ψ x.2) :=
    hφ.mul_of_nonneg hψ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  rw [hφ.tsum_mul_tsum_eq_tsum_sum_antidiagonal hψ hprod]
  refine Summable.tsum_le_tsum ?_ ?_ (summable_sum_mul_antidiagonal_of_summable_mul hprod)
  · exact fun n => (norm_sum_le (antidiagonal n) _).trans
      (sum_le_sum fun kl _ => norm_mul_le (f kl.1) (g kl.2))
  · simpa using (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mp
      (f.property.one_mul g.property)

instance oneOne : One (lp (fun _ : ℕ => R) 1) where
  one := ⟨CauchyProduct.one, _root_.one_memℓp_one⟩

@[simp]
lemma one_coeFn_one : ⇑(1 : lp (fun _ : ℕ => R) 1) = CauchyProduct.one := rfl

instance oneRing : Ring (lp (fun _ : ℕ => R) 1) where
  mul_assoc f g h := lp.ext <| CauchyProduct.assoc (⇑f) (⇑g) (⇑h)
  one_mul f := lp.ext <| CauchyProduct.one_mul (⇑f)
  mul_one f := lp.ext <| CauchyProduct.mul_one (⇑f)
  left_distrib f g h := lp.ext <| CauchyProduct.left_distrib (⇑f) (⇑g) (⇑h)
  right_distrib f g h := lp.ext <| CauchyProduct.right_distrib (⇑f) (⇑g) (⇑h)
  zero_mul f := lp.ext <| CauchyProduct.zero_mul (⇑f)
  mul_zero f := lp.ext <| CauchyProduct.mul_zero (⇑f)

instance oneNormedRing : NormedRing (lp (fun _ : ℕ => R) 1) :=
  { lp.normedAddCommGroup, lp.oneRing with
    dist_eq := fun _ _ => rfl
    norm_mul_le := one_norm_mul_le' }

end lp

end LpOneNormedRing

section LpOneNormOneClass

variable {R : Type*} [NormedRing R] [NormOneClass R]

namespace lp

theorem one_norm_one : ‖(1 : lp (fun _ : ℕ => R) 1)‖ = 1 := by
  rw [one_norm_eq_tsum']
  have h : (fun n => ‖(1 : lp (fun _ : ℕ => R) 1) n‖) = fun n => if n = 0 then 1 else 0 := by
    ext n; cases n with
    | zero => rw [one_coeFn_one, CauchyProduct.one_apply_zero, norm_one]; simp only [↓reduceIte]
    | succ n =>
        rw [one_coeFn_one, CauchyProduct.one_apply_ne (Nat.succ_ne_zero n), _root_.norm_zero]
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  rw [h, tsum_ite_eq]

instance oneNormOneClass : NormOneClass (lp (fun _ : ℕ => R) 1) where
  norm_one := one_norm_one

end lp

end LpOneNormOneClass

section LpOneNormedCommRing

variable {R : Type*} [NormedCommRing R]

namespace lp

instance oneNormedCommRing : NormedCommRing (lp (fun _ : ℕ => R) 1) where
  mul_comm f g := lp.ext <| CauchyProduct.comm (⇑f) (⇑g)

/-! ### Scalar Multiplication Compatibility -/

instance one_isScalarTower : IsScalarTower R (lp (fun _ : ℕ => R) 1) (lp (fun _ : ℕ => R) 1) :=
  ⟨fun r f g => lp.ext <| CauchyProduct.smul_mul r (⇑f) (⇑g)⟩

instance one_smulCommClass : SMulCommClass R (lp (fun _ : ℕ => R) 1) (lp (fun _ : ℕ => R) 1) :=
  ⟨fun r f g => lp.ext <| (CauchyProduct.mul_smul r (⇑f) (⇑g)).symm⟩

end lp

end LpOneNormedCommRing

section LpOneNormedAlgebra

variable {𝕜 : Type*} {R : Type*}
variable [NormedField 𝕜] [NormedCommRing R] [NormedAlgebra 𝕜 R]

namespace lp

/-- Scalar multiplication satisfies `(c • f) * g = c • (f * g)`. -/
theorem one_smul_mul_assoc (c : 𝕜) (f g : lp (fun _ : ℕ => R) 1) :
    (c • f) * g = c • (f * g) := Subtype.ext <| funext fun n => by
  simp only [lp.coeFn_smul, one_coeFn_mul, Pi.smul_apply, CauchyProduct.apply_eq, smul_sum]
  apply sum_congr rfl
  intro kl _
  exact smul_mul_assoc c (f kl.1) (g kl.2)

/-- Scalar multiplication satisfies `f * (c • g) = c • (f * g)`. -/
theorem one_mul_smul_comm (c : 𝕜) (f g : lp (fun _ : ℕ => R) 1) :
    f * (c • g) = c • (f * g) := Subtype.ext <| funext fun n => by
  simp only [lp.coeFn_smul, one_coeFn_mul, Pi.smul_apply, CauchyProduct.apply_eq, smul_sum]
  apply sum_congr rfl
  intro kl _
  exact mul_smul_comm c (f kl.1) (g kl.2)

instance one_isScalarTower' : IsScalarTower 𝕜 (lp (fun _ : ℕ => R) 1) (lp (fun _ : ℕ => R) 1) :=
  ⟨fun c f g => one_smul_mul_assoc c f g⟩

instance one_smulCommClass' : SMulCommClass 𝕜 (lp (fun _ : ℕ => R) 1) (lp (fun _ : ℕ => R) 1) :=
  ⟨fun c f g => (one_mul_smul_comm c f g).symm⟩

instance oneAlgebra : Algebra 𝕜 (lp (fun _ : ℕ => R) 1) :=
  Algebra.ofModule one_smul_mul_assoc one_mul_smul_comm

instance oneNormedAlgebra : NormedAlgebra 𝕜 (lp (fun _ : ℕ => R) 1) where
  norm_smul_le := norm_smul_le

end lp

end LpOneNormedAlgebra

end

/-!
## Implementation Notes

### Two Approaches to Convolution

1. **CauchyProduct** (this file): Finite sums over `HasAntidiagonal`. Works for ℕ, ℕ × ℕ, etc.
   Ring axioms proven via finite sum manipulations.

2. **DiscreteConvolution**: Infinite sums (`tsum`) over `mulFiber`. Works for any monoid.
   Ring axioms require summability hypotheses.

For ℓ¹(ℕ, R), the CauchyProduct approach is simpler since antidiagonals are finite.
DiscreteConvolution.lean provides the general theory for monoids without HasAntidiagonal.

### Generalization Path

To extend beyond ℕ to general monoids M:
* Use `DiscreteConvolution.lp.oneMul` and `DiscreteConvolution.lp.oneOne`
* Prove ring axioms using `convolution_assoc`, `delta_convolution`, `convolution_delta`
* Requires showing `ConvolutionExists` for ℓ¹ functions (done in DiscreteConvolution)
-/
