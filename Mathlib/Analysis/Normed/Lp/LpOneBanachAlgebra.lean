/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Banach Algebra Structure on ℓ¹ via Cauchy Product

This file establishes that `lp (fun _ : G => R) 1` is a ring when equipped with the
Cauchy product (discrete convolution), for any `AddMonoid G` with `HasAntidiagonal G`.
For the special case `G = ℕ`, we establish the full Banach algebra structure.

Note: This is the *discrete* Cauchy product over finite antidiagonals, not the
measure-theoretic convolution from `MeasureTheory.convolution`.

## Main Definitions

* `CauchyProduct.apply`: Cauchy product `(a * b)_n = Σ_{k+l=n} a_k * b_l`
* `CauchyProduct.one`: Identity element `Pi.single 0 1`
* `CauchyProduct.npow`: Natural number power under Cauchy product

## Main Results

### Cauchy Product (General `[AddMonoid G] [HasAntidiagonal G]`)
* `CauchyProduct.assoc`: Associativity (no commutativity required)
* `CauchyProduct.one_mul`, `CauchyProduct.mul_one`: Identity laws
* `CauchyProduct.left_distrib`, `CauchyProduct.right_distrib`: Distributivity
* `CauchyProduct.smul_mul`: Left scalar multiplication compatibility

### Cauchy Product (Commutative `[AddCommMonoid G] [HasAntidiagonal G]`)
* `CauchyProduct.comm`: Commutativity (when `R` is commutative)
* `CauchyProduct.mul_smul`: Right scalar multiplication compatibility

### Membership (G = ℕ)
* `Memℓp.one_mul`: Cauchy product preserves ℓ¹ membership
* `one_memℓp_one`: The identity element is in ℓ¹
* `Memℓp.one_pow`: Powers preserve ℓ¹ membership
* `natCast_memℓp_one`, `intCast_memℓp_one`: Cast membership

### Banach Algebra Structure (G = ℕ)
* `lp.oneRing`: `Ring` instance
* `lp.oneNormedRing`: `NormedRing` instance
* `lp.oneNormedCommRing`: `NormedCommRing` instance (when `R` is commutative)
* `lp.oneNormedAlgebra`: `NormedAlgebra 𝕜` instance
* `lp.oneNormOneClass`: `‖1‖ = 1` (requires `NormOneClass R`)
* `lp.one_norm_mul_le`: Submultiplicativity `‖f * g‖ ≤ ‖f‖ * ‖g‖`

## Design Notes

The Cauchy product uses `Finset.antidiagonal` from the `HasAntidiagonal` typeclass. This covers:
- ℕ (univariate power series multiplication)
- ℕ × ℕ, ℕ^k (multivariate)
- `α →₀ ℕ` (finitely supported functions)
- Potentially `List α` with append (non-commutative)

But NOT ℤ, whose antidiagonals are infinite.

The ℓ¹ analytic estimates are ℕ-specific because Mathlib's `tsum_mul_tsum_eq_tsum_sum_antidiagonal`
and `summable_sum_mul_antidiagonal_of_summable_mul` are proven for ℕ.

The ring axioms are proven directly via finite sum manipulations. Associativity
uses `Finset.sum_nbij'` to establish a bijection between the two triple-sum indexing
schemes `⟨(i+j, k), (i, j)⟩ ↔ ⟨(i, j+k), (j, k)⟩`
this only requires `add_assoc`, not commutativity.
-/

@[expose] public section

open scoped BigOperators NNReal ENNReal

open Finset

noncomputable section

/-! ## Cauchy Product (Pure Algebra)

The Cauchy product of functions `a, b : G → R` is defined as:

  `(a * b)_n = Σ_{k+l=n} a_k * b_l`

where the sum is over the antidiagonal `{(k, l) : k + l = n}`.
-/

namespace CauchyProduct

variable {G : Type*} {R : Type*}

/-! ### Identity Element

The multiplicative identity is `Pi.single 0 1`: the function that is 1 at 0 and 0 elsewhere.
This section requires only `DecidableEq G` and `AddMonoid G` (for the zero element). -/

section One

variable [AddMonoid G] [DecidableEq G] [Semiring R]

/-- The multiplicative identity: `e_0 = 1, e_g = 0` for `g ≠ 0`. -/
def one : G → R := Pi.single 0 1

@[simp] lemma one_apply_zero : (one : G → R) 0 = 1 := Pi.single_eq_same 0 1

lemma one_apply_ne {g : G} (hg : g ≠ 0) : (one : G → R) g = 0 := Pi.single_eq_of_ne hg 1

end One

/-! ### Cauchy Product Operations

This section requires `HasAntidiagonal G` for the finite sums over antidiagonals. -/

section Product

variable [AddMonoid G] [HasAntidiagonal G] [Semiring R]

/-- Cauchy product (convolution) of functions: `(a * b)_n = Σ_{k+l=n} a_k * b_l`. -/
def apply (a b : G → R) : G → R :=
  fun n => ∑ kl ∈ antidiagonal n, a kl.1 * b kl.2

/-- Notation for Cauchy product: `a ⋆ b` denotes the convolution of functions `a` and `b`. -/
scoped notation:70 a:70 " ⋆ " b:71 => apply a b

lemma apply_eq (a b : G → R) (n : G) :
    (a ⋆ b) n = ∑ kl ∈ antidiagonal n, a kl.1 * b kl.2 := rfl

/-! #### Ring Axioms (without identity) -/

lemma left_distrib (a b c : G → R) : a ⋆ (b + c) = a ⋆ b + a ⋆ c := by
  ext n; simp only [Pi.add_apply, apply_eq, mul_add, sum_add_distrib]

lemma right_distrib (a b c : G → R) : (a + b) ⋆ c = a ⋆ c + b ⋆ c := by
  ext n; simp only [apply_eq, Pi.add_apply, add_mul, sum_add_distrib]

@[simp] lemma zero_mul (a : G → R) : (0 : G → R) ⋆ a = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.zero_mul, sum_const_zero]

@[simp] lemma mul_zero (a : G → R) : a ⋆ (0 : G → R) = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.mul_zero, sum_const_zero]

/-! #### Associativity

Both `((a ⋆ b) ⋆ c)_n` and `(a ⋆ (b ⋆ c))_n` sum over all triples `(i, j, k)` with
`i + j + k = n`. We use `Finset.sum_nbij'` to establish the equality via bijection
between the two indexing schemes. This proof does not require commutativity. -/

theorem assoc (a b c : G → R) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  ext n
  simp only [apply_eq, sum_mul, mul_sum]
  rw [sum_sigma', sum_sigma']
  -- x = ⟨(ij, k), (i, j)⟩ on LHS, x = ⟨(i, jk), (j, k)⟩ on RHS
  refine sum_nbij'
    (fun x => ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
    (fun x => ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩)
    ?_ ?_ ?_ ?_ ?_
  all_goals (intro x hx; simp_all only [mem_sigma, mem_antidiagonal, Prod.mk.eta, Sigma.eta])
  iterate 2 exact ⟨by rw [← hx.1, ← hx.2, add_assoc], trivial⟩
  obtain ⟨⟨fst, snd_1⟩, ⟨fst_1, snd⟩⟩ := x
  dsimp at *
  exact mul_assoc _ _ _

/-! #### Scalar Multiplication -/

theorem smul_mul (c : R) (a b : G → R) : (c • a) ⋆ b = c • (a ⋆ b) := by
  ext n; simp only [apply_eq, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

end Product

/-! ### Identity Laws

These require both `DecidableEq G` (for `one`) and `HasAntidiagonal G` (for `⋆`).
Only `AddMonoid` is needed — we use `zero_add` and `add_zero`, not commutativity. -/

section Identity

variable [AddMonoid G] [DecidableEq G] [HasAntidiagonal G] [Semiring R]

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
    intro
    simp_all only [add_zero, not_true_eq_false, imp_false]
  · simp only [mem_antidiagonal, add_zero, not_true_eq_false,
      Pi.single_eq_same, _root_.mul_one, IsEmpty.forall_iff]


end Identity

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

/-! ### Powers -/

section Pow

variable [AddMonoid G] [DecidableEq G] [HasAntidiagonal G] [Semiring R]

/-- Natural number power under Cauchy product. -/
def npow : ℕ → (G → R) → (G → R)
  | 0, _ => one
  | n + 1, a => npow n a ⋆ a

@[simp] theorem npow_zero (a : G → R) : npow 0 a = one := rfl
@[simp] theorem npow_succ (n : ℕ) (a : G → R) : npow (n + 1) a = npow n a ⋆ a := rfl

end Pow

end CauchyProduct


/-! ## ℓ¹ Banach Algebra Structure (G = ℕ)

This section establishes the Banach algebra structure on `lp (fun _ : ℕ => R) 1`.
The key analytic results are:

1. **Membership closure**: If `f, g ∈ ℓ¹`, then `f ⋆ g ∈ ℓ¹`
2. **Submultiplicativity**: `‖f ⋆ g‖ ≤ ‖f‖ · ‖g‖`
3. **Norm of identity**: `‖1‖ = 1` (requires `NormOneClass R`)
-/

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

/-- Powers (under Cauchy product) preserve ℓ¹ membership. -/
theorem Memℓp.one_pow {f : ℕ → R} (hf : Memℓp f 1) (n : ℕ) :
    Memℓp (CauchyProduct.npow n f) 1 := by
  induction n with
  | zero => exact one_memℓp_one
  | succ n ih => exact ih.one_mul hf

/-- Natural number cast is in ℓ¹ (as `n • 1` under Cauchy product). -/
theorem natCast_memℓp_one (n : ℕ) : Memℓp (n • CauchyProduct.one : ℕ → R) 1 := by
  induction n with
  | zero =>
    simp only [zero_nsmul]
    exact zero_memℓp
  | succ n ih =>
    simp only [add_smul, one_smul]
    exact ih.add one_memℓp_one

/-- Integer cast is in ℓ¹ (as `z • 1` under Cauchy product). -/
theorem intCast_memℓp_one (z : ℤ) : Memℓp (z • CauchyProduct.one : ℕ → R) 1 := by
  cases z with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, natCast_zsmul]
    exact natCast_memℓp_one n
  | negSucc n =>
    simp only [negSucc_zsmul]
    exact (natCast_memℓp_one (n + 1)).neg

/-! ### lp Instances -/

namespace lp

/-- The ℓ¹ norm equals the sum of norms (as a tsum). -/
theorem one_norm_eq_tsum (f : lp (fun _ : ℕ => R) 1) :
    ‖f‖ = ∑' n, ‖f n‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) f]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]

/-- The norm sequence of an ℓ¹ function is summable. -/
theorem one_summable_norm (f : lp (fun _ : ℕ => R) 1) : Summable (fun n => ‖f n‖) := by
  have := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)] at this
  simpa using this

instance oneMul : Mul (lp (fun _ : ℕ => R) 1) where
  mul f g := ⟨CauchyProduct.apply (⇑f) (⇑g), f.property.one_mul g.property⟩

@[simp]
theorem one_coeFn_mul (f g : lp (fun _ : ℕ => R) 1) :
    ⇑(f * g) = CauchyProduct.apply (⇑f) (⇑g) := rfl

/-- **Submultiplicativity**: `‖f * g‖_1 ≤ ‖f‖_1 · ‖g‖_1`

    This makes ℓ¹ a Banach algebra. The proof uses:
    1. Mertens' theorem (`tsum_mul_tsum_eq_tsum_sum_antidiagonal`) to exchange sum order
    2. Triangle inequality to bound Cauchy product by product of norms -/
theorem one_norm_mul_le (f g : lp (fun _ : ℕ => R) 1) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [one_norm_eq_tsum, one_norm_eq_tsum f, one_norm_eq_tsum g]
  let φ := fun k => ‖f k‖
  let ψ := fun l => ‖g l‖
  have hφ : Summable φ := one_summable_norm f
  have hψ : Summable ψ := one_summable_norm g
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
-- constant sequence `[1, 1, 1, ...]`.

instance oneNormedRing : NormedRing (lp (fun _ : ℕ => R) 1) :=
  { lp.normedAddCommGroup, lp.oneRing with
    dist_eq := fun _ _ => rfl
    norm_mul_le := one_norm_mul_le }

end lp

end LpOneNormedRing

section LpOneNormOneClass

variable {R : Type*} [NormedRing R] [NormOneClass R]

namespace lp

theorem one_norm_one : ‖(1 : lp (fun _ : ℕ => R) 1)‖ = 1 := by
  rw [one_norm_eq_tsum]
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

/-- Scalar multiplication satisfies `(c • f) * g = c • (f * g)` for Cauchy product. -/
theorem one_smul_mul_assoc (c : 𝕜) (f g : lp (fun _ : ℕ => R) 1) :
    (c • f) * g = c • (f * g) := Subtype.ext <| funext fun n => by
  simp only [lp.coeFn_smul, one_coeFn_mul, Pi.smul_apply, CauchyProduct.apply_eq, smul_sum]
  apply sum_congr rfl
  intro kl _
  exact smul_mul_assoc c (f kl.1) (g kl.2)

/-- Scalar multiplication satisfies `f * (c • g) = c • (f * g)` for Cauchy product. -/
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

### Generalization via HasAntidiagonal

The `CauchyProduct` namespace is defined for `[AddMonoid G] [HasAntidiagonal G]`.
This covers ℕ, ℕ × ℕ, finitely supported functions `α →₀ ℕ`, and potentially
non-commutative monoids like `List α` with append (if given a `HasAntidiagonal` instance).

Only `CauchyProduct.comm` and `CauchyProduct.mul_smul` require `[AddCommMonoid G]`.

The analytic part (ℓ¹ Banach algebra) is currently ℕ-specific because the key lemmas
`tsum_mul_tsum_eq_tsum_sum_antidiagonal` and `summable_sum_mul_antidiagonal_of_summable_mul`
are proven for ℕ in Mathlib. Generalizing these would be a separate upstream contribution.

### Typeclass Requirements

- `oneRing`, `oneNormedRing`: require only `[NormedRing R]`
- `oneNormOneClass`: requires `[NormOneClass R]` (uses `norm_one`)
- `oneNormedCommRing`: requires `[NormedCommRing R]`
- `oneNormedAlgebra`: requires `[NormedField 𝕜] [NormedCommRing R] [NormedAlgebra 𝕜 R]`

### Relation to MeasureTheory.convolution

For `AddCommGroup G` with discrete topology and counting measure,
`MeasureTheory.convolution` gives `(f ⋆ g)(n) = ∑' k, f(k) * g(n - k)`.
This is related but distinct:
- Our Cauchy product uses `HasAntidiagonal` (finite sums over `{(k,l) : k + l = n}`)
- `MeasureTheory.convolution` uses infinite sums and requires subtraction

For ℕ (not a group), only the Cauchy product approach works.
-/
