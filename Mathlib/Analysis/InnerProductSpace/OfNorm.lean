/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module analysis.inner_product_space.of_norm
! leanprover-community/mathlib commit baa88307f3e699fa7054ef04ec79fa4f056169cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Inner product space derived from a norm

This file defines an `inner_product_space` instance from a norm that respects the
parallellogram identity. The parallelogram identity is a way to express the inner product of `x` and
`y` in terms of the norms of `x`, `y`, `x + y`, `x - y`.

## Main results

- `inner_product_space.of_norm`: a normed space whose norm respects the parallellogram identity,
  can be seen as an inner product space.

## Implementation notes

We define `inner_`

$$\langle x, y \rangle := \frac{1}{4} (‖x + y‖^2 - ‖x - y‖^2 + i ‖ix + y‖ ^ 2 - i ‖ix - y‖^2)$$

and use the parallelogram identity

$$‖x + y‖^2 + ‖x - y‖^2 = 2 (‖x‖^2 + ‖y‖^2)$$

to prove it is an inner product, i.e., that it is conjugate-symmetric (`inner_.conj_symm`) and
linear in the first argument. `add_left` is proved by judicious application of the parallelogram
identity followed by tedious arithmetic. `smul_left` is proved step by step, first noting that
$\langle λ x, y \rangle = λ \langle x, y \rangle$ for $λ ∈ ℕ$, $λ = -1$, hence $λ ∈ ℤ$ and $λ ∈ ℚ$
by arithmetic. Then by continuity and the fact that ℚ is dense in ℝ, the same is true for ℝ.
The case of ℂ then follows by applying the result for ℝ and more arithmetic.

## TODO

Move upstream to `analysis.inner_product_space.basic`.

## References

- [Jordan, P. and von Neumann, J., *On inner products in linear, metric spaces*][Jordan1935]
- https://math.stackexchange.com/questions/21792/norms-induced-by-inner-products-and-the-parallelogram-law
- https://math.dartmouth.edu/archive/m113w10/public_html/jordan-vneumann-thm.pdf

## Tags

inner product space, Hilbert space, norm
-/


open IsROrC

open scoped ComplexConjugate

variable {𝕜 : Type _} [IsROrC 𝕜] (E : Type _) [NormedAddCommGroup E]

/-- Predicate for the parallelogram identity to hold in a normed group. This is a scalar-less
version of `inner_product_space`. If you have an `inner_product_spaceable` assumption, you can
locally upgrade that to `inner_product_space 𝕜 E` using `casesI nonempty_inner_product_space 𝕜 E`.
-/
class InnerProductSpaceable : Prop where
  parallelogram_identity :
    ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)
#align inner_product_spaceable InnerProductSpaceable

variable (𝕜) {E}

theorem InnerProductSpace.to_innerProductSpaceable [InnerProductSpace 𝕜 E] :
    InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm 𝕜⟩
#align inner_product_space.to_inner_product_spaceable InnerProductSpace.to_innerProductSpaceable

-- See note [lower instance priority]
instance (priority := 100) InnerProductSpace.to_innerProductSpaceable_of_real
    [InnerProductSpace ℝ E] : InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm ℝ⟩
#align inner_product_space.to_inner_product_spaceable_of_real InnerProductSpace.to_innerProductSpaceable_of_real

variable [NormedSpace 𝕜 E]

local notation "𝓚" => algebraMap ℝ 𝕜

/-- Auxiliary definition of the inner product derived from the norm. -/
private noncomputable def inner_ (x y : E) : 𝕜 :=
  4⁻¹ *
    (𝓚 ‖x + y‖ * 𝓚 ‖x + y‖ - 𝓚 ‖x - y‖ * 𝓚 ‖x - y‖ +
        (i : 𝕜) * 𝓚 ‖(i : 𝕜) • x + y‖ * 𝓚 ‖(i : 𝕜) • x + y‖ -
      (i : 𝕜) * 𝓚 ‖(i : 𝕜) • x - y‖ * 𝓚 ‖(i : 𝕜) • x - y‖)

namespace InnerProductSpaceable

variable {𝕜} (E)

/-- Auxiliary definition for the `add_left` property -/
private def innerProp (r : 𝕜) : Prop :=
  ∀ x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y

variable {E}

theorem innerProp_neg_one : InnerProp E ((-1 : ℤ) : 𝕜) := by
  intro x y
  simp only [inner_, neg_mul_eq_neg_mul, one_mul, Int.cast_one, one_smul, RingHom.map_one, map_neg,
    Int.cast_neg, neg_smul, neg_one_mul]
  rw [neg_mul_comm]
  congr 1
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  have h₃ : ‖(I : 𝕜) • -x + y‖ = ‖(I : 𝕜) • x - y‖ := by
    rw [← neg_sub, norm_neg, sub_eq_neg_add, ← smul_neg]
  have h₄ : ‖(I : 𝕜) • -x - y‖ = ‖(I : 𝕜) • x + y‖ := by rw [smul_neg, ← neg_add', norm_neg]
  rw [h₁, h₂, h₃, h₄]
  ring
#align inner_product_spaceable.inner_prop_neg_one InnerProductSpaceable.innerProp_neg_one

theorem Continuous.inner_ {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => inner_ 𝕜 (f x) (g x) := by unfold inner_; continuity
#align inner_product_spaceable.continuous.inner_ InnerProductSpaceable.Continuous.inner_

theorem Inner_.norm_sq (x : E) : ‖x‖ ^ 2 = re (inner_ 𝕜 x x) := by
  simp only [inner_]
  have h₁ : norm_sq (4 : 𝕜) = 16 := by
    have : ((4 : ℝ) : 𝕜) = (4 : 𝕜) := by simp only [of_real_one, of_real_bit0]
    rw [← this, norm_sq_eq_def', IsROrC.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have h₂ : ‖x + x‖ = 2 * ‖x‖ := by rw [← two_smul 𝕜, norm_smul, IsROrC.norm_two]
  simp only [inner, h₁, h₂, one_im, bit0_zero, add_zero, norm_zero, I_re, of_real_im, map_add,
    bit0_im, zero_div, MulZeroClass.zero_mul, AddMonoidHom.map_neg, of_real_re, map_sub, sub_zero,
    inv_re, one_re, inv_im, bit0_re, mul_re, MulZeroClass.mul_zero, sub_self, neg_zero,
    algebra_map_eq_of_real]
  ring
#align inner_product_spaceable.inner_.norm_sq InnerProductSpaceable.Inner_.norm_sq

theorem Inner_.conj_symm (x y : E) : conj (inner_ 𝕜 y x) = inner_ 𝕜 x y := by
  simp only [inner_]
  have h4 : conj (4⁻¹ : 𝕜) = 4⁻¹ := by
    rw [IsROrC.conj_inv, ← of_real_one, ← of_real_bit0, ← of_real_bit0, conj_of_real]
  rw [map_mul, h4]
  congr 1
  simp only [map_sub, map_add, algebra_map_eq_of_real, ← of_real_mul, conj_of_real, map_mul, conj_I]
  rw [add_comm y x, norm_sub_rev]
  by_cases hI : (I : 𝕜) = 0
  · simp only [hI, neg_zero, MulZeroClass.zero_mul]
  have h₁ : ‖(I : 𝕜) • y - x‖ = ‖(I : 𝕜) • x + y‖ := by
    trans ‖(I : 𝕜) • ((I : 𝕜) • y - x)‖
    · rw [norm_smul, norm_I_of_ne_zero hI, one_mul]
    · rw [smul_sub, smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, ← neg_add', add_comm, norm_neg]
  have h₂ : ‖(I : 𝕜) • y + x‖ = ‖(I : 𝕜) • x - y‖ := by
    trans ‖(I : 𝕜) • ((I : 𝕜) • y + x)‖
    · rw [norm_smul, norm_I_of_ne_zero hI, one_mul]
    · rw [smul_add, smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, ← neg_add_eq_sub]
  rw [h₁, h₂, ← sub_add_eq_add_sub]
  simp only [neg_mul, sub_eq_add_neg, neg_neg]
#align inner_product_spaceable.inner_.conj_symm InnerProductSpaceable.Inner_.conj_symm

variable [InnerProductSpaceable E]

private theorem add_left_aux1 (x y z : E) :
    ‖x + y + z‖ * ‖x + y + z‖ =
      (‖2 • x + y‖ * ‖2 • x + y‖ + ‖2 • z + y‖ * ‖2 • z + y‖) / 2 - ‖x - z‖ * ‖x - z‖ := by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  convert parallelogram_identity (x + y + z) (x - z) using 4 <;> · rw [two_smul]; abel

private theorem add_left_aux2 (x y z : E) :
    ‖x + y - z‖ * ‖x + y - z‖ =
      (‖2 • x + y‖ * ‖2 • x + y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 - ‖x + z‖ * ‖x + z‖ := by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  have h₀ := parallelogram_identity (x + y - z) (x + z)
  convert h₀ using 4 <;> · rw [two_smul]; abel

private theorem add_left_aux2' (x y z : E) :
    ‖x + y + z‖ * ‖x + y + z‖ - ‖x + y - z‖ * ‖x + y - z‖ =
      ‖x + z‖ * ‖x + z‖ - ‖x - z‖ * ‖x - z‖ +
        (‖2 • z + y‖ * ‖2 • z + y‖ - ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 :=
  by rw [add_left_aux1, add_left_aux2]; ring

private theorem add_left_aux3 (y z : E) :
    ‖2 • z + y‖ * ‖2 • z + y‖ = 2 * (‖y + z‖ * ‖y + z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ := by
  apply eq_sub_of_add_eq
  convert parallelogram_identity (y + z) z using 4 <;> · try rw [two_smul]; abel

private theorem add_left_aux4 (y z : E) :
    ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖y - z‖ * ‖y - z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ := by
  apply eq_sub_of_add_eq'
  have h₀ := parallelogram_identity (y - z) z
  convert h₀ using 4 <;> · try rw [two_smul]; abel

private theorem add_left_aux4' (y z : E) :
    (‖2 • z + y‖ * ‖2 • z + y‖ - ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 =
      ‖y + z‖ * ‖y + z‖ - ‖y - z‖ * ‖y - z‖ :=
  by rw [add_left_aux3, add_left_aux4]; ring

private theorem add_left_aux5 (x y z : E) :
    ‖(i : 𝕜) • (x + y) + z‖ * ‖(i : 𝕜) • (x + y) + z‖ =
      (‖(i : 𝕜) • (2 • x + y)‖ * ‖(i : 𝕜) • (2 • x + y)‖ +
            ‖(i : 𝕜) • y + 2 • z‖ * ‖(i : 𝕜) • y + 2 • z‖) /
          2 -
        ‖(i : 𝕜) • x - z‖ * ‖(i : 𝕜) • x - z‖ := by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  have h₀ := parallelogram_identity ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z)
  convert h₀ using 4 <;> · try simp only [two_smul, smul_add]; abel

private theorem add_left_aux6 (x y z : E) :
    ‖(i : 𝕜) • (x + y) - z‖ * ‖(i : 𝕜) • (x + y) - z‖ =
      (‖(i : 𝕜) • (2 • x + y)‖ * ‖(i : 𝕜) • (2 • x + y)‖ +
            ‖(i : 𝕜) • y - 2 • z‖ * ‖(i : 𝕜) • y - 2 • z‖) /
          2 -
        ‖(i : 𝕜) • x + z‖ * ‖(i : 𝕜) • x + z‖ := by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  have h₀ := parallelogram_identity ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z)
  convert h₀ using 4 <;> · try simp only [two_smul, smul_add]; abel

private theorem add_left_aux7 (y z : E) :
    ‖(i : 𝕜) • y + 2 • z‖ * ‖(i : 𝕜) • y + 2 • z‖ =
      2 * (‖(i : 𝕜) • y + z‖ * ‖(i : 𝕜) • y + z‖ + ‖z‖ * ‖z‖) - ‖(i : 𝕜) • y‖ * ‖(i : 𝕜) • y‖ := by
  apply eq_sub_of_add_eq
  have h₀ := parallelogram_identity ((I : 𝕜) • y + z) z
  convert h₀ using 4 <;> · try simp only [two_smul, smul_add]; abel

private theorem add_left_aux8 (y z : E) :
    ‖(i : 𝕜) • y - 2 • z‖ * ‖(i : 𝕜) • y - 2 • z‖ =
      2 * (‖(i : 𝕜) • y - z‖ * ‖(i : 𝕜) • y - z‖ + ‖z‖ * ‖z‖) - ‖(i : 𝕜) • y‖ * ‖(i : 𝕜) • y‖ := by
  apply eq_sub_of_add_eq'
  have h₀ := parallelogram_identity ((I : 𝕜) • y - z) z
  convert h₀ using 4 <;> · try simp only [two_smul, smul_add]; abel

theorem add_left (x y z : E) : inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z := by
  simp only [inner_, ← mul_add]
  congr
  simp only [mul_assoc, ← map_mul, add_sub_assoc, ← mul_sub, ← map_sub]
  rw [add_add_add_comm]
  simp only [← map_add, ← mul_add]
  congr
  · rw [← add_sub_assoc, add_left_aux2', add_left_aux4']
  · rw [add_left_aux5, add_left_aux6, add_left_aux7, add_left_aux8]
    simp only [map_sub, map_mul, map_add, div_eq_mul_inv]
    ring
#align inner_product_spaceable.add_left InnerProductSpaceable.add_left

theorem nat (n : ℕ) (x y : E) : inner_ 𝕜 ((n : 𝕜) • x) y = (n : 𝕜) * inner_ 𝕜 x y := by
  induction' n with n ih
  ·
    simp only [inner_, Nat.zero_eq, zero_sub, Nat.cast_zero, MulZeroClass.zero_mul,
      eq_self_iff_true, zero_smul, zero_add, MulZeroClass.mul_zero, sub_self, norm_neg, smul_zero]
  · simp only [Nat.cast_succ, add_smul, one_smul]
    rw [add_left, ih, add_mul, one_mul]
#align inner_product_spaceable.nat InnerProductSpaceable.nat

private theorem nat_prop (r : ℕ) : InnerProp E (r : 𝕜) := fun x y => by simp only [map_natCast];
  exact Nat r x y

private theorem int_prop (n : ℤ) : InnerProp E (n : 𝕜) := by
  intro x y
  rw [← n.sign_mul_nat_abs]
  simp only [Int.cast_ofNat, map_natCast, map_intCast, Int.cast_mul, map_mul, mul_smul]
  obtain hn | rfl | hn := lt_trichotomy n 0
  · rw [Int.sign_eq_neg_one_of_neg hn, inner_prop_neg_one ((n.nat_abs : 𝕜) • x), Nat]
    simp only [map_neg, neg_mul, one_mul, mul_eq_mul_left_iff, true_or_iff, Int.natAbs_eq_zero,
      eq_self_iff_true, Int.cast_one, map_one, neg_inj, Nat.cast_eq_zero, Int.cast_neg]
  ·
    simp only [inner_, Int.cast_zero, zero_sub, Nat.cast_zero, MulZeroClass.zero_mul,
      eq_self_iff_true, Int.sign_zero, zero_smul, zero_add, MulZeroClass.mul_zero, smul_zero,
      sub_self, norm_neg, Int.natAbs_zero]
  · rw [Int.sign_eq_one_of_pos hn]
    simp only [one_mul, mul_eq_mul_left_iff, true_or_iff, Int.natAbs_eq_zero, eq_self_iff_true,
      Int.cast_one, one_smul, Nat.cast_eq_zero, Nat]

private theorem rat_prop (r : ℚ) : InnerProp E (r : 𝕜) := by
  intro x y
  have : (r.denom : 𝕜) ≠ 0 := by
    haveI : CharZero 𝕜 := IsROrC.charZero_isROrC
    exact_mod_cast r.pos.ne'
  rw [← r.num_div_denom, ← mul_right_inj' this, ← Nat r.denom _ y, smul_smul, Rat.cast_div]
  simp only [map_natCast, Rat.cast_coe_nat, map_intCast, Rat.cast_coe_int, map_div₀]
  rw [← mul_assoc, mul_div_cancel' _ this, int_prop _ x, map_intCast]

private theorem real_prop (r : ℝ) : InnerProp E (r : 𝕜) := by
  intro x y
  revert r
  rw [← Function.funext_iff]
  refine' rat.dense_embedding_coe_real.dense.equalizer _ _ (funext fun X => _)
  · exact (continuous_of_real.smul continuous_const).inner_ continuous_const
  · exact (continuous_conj.comp continuous_of_real).mul continuous_const
  · simp only [Function.comp_apply, IsROrC.ofReal_ratCast, rat_prop _ _]

private theorem I_prop : InnerProp E (i : 𝕜) := by
  by_cases hI : (I : 𝕜) = 0
  · rw [hI, ← Nat.cast_zero]; exact nat_prop _
  intro x y
  have hI' : (-I : 𝕜) * I = 1 := by rw [← inv_I, inv_mul_cancel hI]
  rw [conj_I, inner_, inner_, mul_left_comm]
  congr 1
  rw [smul_smul, I_mul_I_of_nonzero hI, neg_one_smul]
  rw [mul_sub, mul_add, mul_sub, mul_assoc I (𝓚 ‖I • x - y‖), ← mul_assoc (-I) I, hI', one_mul,
    mul_assoc I (𝓚 ‖I • x + y‖), ← mul_assoc (-I) I, hI', one_mul]
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  rw [h₁, h₂]
  simp only [sub_eq_add_neg, mul_assoc]
  rw [← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul]
  abel

theorem innerProp (r : 𝕜) : InnerProp E r := by
  intro x y
  rw [← re_add_im r, add_smul, add_left, real_prop _ x, ← smul_smul, real_prop _ _ y, I_prop,
    map_add, map_mul, conj_of_real, conj_of_real, conj_I]
  ring
#align inner_product_spaceable.inner_prop InnerProductSpaceable.innerProp

end InnerProductSpaceable

open InnerProductSpaceable

/-- **Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies the
parallelogram identity can be given a compatible inner product. -/
noncomputable def InnerProductSpace.ofNorm
    (h : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
    InnerProductSpace 𝕜 E :=
  haveI : InnerProductSpaceable E := ⟨h⟩
  { inner := inner_ 𝕜
    norm_sq_eq_inner := inner_.norm_sq
    conj_symm := inner_.conj_symm
    add_left
    smul_left := fun _ _ _ => inner_prop _ _ _ }
#align inner_product_space.of_norm InnerProductSpace.ofNorm

variable (𝕜 E) [InnerProductSpaceable E]

/-- **Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies the
parallelogram identity can be given a compatible inner product. Do
`casesI nonempty_inner_product_space 𝕜 E` to locally upgrade `inner_product_spaceable E` to
`inner_product_space 𝕜 E`. -/
theorem nonempty_innerProductSpace : Nonempty (InnerProductSpace 𝕜 E) :=
  ⟨{  inner := inner_ 𝕜
      norm_sq_eq_inner := Inner_.norm_sq
      conj_symm := Inner_.conj_symm
      add_left := add_left
      smul_left := fun _ _ _ => innerProp _ _ _ }⟩
#align nonempty_inner_product_space nonempty_innerProductSpace

variable {𝕜 E} [NormedSpace ℝ E]

-- TODO: Replace `inner_product_space.to_uniform_convex_space`
-- See note [lower instance priority]
instance (priority := 100) InnerProductSpaceable.to_uniformConvexSpace : UniformConvexSpace E := by
  cases nonempty_innerProductSpace ℝ E; infer_instance
#align inner_product_spaceable.to_uniform_convex_space InnerProductSpaceable.to_uniformConvexSpace

