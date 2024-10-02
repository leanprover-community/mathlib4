/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Inner product space derived from a norm

This file defines an `InnerProductSpace` instance from a norm that respects the
parallellogram identity. The parallelogram identity is a way to express the inner product of `x` and
`y` in terms of the norms of `x`, `y`, `x + y`, `x - y`.

## Main results

- `InnerProductSpace.ofNorm`: a normed space whose norm respects the parallellogram identity,
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

Move upstream to `Analysis.InnerProductSpace.Basic`.

## References

- [Jordan, P. and von Neumann, J., *On inner products in linear, metric spaces*][Jordan1935]
- https://math.stackexchange.com/questions/21792/norms-induced-by-inner-products-and-the-parallelogram-law
- https://math.dartmouth.edu/archive/m113w10/public_html/jordan-vneumann-thm.pdf

## Tags

inner product space, Hilbert space, norm
-/


open RCLike

open scoped ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]

/-- Predicate for the parallelogram identity to hold in a normed group. This is a scalar-less
version of `InnerProductSpace`. If you have an `InnerProductSpaceable` assumption, you can
locally upgrade that to `InnerProductSpace 𝕜 E` using `casesI nonempty_innerProductSpace 𝕜 E`.
-/
class InnerProductSpaceable : Prop where
  parallelogram_identity :
    ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)

variable (𝕜) {E}

theorem InnerProductSpace.toInnerProductSpaceable [InnerProductSpace 𝕜 E] :
    InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm 𝕜⟩

-- See note [lower instance priority]
instance (priority := 100) InnerProductSpace.toInnerProductSpaceable_ofReal
    [InnerProductSpace ℝ E] : InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm ℝ⟩

variable [NormedSpace 𝕜 E]

local notation "𝓚" => algebraMap ℝ 𝕜

/-- Auxiliary definition of the inner product derived from the norm. -/
private noncomputable def inner_ (x y : E) : 𝕜 :=
  4⁻¹ * (𝓚 ‖x + y‖ * 𝓚 ‖x + y‖ - 𝓚 ‖x - y‖ * 𝓚 ‖x - y‖ +
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x + y‖ * 𝓚 ‖(I : 𝕜) • x + y‖ -
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x - y‖ * 𝓚 ‖(I : 𝕜) • x - y‖)

namespace InnerProductSpaceable

variable {𝕜} (E)

-- Porting note: prime added to avoid clashing with public `innerProp`
/-- Auxiliary definition for the `add_left` property. -/
private def innerProp' (r : 𝕜) : Prop :=
  ∀ x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y

variable {E}

theorem innerProp_neg_one : innerProp' E ((-1 : ℤ) : 𝕜) := by
  intro x y
  simp only [inner_, map_one, map_neg, Int.cast_neg, Int.cast_one]
  have h₁ : ‖(-1 : 𝕜) • x - y‖ = ‖x + y‖ := by convert norm_neg (x + y) using 2; module
  have h₂ : ‖(-1 : 𝕜) • x + y‖ = ‖x - y‖ := by convert norm_neg (x - y) using 2; module
  have h₃ : ‖(I : 𝕜) • (-1 : 𝕜) • x + y‖ = ‖(I : 𝕜) • x - y‖ := by
    convert norm_neg ((I : 𝕜) • x - y) using 2; module
  have h₄ : ‖(I : 𝕜) • (-1 : 𝕜) • x - y‖ = ‖(I : 𝕜) • x + y‖ := by
    convert norm_neg ((I : 𝕜) • x + y) using 2; module
  rw [h₁, h₂, h₃, h₄]
  ring

theorem _root_.Continuous.inner_ {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => inner_ 𝕜 (f x) (g x) := by
  unfold inner_
  fun_prop

theorem inner_.norm_sq (x : E) : ‖x‖ ^ 2 = re (inner_ 𝕜 x x) := by
  simp only [inner_, normSq_apply, ofNat_re, ofNat_im, map_sub, map_add, map_zero, map_mul,
    ofReal_re, ofReal_im, mul_re, inv_re,  mul_im, I_re, inv_im]
  have h₂ : ‖x + x‖ = 2 * ‖x‖ := by rw [← two_smul 𝕜, norm_smul, RCLike.norm_two]
  have h₃ : ‖x - x‖ = 0 := by simp
  rw [h₂, h₃]
  ring

theorem inner_.conj_symm (x y : E) : conj (inner_ 𝕜 y x) = inner_ 𝕜 x y := by
  simp only [inner_, map_sub, map_add, map_mul, map_inv₀, map_ofNat, conj_ofReal, conj_I]
  rw [add_comm y x, norm_sub_rev]
  by_cases hI : (I : 𝕜) = 0
  · simp only [hI, neg_zero, zero_mul]
  have hI' := I_mul_I_of_nonzero hI
  -- Porting note: this replaces `norm_I_of_ne_zero` which does not exist in Lean 4
  have : ‖(I : 𝕜)‖ = 1 := by
    rw [← mul_self_inj_of_nonneg (norm_nonneg I) zero_le_one, one_mul, ← norm_mul,
      hI', norm_neg, norm_one]
  have I_smul (v : E) : ‖(I:𝕜) • v‖ = ‖v‖ := by rw [norm_smul, this, one_mul]
  have h₁ : ‖(I : 𝕜) • y - x‖ = ‖(I : 𝕜) • x + y‖ := by
    convert I_smul ((I : 𝕜) • x + y) using 2
    linear_combination (norm := module) congr(-$hI' • x)
  have h₂ : ‖(I : 𝕜) • y + x‖ = ‖(I : 𝕜) • x - y‖ := by
    convert (I_smul ((I : 𝕜) • y + x)).symm using 2
    linear_combination (norm := module) congr(-$hI' • y)
  rw [h₁, h₂]
  ring

variable [InnerProductSpaceable E]

private theorem add_left_aux1 (x y z : E) :
    ‖2 • x + y‖ * ‖2 • x + y‖ + ‖2 • z + y‖ * ‖2 • z + y‖
    = 2 * (‖x + y + z‖ * ‖x + y + z‖ + ‖x - z‖ * ‖x - z‖) := by
  convert parallelogram_identity (x + y + z) (x - z) using 4 <;> abel

private theorem add_left_aux2 (x y z : E) : ‖2 • x + y‖ * ‖2 • x + y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖
    = 2 * (‖x + y - z‖ * ‖x + y - z‖ + ‖x + z‖ * ‖x + z‖) := by
  convert parallelogram_identity (x + y - z) (x + z) using 4 <;> abel

private theorem add_left_aux3 (y z : E) :
    ‖2 • z + y‖ * ‖2 • z + y‖ + ‖y‖ * ‖y‖ = 2 * (‖y + z‖ * ‖y + z‖ + ‖z‖ * ‖z‖)  := by
  convert parallelogram_identity (y + z) z using 4 <;> abel

private theorem add_left_aux4 (y z : E) :
    ‖y‖ * ‖y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖y - z‖ * ‖y - z‖ + ‖z‖ * ‖z‖) := by
  convert parallelogram_identity (y - z) z using 4 <;> abel

variable (𝕜)

private theorem add_left_aux5 (x y z : E) :
    ‖(I : 𝕜) • (2 • x + y)‖ * ‖(I : 𝕜) • (2 • x + y)‖
    + ‖(I : 𝕜) • y + 2 • z‖ * ‖(I : 𝕜) • y + 2 • z‖
    = 2 * (‖(I : 𝕜) • (x + y) + z‖ * ‖(I : 𝕜) • (x + y) + z‖
    + ‖(I : 𝕜) • x - z‖ * ‖(I : 𝕜) • x - z‖) := by
  convert parallelogram_identity ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z) using 4 <;> module

private theorem add_left_aux6 (x y z : E) :
    (‖(I : 𝕜) • (2 • x + y)‖ * ‖(I : 𝕜) • (2 • x + y)‖ +
    ‖(I : 𝕜) • y - 2 • z‖ * ‖(I : 𝕜) • y - 2 • z‖)
    = 2 * (‖(I : 𝕜) • (x + y) - z‖ * ‖(I : 𝕜) • (x + y) - z‖ +
    ‖(I : 𝕜) • x + z‖ * ‖(I : 𝕜) • x + z‖) := by
  convert parallelogram_identity ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z) using 4 <;> module

private theorem add_left_aux7 (y z : E) :
    ‖(I : 𝕜) • y + 2 • z‖ * ‖(I : 𝕜) • y + 2 • z‖ + ‖(I : 𝕜) • y‖ * ‖(I : 𝕜) • y‖ =
    2 * (‖(I : 𝕜) • y + z‖ * ‖(I : 𝕜) • y + z‖ + ‖z‖ * ‖z‖) := by
  convert parallelogram_identity ((I : 𝕜) • y + z) z using 4 <;> module

private theorem add_left_aux8 (y z : E) :
    ‖(I : 𝕜) • y‖ * ‖(I : 𝕜) • y‖ + ‖(I : 𝕜) • y - 2 • z‖ * ‖(I : 𝕜) • y - 2 • z‖ =
    2 * (‖(I : 𝕜) • y - z‖ * ‖(I : 𝕜) • y - z‖ + ‖z‖ * ‖z‖) := by
  convert parallelogram_identity ((I : 𝕜) • y - z) z using 4 <;> module

variable {𝕜}

theorem add_left (x y z : E) : inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z := by
  have H_re := congr(- $(add_left_aux1 x y z) + $(add_left_aux2 x y z)
    + $(add_left_aux3 y z) - $(add_left_aux4 y z))
  have H_im := congr(- $(add_left_aux5 𝕜 x y z) + $(add_left_aux6 𝕜 x y z)
      + $(add_left_aux7 𝕜 y z) - $(add_left_aux8 𝕜 y z))
  have H := congr(𝓚 $H_re + I * 𝓚 $H_im)
  simp only [inner_, map_add, map_sub, map_neg, map_mul, map_ofNat] at H ⊢
  linear_combination H / 8

theorem nat (n : ℕ) (x y : E) : inner_ 𝕜 ((n : 𝕜) • x) y = (n : 𝕜) * inner_ 𝕜 x y := by
  induction' n with n ih
  · simp only [inner_, zero_sub, Nat.cast_zero, zero_mul,
      eq_self_iff_true, zero_smul, zero_add, mul_zero, sub_self, norm_neg, smul_zero]
  · simp only [Nat.cast_succ, add_smul, one_smul]
    rw [add_left, ih, add_mul, one_mul]

private theorem nat_prop (r : ℕ) : innerProp' E (r : 𝕜) := fun x y => by
  simp only [map_natCast]; exact nat r x y

private theorem int_prop (n : ℤ) : innerProp' E (n : 𝕜) := by
  intro x y
  rw [← n.sign_mul_natAbs]
  simp only [Int.cast_natCast, map_natCast, map_intCast, Int.cast_mul, map_mul, mul_smul]
  obtain hn | rfl | hn := lt_trichotomy n 0
  · rw [Int.sign_eq_neg_one_of_neg hn, innerProp_neg_one ((n.natAbs : 𝕜) • x), nat]
    simp only [map_neg, neg_mul, one_mul, mul_eq_mul_left_iff, Int.natAbs_eq_zero,
      eq_self_iff_true, Int.cast_one, map_one, neg_inj, Nat.cast_eq_zero, Int.cast_neg]
  · simp only [inner_, Int.cast_zero, zero_sub, Nat.cast_zero, zero_mul,
      eq_self_iff_true, Int.sign_zero, zero_smul, zero_add, mul_zero, smul_zero,
      sub_self, norm_neg, Int.natAbs_zero]
  · rw [Int.sign_eq_one_of_pos hn]
    simp only [one_mul, mul_eq_mul_left_iff, Int.natAbs_eq_zero, eq_self_iff_true,
      Int.cast_one, one_smul, Nat.cast_eq_zero, nat]

private theorem rat_prop (r : ℚ) : innerProp' E (r : 𝕜) := by
  intro x y
  have : (r.den : 𝕜) ≠ 0 := by
    haveI : CharZero 𝕜 := RCLike.charZero_rclike
    exact mod_cast r.pos.ne'
  rw [← r.num_div_den, ← mul_right_inj' this, ← nat r.den _ y, smul_smul, Rat.cast_div]
  simp only [map_natCast, Rat.cast_natCast, map_intCast, Rat.cast_intCast, map_div₀]
  rw [← mul_assoc, mul_div_cancel₀ _ this, int_prop _ x, map_intCast]

private theorem real_prop (r : ℝ) : innerProp' E (r : 𝕜) := by
  intro x y
  revert r
  rw [← Function.funext_iff]
  refine Rat.isDenseEmbedding_coe_real.dense.equalizer ?_ ?_ (funext fun X => ?_)
  · exact (continuous_ofReal.smul continuous_const).inner_ continuous_const
  · exact (continuous_conj.comp continuous_ofReal).mul continuous_const
  · simp only [Function.comp_apply, RCLike.ofReal_ratCast, rat_prop _ _]

private theorem I_prop : innerProp' E (I : 𝕜) := by
  by_cases hI : (I : 𝕜) = 0
  · rw [hI, ← Nat.cast_zero]; exact nat_prop _
  intro x y
  have hI' : (-I : 𝕜) * I = 1 := by rw [← inv_I, inv_mul_cancel₀ hI]
  rw [conj_I, inner_, inner_, mul_left_comm]
  congr 1
  rw [smul_smul, I_mul_I_of_nonzero hI, neg_one_smul]
  rw [mul_sub, mul_add, mul_sub, mul_assoc I (𝓚 ‖I • x - y‖), ← mul_assoc (-I) I, hI', one_mul,
    mul_assoc I (𝓚 ‖I • x + y‖), ← mul_assoc (-I) I, hI', one_mul]
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  rw [h₁, h₂]
  ring

theorem innerProp (r : 𝕜) : innerProp' E r := by
  intro x y
  rw [← re_add_im r, add_smul, add_left, real_prop _ x, ← smul_smul, real_prop _ _ y, I_prop,
    map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  ring

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
    add_left := InnerProductSpaceable.add_left
    smul_left := fun _ _ _ => innerProp _ _ _ }

variable (E)
variable [InnerProductSpaceable E]

/-- **Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies the
parallelogram identity can be given a compatible inner product. Do
`casesI nonempty_innerProductSpace 𝕜 E` to locally upgrade `InnerProductSpaceable E` to
`InnerProductSpace 𝕜 E`. -/
theorem nonempty_innerProductSpace : Nonempty (InnerProductSpace 𝕜 E) :=
  ⟨{  inner := inner_ 𝕜
      norm_sq_eq_inner := inner_.norm_sq
      conj_symm := inner_.conj_symm
      add_left := add_left
      smul_left := fun _ _ _ => innerProp _ _ _ }⟩

variable {𝕜 E}
variable [NormedSpace ℝ E]

-- TODO: Replace `InnerProductSpace.toUniformConvexSpace`
-- See note [lower instance priority]
instance (priority := 100) InnerProductSpaceable.to_uniformConvexSpace : UniformConvexSpace E := by
  cases nonempty_innerProductSpace ℝ E; infer_instance
