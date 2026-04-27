/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Tactic.Module

/-!
# Inner product space derived from a norm

This file defines an `InnerProductSpace` instance from a norm that respects the
parallelogram identity. The parallelogram identity is a way to express the inner product of `x` and
`y` in terms of the norms of `x`, `y`, `x + y`, `x - y`.

## Main results

- `InnerProductSpace.ofNorm`: a normed space whose norm respects the parallelogram identity,
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

@[expose] public section


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
  ⟨parallelogram_law_with_norm_mul 𝕜⟩

-- See note [lower instance priority]
instance (priority := 100) InnerProductSpace.toInnerProductSpaceable_ofReal
    [InnerProductSpace ℝ E] : InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm_mul ℝ⟩

variable [NormedSpace 𝕜 E]

local notation "𝓚" => algebraMap ℝ 𝕜

set_option backward.privateInPublic true in
/-- Auxiliary definition of the inner product derived from the norm. -/
private noncomputable def inner_ (x y : E) : 𝕜 :=
  4⁻¹ * (𝓚 ‖x + y‖ * 𝓚 ‖x + y‖ - 𝓚 ‖x - y‖ * 𝓚 ‖x - y‖ +
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x + y‖ * 𝓚 ‖(I : 𝕜) • x + y‖ -
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x - y‖ * 𝓚 ‖(I : 𝕜) • x - y‖)

namespace InnerProductSpaceable

variable {𝕜} (E)

set_option backward.privateInPublic true in
-- This has a prime added to avoid clashing with public `innerProp`
/-- Auxiliary definition for the `add_left` property. -/
private def innerProp' (r : 𝕜) : Prop :=
  ∀ x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y

variable {E}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem _root_.Continuous.inner_ {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => inner_ 𝕜 (f x) (g x) := by
  unfold _root_.inner_
  fun_prop

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem inner_.norm_sq (x : E) : ‖x‖ ^ 2 = re (inner_ 𝕜 x x) := by
  simp only [inner_, normSq_apply, ofNat_re, ofNat_im, map_sub, map_add,
    ofReal_re, ofReal_im, mul_re, inv_re, mul_im, I_re, inv_im]
  have h₁ : ‖x - x‖ = 0 := by simp
  have h₂ : ‖x + x‖ = 2 • ‖x‖ := by convert norm_nsmul 𝕜 2 x using 2; module
  rw [h₁, h₂]
  ring

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem inner_.conj_symm (x y : E) : conj (inner_ 𝕜 y x) = inner_ 𝕜 x y := by
  simp only [inner_, map_sub, map_add, map_mul, map_inv₀, map_ofNat, conj_ofReal, conj_I]
  rw [add_comm y x, norm_sub_rev]
  by_cases hI : (I : 𝕜) = 0
  · simp only [hI, neg_zero, zero_mul]
  have hI' := I_mul_I_of_nonzero hI
  have I_smul (v : E) : ‖(I : 𝕜) • v‖ = ‖v‖ := by rw [norm_smul, norm_I_of_ne_zero hI, one_mul]
  have h₁ : ‖(I : 𝕜) • y - x‖ = ‖(I : 𝕜) • x + y‖ := by
    convert I_smul ((I : 𝕜) • x + y) using 2
    linear_combination (norm := module) -hI' • x
  have h₂ : ‖(I : 𝕜) • y + x‖ = ‖(I : 𝕜) • x - y‖ := by
    convert (I_smul ((I : 𝕜) • y + x)).symm using 2
    linear_combination (norm := module) -hI' • y
  rw [h₁, h₂]
  ring

variable [InnerProductSpaceable E]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem add_left (x y z : E) : inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z := by
  unfold inner_
  have h1 := parallelogram_identity (x + y + z) (x - z)
  have h2 := parallelogram_identity (x + y - z) (x + z)
  have h3 := parallelogram_identity (y + z) z
  have h4 := parallelogram_identity (y - z) z
  have h5 := parallelogram_identity ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z)
  have h6 := parallelogram_identity ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z)
  have h7 := parallelogram_identity ((I : 𝕜) • y + z) z
  have h8 := parallelogram_identity ((I : 𝕜) • y - z) z
  apply_fun 𝓚 at h1 h2 h3 h4 h5 h6 h7 h8
  simp only [map_add, map_mul, map_ofNat, smul_add] at *
  abel_nf at * -- TODO this should be `module_nf` (then the `smul_add` above can go)
  linear_combination (- h1 + h2 + h3 - h4 + I * (- h5 + h6 + h7 - h8)) / 8

private theorem rat_prop (r : ℚ) : innerProp' E (r : 𝕜) := by
  intro x y
  let hom : 𝕜 →ₗ[ℚ] 𝕜 := AddMonoidHom.toRatLinearMap <|
    AddMonoidHom.mk' (fun r ↦ inner_ 𝕜 (r • x) y) <| fun a b ↦ by
      simpa [add_smul] using add_left (a • x) (b • x) y
  simpa [hom, Rat.smul_def] using map_smul hom r 1

private theorem real_prop (r : ℝ) : innerProp' E (r : 𝕜) := by
  intro x y
  revert r
  rw [← funext_iff]
  refine Rat.isDenseEmbedding_coe_real.dense.equalizer ?_ ?_ (funext fun X => ?_)
  · exact (continuous_ofReal.smul continuous_const).inner_ continuous_const
  · exact (continuous_conj.comp continuous_ofReal).mul continuous_const
  · simp only [Function.comp_apply, RCLike.ofReal_ratCast, rat_prop _ _]

private theorem I_prop : innerProp' E (I : 𝕜) := by
  by_cases hI : (I : 𝕜) = 0
  · rw [hI]
    simpa using real_prop (𝕜 := 𝕜) 0
  intro x y
  have hI' := I_mul_I_of_nonzero hI
  rw [conj_I, inner_, inner_, mul_left_comm, smul_smul, hI', neg_one_smul]
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  rw [h₁, h₂]
  linear_combination (- 𝓚 ‖(I : 𝕜) • x - y‖ ^ 2 + 𝓚 ‖(I : 𝕜) • x + y‖ ^ 2) * hI' / 4

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem innerProp (r : 𝕜) : innerProp' E r := by
  intro x y
  rw [← re_add_im r, add_smul, add_left, real_prop _ x, ← smul_smul, real_prop _ _ y, I_prop,
    map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  ring

end InnerProductSpaceable

open InnerProductSpaceable

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- **Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies the
parallelogram identity can be given a compatible inner product. -/
@[implicit_reducible]
noncomputable def InnerProductSpace.ofNorm
    (h : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
    InnerProductSpace 𝕜 E :=
  haveI : InnerProductSpaceable E := ⟨h⟩
  { inner := inner_ 𝕜
    norm_sq_eq_re_inner := inner_.norm_sq
    conj_inner_symm := inner_.conj_symm
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
      norm_sq_eq_re_inner := inner_.norm_sq
      conj_inner_symm := inner_.conj_symm
      add_left := add_left
      smul_left := fun _ _ _ => innerProp _ _ _ }⟩

variable {𝕜 E}
variable [NormedSpace ℝ E]

-- TODO: Replace `InnerProductSpace.toUniformConvexSpace`
-- See note [lower instance priority]
instance (priority := 100) InnerProductSpaceable.to_uniformConvexSpace : UniformConvexSpace E := by
  cases nonempty_innerProductSpace ℝ E; infer_instance
