/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

#align_import number_theory.modular from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in
`Analysis.Complex.UpperHalfPlane`). We then define the standard fundamental domain
(`ModularGroup.fd`, `𝒟`) for this action and show
(`ModularGroup.exists_smul_mem_fd`) that any point in `ℍ` can be
moved inside `𝒟`.

## Main definitions

The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟`:
`fd := {z | 1 ≤ (z : ℂ).normSq ∧ |z.re| ≤ (1 : ℝ) / 2}`

The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟ᵒ`:
`fdo := {z | 1 < (z : ℂ).normSq ∧ |z.re| < (1 : ℝ) / 2}`

These notations are localized in the `Modular` locale and can be enabled via `open scoped Modular`.

## Main results

Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`:
`exists_smul_mem_fd (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟`

If both `z` and `γ • z` are in the open domain `𝒟ᵒ` then `z = γ • z`:
`eq_smul_self_of_mem_fdo_mem_fdo {z : ℍ} {g : SL(2,ℤ)} (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z`

# Discussion

Standard proofs make use of the identity

`g • z = a / c - 1 / (c (cz + d))`

for `g = [[a, b], [c, d]]` in `SL(2)`, but this requires separate handling of whether `c = 0`.
Instead, our proof makes use of the following perhaps novel identity (see
`ModularGroup.smul_eq_lcRow0_add`):

`g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

where there is no issue of division by zero.

Another feature is that we delay until the very end the consideration of special matrices
`T=[[1,1],[0,1]]` (see `ModularGroup.T`) and `S=[[0,-1],[1,0]]` (see `ModularGroup.S`), by
instead using abstract theory on the properness of certain maps (phrased in terms of the filters
`Filter.cocompact`, `Filter.cofinite`, etc) to deduce existence theorems, first to prove the
existence of `g` maximizing `(g•z).im` (see `ModularGroup.exists_max_im`), and then among
those, to minimize `|(g•z).re|` (see `ModularGroup.exists_row_one_eq_and_min_re`).
-/


open Complex hiding abs_two

open Matrix hiding mul_smul

open Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup

noncomputable section

local notation "SL(" n ", " R ")" => SpecialLinearGroup (Fin n) R

local macro "↑ₘ" t:term:80 : term => `(term| ($t : Matrix (Fin 2) (Fin 2) ℤ))

open scoped UpperHalfPlane ComplexConjugate

namespace ModularGroup

variable {g : SL(2, ℤ)} (z : ℍ)

section BottomRow

/-- The two numbers `c`, `d` in the "bottom_row" of `g=[[*,*],[c,d]]` in `SL(2, ℤ)` are coprime. -/
theorem bottom_row_coprime {R : Type*} [CommRing R] (g : SL(2, R)) :
    IsCoprime ((↑g : Matrix (Fin 2) (Fin 2) R) 1 0) ((↑g : Matrix (Fin 2) (Fin 2) R) 1 1) := by
  use -(↑g : Matrix (Fin 2) (Fin 2) R) 0 1, (↑g : Matrix (Fin 2) (Fin 2) R) 0 0
  rw [add_comm, neg_mul, ← sub_eq_add_neg, ← det_fin_two]
  exact g.det_coe
#align modular_group.bottom_row_coprime ModularGroup.bottom_row_coprime

/-- Every pair `![c, d]` of coprime integers is the "bottom_row" of some element `g=[[*,*],[c,d]]`
of `SL(2,ℤ)`. -/
theorem bottom_row_surj {R : Type*} [CommRing R] :
    Set.SurjOn (fun g : SL(2, R) => (↑g : Matrix (Fin 2) (Fin 2) R) 1) Set.univ
      {cd | IsCoprime (cd 0) (cd 1)} := by
  rintro cd ⟨b₀, a, gcd_eqn⟩
  let A := of ![![a, -b₀], cd]
  have det_A_1 : det A = 1 := by
    convert gcd_eqn
    rw [det_fin_two]
    simp [A, (by ring : a * cd 1 + b₀ * cd 0 = b₀ * cd 0 + a * cd 1)]
  refine ⟨⟨A, det_A_1⟩, Set.mem_univ _, ?_⟩
  ext; simp [A]
#align modular_group.bottom_row_surj ModularGroup.bottom_row_surj

end BottomRow

section TendstoLemmas

open Filter ContinuousLinearMap

attribute [local simp] ContinuousLinearMap.coe_smul

/-- The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
theorem tendsto_normSq_coprime_pair :
    Filter.Tendsto (fun p : Fin 2 → ℤ => normSq ((p 0 : ℂ) * z + p 1)) cofinite atTop := by
  -- using this instance rather than the automatic `Function.module` makes unification issues in
  -- `LinearEquiv.closedEmbedding_of_injective` less bad later in the proof.
  letI : Module ℝ (Fin 2 → ℝ) := NormedSpace.toModule
  let π₀ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let π₁ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
  let f : (Fin 2 → ℝ) →ₗ[ℝ] ℂ := π₀.smulRight (z : ℂ) + π₁.smulRight 1
  have f_def : ⇑f = fun p : Fin 2 → ℝ => (p 0 : ℂ) * ↑z + p 1 := by
    ext1
    dsimp only [π₀, π₁, f, LinearMap.coe_proj, real_smul, LinearMap.coe_smulRight,
      LinearMap.add_apply]
    rw [mul_one]
  have :
    (fun p : Fin 2 → ℤ => normSq ((p 0 : ℂ) * ↑z + ↑(p 1))) =
      normSq ∘ f ∘ fun p : Fin 2 → ℤ => ((↑) : ℤ → ℝ) ∘ p := by
    ext1
    rw [f_def]
    dsimp only [Function.comp_def]
    rw [ofReal_intCast, ofReal_intCast]
  rw [this]
  have hf : LinearMap.ker f = ⊥ := by
    let g : ℂ →ₗ[ℝ] Fin 2 → ℝ :=
      LinearMap.pi ![imLm, imLm.comp ((z : ℂ) • ((conjAe : ℂ →ₐ[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ))]
    suffices ((z : ℂ).im⁻¹ • g).comp f = LinearMap.id by exact LinearMap.ker_eq_bot_of_inverse this
    apply LinearMap.ext
    intro c
    have hz : (z : ℂ).im ≠ 0 := z.2.ne'
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    ext i
    dsimp only [Pi.smul_apply, LinearMap.pi_apply, smul_eq_mul]
    fin_cases i
    · show (z : ℂ).im⁻¹ * (f c).im = c 0
      rw [f_def, add_im, im_ofReal_mul, ofReal_im, add_zero, mul_left_comm, inv_mul_cancel hz,
        mul_one]
    · show (z : ℂ).im⁻¹ * ((z : ℂ) * conj (f c)).im = c 1
      rw [f_def, RingHom.map_add, RingHom.map_mul, mul_add, mul_left_comm, mul_conj, conj_ofReal,
        conj_ofReal, ← ofReal_mul, add_im, ofReal_im, zero_add, inv_mul_eq_iff_eq_mul₀ hz]
      simp only [ofReal_im, ofReal_re, mul_im, zero_add, mul_zero]
  have hf' : ClosedEmbedding f := f.closedEmbedding_of_injective hf
  have h₂ : Tendsto (fun p : Fin 2 → ℤ => ((↑) : ℤ → ℝ) ∘ p) cofinite (cocompact _) := by
    convert Tendsto.pi_map_coprodᵢ fun _ => Int.tendsto_coe_cofinite
    · rw [coprodᵢ_cofinite]
    · rw [coprodᵢ_cocompact]
  exact tendsto_normSq_cocompact_atTop.comp (hf'.tendsto_cocompact.comp h₂)
#align modular_group.tendsto_norm_sq_coprime_pair ModularGroup.tendsto_normSq_coprime_pair

/-- Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
def lcRow0 (p : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
  ((p 0 : ℝ) • LinearMap.proj (0 : Fin 2) +
      (p 1 : ℝ) • LinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
    (LinearMap.proj 0)
#align modular_group.lc_row0 ModularGroup.lcRow0

@[simp]
theorem lcRow0_apply (p : Fin 2 → ℤ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    lcRow0 p g = p 0 * g 0 0 + p 1 * g 0 1 :=
  rfl
#align modular_group.lc_row0_apply ModularGroup.lcRow0_apply

/-- Linear map sending the matrix [a, b; c, d] to the matrix [ac₀ + bd₀, - ad₀ + bc₀; c, d], for
some fixed `(c₀, d₀)`. -/
@[simps!]
def lcRow0Extend {cd : Fin 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearEquiv.piCongrRight
    ![by
      refine
        LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (Fin 2 → ℝ)
          (GeneralLinearGroup.toLinear (planeConformalMatrix (cd 0 : ℝ) (-(cd 1 : ℝ)) ?_))
      norm_cast
      rw [neg_sq]
      exact hcd.sq_add_sq_ne_zero, LinearEquiv.refl ℝ (Fin 2 → ℝ)]
#align modular_group.lc_row0_extend ModularGroup.lcRow0Extend

-- `simpNF` times out, but only in CI where all of `Mathlib` is imported
attribute [nolint simpNF] lcRow0Extend_apply lcRow0Extend_symm_apply

/-- The map `lcRow0` is proper, that is, preimages of cocompact sets are finite in
`[[* , *], [c, d]]`. -/
theorem tendsto_lcRow0 {cd : Fin 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    Tendsto (fun g : { g : SL(2, ℤ) // (↑ₘg) 1 = cd } => lcRow0 cd ↑(↑g : SL(2, ℝ))) cofinite
      (cocompact ℝ) := by
  let mB : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => of ![![t, (-(1 : ℤ) : ℝ)], (↑) ∘ cd]
  have hmB : Continuous mB := by
    refine continuous_matrix ?_
    simp only [mB, Fin.forall_fin_two, continuous_const, continuous_id', of_apply, cons_val_zero,
      cons_val_one, and_self_iff]
  refine Filter.Tendsto.of_tendsto_comp ?_ (comap_cocompact_le hmB)
  let f₁ : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℝ := fun g =>
    Matrix.map (↑g : Matrix _ _ ℤ) ((↑) : ℤ → ℝ)
  have cocompact_ℝ_to_cofinite_ℤ_matrix :
    Tendsto (fun m : Matrix (Fin 2) (Fin 2) ℤ => Matrix.map m ((↑) : ℤ → ℝ)) cofinite
      (cocompact _) := by
    simpa only [coprodᵢ_cofinite, coprodᵢ_cocompact] using
      Tendsto.pi_map_coprodᵢ fun _ : Fin 2 =>
        Tendsto.pi_map_coprodᵢ fun _ : Fin 2 => Int.tendsto_coe_cofinite
  have hf₁ : Tendsto f₁ cofinite (cocompact _) :=
    cocompact_ℝ_to_cofinite_ℤ_matrix.comp Subtype.coe_injective.tendsto_cofinite
  have hf₂ : ClosedEmbedding (lcRow0Extend hcd) :=
    (lcRow0Extend hcd).toContinuousLinearEquiv.toHomeomorph.closedEmbedding
  convert hf₂.tendsto_cocompact.comp (hf₁.comp Subtype.coe_injective.tendsto_cofinite) using 1
  ext ⟨g, rfl⟩ i j : 3
  fin_cases i <;> [fin_cases j; skip]
  -- the following are proved by `simp`, but it is replaced by `simp only` to avoid timeouts.
  · simp only [mB, mulVec, dotProduct, Fin.sum_univ_two, coe_matrix_coe,
      Int.coe_castRingHom, lcRow0_apply, Function.comp_apply, cons_val_zero, lcRow0Extend_apply,
      LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, GeneralLinearGroup.coe_toLinear,
      val_planeConformalMatrix, neg_neg, mulVecLin_apply, cons_val_one, head_cons, of_apply,
      Fin.mk_zero, Fin.mk_one]
  · convert congr_arg (fun n : ℤ => (-n : ℝ)) g.det_coe.symm using 1
    simp only [f₁, mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two, Function.comp_apply,
      Subtype.coe_mk, lcRow0Extend_apply, cons_val_zero,
      LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, GeneralLinearGroup.coe_toLinear,
      val_planeConformalMatrix, mulVecLin_apply, cons_val_one, head_cons, map_apply, neg_mul,
      Int.cast_sub, Int.cast_mul, neg_sub, of_apply, Fin.mk_zero, Fin.mk_one]
    ring
  · rfl
#align modular_group.tendsto_lc_row0 ModularGroup.tendsto_lcRow0

/-- This replaces `(g•z).re = a/c + *` in the standard theory with the following novel identity:
  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`
  which does not need to be decomposed depending on whether `c = 0`. -/
theorem smul_eq_lcRow0_add {p : Fin 2 → ℤ} (hp : IsCoprime (p 0) (p 1)) (hg : (↑ₘg) 1 = p) :
    ↑(g • z) =
      (lcRow0 p ↑(g : SL(2, ℝ)) : ℂ) / ((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) +
        ((p 1 : ℂ) * z - p 0) / (((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) * (p 0 * z + p 1)) := by
  have nonZ1 : (p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2 ≠ 0 := mod_cast hp.sq_add_sq_ne_zero
  have : ((↑) : ℤ → ℝ) ∘ p ≠ 0 := fun h => hp.ne_zero (by ext i; simpa using congr_fun h i)
  have nonZ2 : (p 0 : ℂ) * z + p 1 ≠ 0 := by simpa using linear_ne_zero _ z this
  field_simp [nonZ1, nonZ2, denom_ne_zero, num]
  rw [(by simp :
    (p 1 : ℂ) * z - p 0 = (p 1 * z - p 0) * ↑(Matrix.det (↑g : Matrix (Fin 2) (Fin 2) ℤ)))]
  rw [← hg, det_fin_two]
  simp only [Int.coe_castRingHom, coe_matrix_coe, Int.cast_mul, ofReal_intCast, map_apply, denom,
    Int.cast_sub, coe_GLPos_coe_GL_coe_matrix, coe'_apply_complex]
  ring
#align modular_group.smul_eq_lc_row0_add ModularGroup.smul_eq_lcRow0_add

theorem tendsto_abs_re_smul {p : Fin 2 → ℤ} (hp : IsCoprime (p 0) (p 1)) :
    Tendsto
      (fun g : { g : SL(2, ℤ) // (↑ₘg) 1 = p } => |((g : SL(2, ℤ)) • z).re|) cofinite atTop := by
  suffices
    Tendsto (fun g : (fun g : SL(2, ℤ) => (↑ₘg) 1) ⁻¹' {p} => ((g : SL(2, ℤ)) • z).re) cofinite
      (cocompact ℝ)
    by exact tendsto_norm_cocompact_atTop.comp this
  have : ((p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact mod_cast hp.sq_add_sq_ne_zero
  let f := Homeomorph.mulRight₀ _ this
  let ff := Homeomorph.addRight
    (((p 1 : ℂ) * z - p 0) / (((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) * (p 0 * z + p 1))).re
  convert (f.trans ff).closedEmbedding.tendsto_cocompact.comp (tendsto_lcRow0 hp) with _ _ g
  change
    ((g : SL(2, ℤ)) • z).re =
      lcRow0 p ↑(↑g : SL(2, ℝ)) / ((p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2) +
        Complex.re (((p 1 : ℂ) * z - p 0) / (((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) * (p 0 * z + p 1)))
  exact mod_cast congr_arg Complex.re (smul_eq_lcRow0_add z hp g.2)
#align modular_group.tendsto_abs_re_smul ModularGroup.tendsto_abs_re_smul

end TendstoLemmas

section FundamentalDomain

set_option linter.uppercaseLean3 false

attribute [local simp] UpperHalfPlane.coe_smul re_smul

/-- For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im` -/
theorem exists_max_im : ∃ g : SL(2, ℤ), ∀ g' : SL(2, ℤ), (g' • z).im ≤ (g • z).im := by
  classical
  let s : Set (Fin 2 → ℤ) := {cd | IsCoprime (cd 0) (cd 1)}
  have hs : s.Nonempty := ⟨![1, 1], isCoprime_one_left⟩
  obtain ⟨p, hp_coprime, hp⟩ :=
    Filter.Tendsto.exists_within_forall_le hs (tendsto_normSq_coprime_pair z)
  obtain ⟨g, -, hg⟩ := bottom_row_surj hp_coprime
  refine ⟨g, fun g' => ?_⟩
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.im_smul_eq_div_normSq,
    div_le_div_left]
  · simpa [← hg] using hp ((↑ₘg') 1) (bottom_row_coprime g')
  · exact z.im_pos
  · exact normSq_denom_pos g' z
  · exact normSq_denom_pos g z
#align modular_group.exists_max_im ModularGroup.exists_max_im

/-- Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
  `|(g•z).re|`.  -/
theorem exists_row_one_eq_and_min_re {cd : Fin 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    ∃ g : SL(2, ℤ), (↑ₘg) 1 = cd ∧ ∀ g' : SL(2, ℤ), (↑ₘg) 1 = (↑ₘg') 1 →
      |(g • z).re| ≤ |(g' • z).re| := by
  haveI : Nonempty { g : SL(2, ℤ) // (↑ₘg) 1 = cd } :=
    let ⟨x, hx⟩ := bottom_row_surj hcd
    ⟨⟨x, hx.2⟩⟩
  obtain ⟨g, hg⟩ := Filter.Tendsto.exists_forall_le (tendsto_abs_re_smul z hcd)
  refine ⟨g, g.2, ?_⟩
  intro g1 hg1
  have : g1 ∈ (fun g : SL(2, ℤ) => (↑ₘg) 1) ⁻¹' {cd} := by
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact Eq.trans hg1.symm (Set.mem_singleton_iff.mp (Set.mem_preimage.mp g.2))
  exact hg ⟨g1, this⟩
#align modular_group.exists_row_one_eq_and_min_re ModularGroup.exists_row_one_eq_and_min_re

theorem coe_T_zpow_smul_eq {n : ℤ} : (↑(T ^ n • z) : ℂ) = z + n := by
  rw [sl_moeb, UpperHalfPlane.coe_smul]
  simp [coe_T_zpow, denom, num, -map_zpow]
#align modular_group.coe_T_zpow_smul_eq ModularGroup.coe_T_zpow_smul_eq

theorem re_T_zpow_smul (n : ℤ) : (T ^ n • z).re = z.re + n := by
  rw [← coe_re, coe_T_zpow_smul_eq, add_re, intCast_re, coe_re]
#align modular_group.re_T_zpow_smul ModularGroup.re_T_zpow_smul

theorem im_T_zpow_smul (n : ℤ) : (T ^ n • z).im = z.im := by
  rw [← coe_im, coe_T_zpow_smul_eq, add_im, intCast_im, add_zero, coe_im]
#align modular_group.im_T_zpow_smul ModularGroup.im_T_zpow_smul

theorem re_T_smul : (T • z).re = z.re + 1 := by simpa using re_T_zpow_smul z 1
#align modular_group.re_T_smul ModularGroup.re_T_smul

theorem im_T_smul : (T • z).im = z.im := by simpa using im_T_zpow_smul z 1
#align modular_group.im_T_smul ModularGroup.im_T_smul

theorem re_T_inv_smul : (T⁻¹ • z).re = z.re - 1 := by simpa using re_T_zpow_smul z (-1)
#align modular_group.re_T_inv_smul ModularGroup.re_T_inv_smul

theorem im_T_inv_smul : (T⁻¹ • z).im = z.im := by simpa using im_T_zpow_smul z (-1)
#align modular_group.im_T_inv_smul ModularGroup.im_T_inv_smul

variable {z}

-- If instead we had `g` and `T` of type `PSL(2, ℤ)`, then we could simply state `g = T^n`.
theorem exists_eq_T_zpow_of_c_eq_zero (hc : (↑ₘg) 1 0 = 0) :
    ∃ n : ℤ, ∀ z : ℍ, g • z = T ^ n • z := by
  have had := g.det_coe
  replace had : (↑ₘg) 0 0 * (↑ₘg) 1 1 = 1 := by rw [det_fin_two, hc] at had; linarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · use (↑ₘg) 0 1
    suffices g = T ^ (↑ₘg) 0 1 by intro z; conv_lhs => rw [this]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  · use -((↑ₘg) 0 1)
    suffices g = -T ^ (-((↑ₘg) 0 1)) by intro z; conv_lhs => rw [this, SL_neg_smul]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
#align modular_group.exists_eq_T_zpow_of_c_eq_zero ModularGroup.exists_eq_T_zpow_of_c_eq_zero

-- If `c = 1`, then `g` factorises into a product terms involving only `T` and `S`.
theorem g_eq_of_c_eq_one (hc : (↑ₘg) 1 0 = 1) : g = T ^ (↑ₘg) 0 0 * S * T ^ (↑ₘg) 1 1 := by
  have hg := g.det_coe.symm
  replace hg : (↑ₘg) 0 1 = (↑ₘg) 0 0 * (↑ₘg) 1 1 - 1 := by rw [det_fin_two, hc] at hg; linarith
  refine Subtype.ext ?_
  conv_lhs => rw [Matrix.eta_fin_two (↑ₘg)]
  rw [hc, hg]
  simp only [coe_mul, coe_T_zpow, coe_S, mul_fin_two]
  congrm !![?_, ?_; ?_, ?_] <;> ring
#align modular_group.g_eq_of_c_eq_one ModularGroup.g_eq_of_c_eq_one

/-- If `1 < |z|`, then `|S • z| < 1`. -/
theorem normSq_S_smul_lt_one (h : 1 < normSq z) : normSq ↑(S • z) < 1 := by
  simpa [coe_S, num, denom] using (inv_lt_inv z.normSq_pos zero_lt_one).mpr h
#align modular_group.norm_sq_S_smul_lt_one ModularGroup.normSq_S_smul_lt_one

/-- If `|z| < 1`, then applying `S` strictly decreases `im`. -/
theorem im_lt_im_S_smul (h : normSq z < 1) : z.im < (S • z).im := by
  have : z.im < z.im / normSq (z : ℂ) := by
    have imz : 0 < z.im := im_pos z
    apply (lt_div_iff z.normSq_pos).mpr
    nlinarith
  convert this
  simp only [ModularGroup.im_smul_eq_div_normSq]
  simp [denom, coe_S]
#align modular_group.im_lt_im_S_smul ModularGroup.im_lt_im_S_smul

/-- The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
def fd : Set ℍ :=
  {z | 1 ≤ normSq (z : ℂ) ∧ |z.re| ≤ (1 : ℝ) / 2}
#align modular_group.fd ModularGroup.fd

/-- The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
def fdo : Set ℍ :=
  {z | 1 < normSq (z : ℂ) ∧ |z.re| < (1 : ℝ) / 2}
#align modular_group.fdo ModularGroup.fdo

@[inherit_doc ModularGroup.fd]
scoped[Modular] notation "𝒟" => ModularGroup.fd

@[inherit_doc ModularGroup.fdo]
scoped[Modular] notation "𝒟ᵒ" => ModularGroup.fdo

open scoped Modular

theorem abs_two_mul_re_lt_one_of_mem_fdo (h : z ∈ 𝒟ᵒ) : |2 * z.re| < 1 := by
  rw [abs_mul, abs_two, ← lt_div_iff' (zero_lt_two' ℝ)]
  exact h.2
#align modular_group.abs_two_mul_re_lt_one_of_mem_fdo ModularGroup.abs_two_mul_re_lt_one_of_mem_fdo

theorem three_lt_four_mul_im_sq_of_mem_fdo (h : z ∈ 𝒟ᵒ) : 3 < 4 * z.im ^ 2 := by
  have : 1 < z.re * z.re + z.im * z.im := by simpa [Complex.normSq_apply] using h.1
  have := h.2
  cases abs_cases z.re <;> nlinarith
#align modular_group.three_lt_four_mul_im_sq_of_mem_fdo ModularGroup.three_lt_four_mul_im_sq_of_mem_fdo

/-- If `z ∈ 𝒟ᵒ`, and `n : ℤ`, then `|z + n| > 1`. -/
theorem one_lt_normSq_T_zpow_smul (hz : z ∈ 𝒟ᵒ) (n : ℤ) : 1 < normSq (T ^ n • z : ℍ) := by
  have hz₁ : 1 < z.re * z.re + z.im * z.im := hz.1
  have hzn := Int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le
  have : 1 < (z.re + ↑n) * (z.re + ↑n) + z.im * z.im := by linarith
  simpa [coe_T_zpow, normSq, num, denom, -map_zpow]
#align modular_group.one_lt_norm_sq_T_zpow_smul ModularGroup.one_lt_normSq_T_zpow_smul

theorem eq_zero_of_mem_fdo_of_T_zpow_mem_fdo {n : ℤ} (hz : z ∈ 𝒟ᵒ) (hg : T ^ n • z ∈ 𝒟ᵒ) :
    n = 0 := by
  suffices |(n : ℝ)| < 1 by
    rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at this
  have h₁ := hz.2
  have h₂ := hg.2
  rw [re_T_zpow_smul] at h₂
  calc
    |(n : ℝ)| ≤ |z.re| + |z.re + (n : ℝ)| := abs_add' (n : ℝ) z.re
    _ < 1 / 2 + 1 / 2 := add_lt_add h₁ h₂
    _ = 1 := add_halves 1
#align modular_group.eq_zero_of_mem_fdo_of_T_zpow_mem_fdo ModularGroup.eq_zero_of_mem_fdo_of_T_zpow_mem_fdo

/-- First Fundamental Domain Lemma: Any `z : ℍ` can be moved to `𝒟` by an element of
`SL(2,ℤ)` -/
theorem exists_smul_mem_fd (z : ℍ) : ∃ g : SL(2, ℤ), g • z ∈ 𝒟 := by
  -- obtain a g₀ which maximizes im (g • z),
  obtain ⟨g₀, hg₀⟩ := exists_max_im z
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_row_one_eq_and_min_re z (bottom_row_coprime g₀)
  refine ⟨g, ?_⟩
  -- `g` has same max im property as `g₀`
  have hg₀' : ∀ g' : SL(2, ℤ), (g' • z).im ≤ (g • z).im := by
    have hg'' : (g • z).im = (g₀ • z).im := by
      rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.im_smul_eq_div_normSq,
        denom_apply, denom_apply, hg]
    simpa only [hg''] using hg₀
  constructor
  · -- Claim: `1 ≤ ⇑norm_sq ↑(g • z)`. If not, then `S•g•z` has larger imaginary part
    contrapose! hg₀'
    refine ⟨S * g, ?_⟩
    rw [mul_smul]
    exact im_lt_im_S_smul hg₀'
  · show |(g • z).re| ≤ 1 / 2
    -- if not, then either `T` or `T'` decrease |Re|.
    rw [abs_le]
    constructor
    · contrapose! hg'
      refine ⟨T * g, (T_mul_apply_one _).symm, ?_⟩
      rw [mul_smul, re_T_smul]
      cases abs_cases ((g • z).re + 1) <;> cases abs_cases (g • z).re <;> linarith
    · contrapose! hg'
      refine ⟨T⁻¹ * g, (T_inv_mul_apply_one _).symm, ?_⟩
      rw [mul_smul, re_T_inv_smul]
      cases abs_cases ((g • z).re - 1) <;> cases abs_cases (g • z).re <;> linarith
#align modular_group.exists_smul_mem_fd ModularGroup.exists_smul_mem_fd

section UniqueRepresentative

/-- An auxiliary result en route to `ModularGroup.c_eq_zero`. -/
theorem abs_c_le_one (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : |(↑ₘg) 1 0| ≤ 1 := by
  let c' : ℤ := (↑ₘg) 1 0
  let c : ℝ := (c' : ℝ)
  suffices 3 * c ^ 2 < 4 by
    rw [← Int.cast_pow, ← Int.cast_three, ← Int.cast_four, ← Int.cast_mul, Int.cast_lt] at this
    replace this : c' ^ 2 ≤ 1 ^ 2 := by linarith
    rwa [sq_le_sq, abs_one] at this
  suffices c ≠ 0 → 9 * c ^ 4 < 16 by
    rcases eq_or_ne c 0 with (hc | hc)
    · rw [hc]; norm_num
    · refine (abs_lt_of_sq_lt_sq' ?_ (by norm_num)).2
      specialize this hc
      linarith
  intro hc
  replace hc : 0 < c ^ 4 := by
    change 0 < c ^ (2 * 2); rw [pow_mul]; apply sq_pos_of_pos (sq_pos_of_ne_zero hc)
  have h₁ :=
    mul_lt_mul_of_pos_right
      (mul_lt_mul'' (three_lt_four_mul_im_sq_of_mem_fdo hg) (three_lt_four_mul_im_sq_of_mem_fdo hz)
        (by linarith) (by linarith))
      hc
  have h₂ : (c * z.im) ^ 4 / normSq (denom (↑g) z) ^ 2 ≤ 1 :=
    div_le_one_of_le
      (pow_four_le_pow_two_of_pow_two_le (UpperHalfPlane.c_mul_im_sq_le_normSq_denom z g))
      (sq_nonneg _)
  let nsq := normSq (denom g z)
  calc
    9 * c ^ 4 < c ^ 4 * z.im ^ 2 * (g • z).im ^ 2 * 16 := by linarith
    _ = c ^ 4 * z.im ^ 4 / nsq ^ 2 * 16 := by
      rw [ModularGroup.im_smul_eq_div_normSq, div_pow]
      ring
    _ ≤ 16 := by rw [← mul_pow]; linarith
#align modular_group.abs_c_le_one ModularGroup.abs_c_le_one

/-- An auxiliary result en route to `ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo`. -/
theorem c_eq_zero (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : (↑ₘg) 1 0 = 0 := by
  have hp : ∀ {g' : SL(2, ℤ)}, g' • z ∈ 𝒟ᵒ → (↑ₘg') 1 0 ≠ 1 := by
    intro g' hg'
    by_contra hc
    let a := (↑ₘg') 0 0
    let d := (↑ₘg') 1 1
    have had : T ^ (-a) * g' = S * T ^ d := by rw [g_eq_of_c_eq_one hc]; group
    let w := T ^ (-a) • g' • z
    have h₁ : w = S • T ^ d • z := by simp only [w, ← mul_smul, had]
    replace h₁ : normSq w < 1 := h₁.symm ▸ normSq_S_smul_lt_one (one_lt_normSq_T_zpow_smul hz d)
    have h₂ : 1 < normSq w := one_lt_normSq_T_zpow_smul hg' (-a)
    linarith
  have hn : (↑ₘg) 1 0 ≠ -1 := by
    intro hc
    replace hc : (↑ₘ(-g)) 1 0 = 1 := by simp [← neg_eq_iff_eq_neg.mpr hc]
    replace hg : -g • z ∈ 𝒟ᵒ := (SL_neg_smul g z).symm ▸ hg
    exact hp hg hc
  specialize hp hg
  rcases Int.abs_le_one_iff.mp <| abs_c_le_one hz hg with ⟨⟩ <;> tauto
#align modular_group.c_eq_zero ModularGroup.c_eq_zero

/-- Second Fundamental Domain Lemma: if both `z` and `g • z` are in the open domain `𝒟ᵒ`,
where `z : ℍ` and `g : SL(2,ℤ)`, then `z = g • z`. -/
theorem eq_smul_self_of_mem_fdo_mem_fdo (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero (c_eq_zero hz hg)
  rw [hn] at hg ⊢
  simp [eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hz hg, one_smul]
#align modular_group.eq_smul_self_of_mem_fdo_mem_fdo ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo

end UniqueRepresentative

end FundamentalDomain

end ModularGroup
