/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

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

These notations are localized in the `Modular` scope and can be enabled via `open scoped Modular`.

## Main results

* `ModularGroup.exists_smul_mem_fd`: Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`.
* `ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo`:
  If both `z` and `γ • z` are in the open domain `𝒟ᵒ` then `z = γ • z`.
* `ModularGroup.fdo_eq_interior_fd` and `ModularGroup.fd_eq_closure_fdo`: topological relations
  between `fd` and `fdo`.

## Discussion

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

@[expose] public section


open Complex

open Matrix hiding mul_smul

open Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup Topology

noncomputable section

open scoped ComplexConjugate MatrixGroups

namespace ModularGroup

variable {g : SL(2, ℤ)} (z : ℍ)

section BottomRow

/-- The two numbers `c`, `d` in the "bottom_row" of `g=[[*,*],[c,d]]` in `SL(2, ℤ)` are coprime. -/
theorem bottom_row_coprime {R : Type*} [CommRing R] (g : SL(2, R)) :
    IsCoprime ((↑g : Matrix (Fin 2) (Fin 2) R) 1 0) ((↑g : Matrix (Fin 2) (Fin 2) R) 1 1) :=
  isCoprime_row g 1

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

end BottomRow

section TendstoLemmas

open Filter ContinuousLinearMap

attribute [local simp] ContinuousLinearMap.coe_smul

set_option backward.isDefEq.respectTransparency false in
/-- The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
theorem tendsto_normSq_coprime_pair :
    Filter.Tendsto (fun p : Fin 2 → ℤ => normSq ((p 0 : ℂ) * z + p 1)) cofinite atTop := by
  -- using this instance rather than the automatic `Function.module` makes unification issues in
  -- `LinearEquiv.isClosedEmbedding_of_injective` less bad later in the proof.
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
    · change (z : ℂ).im⁻¹ * (f c).im = c 0
      rw [f_def, add_im, im_ofReal_mul, ofReal_im, add_zero, mul_left_comm, inv_mul_cancel₀ hz,
        mul_one]
    · change (z : ℂ).im⁻¹ * ((z : ℂ) * conj (f c)).im = c 1
      rw [f_def, map_add, map_mul, mul_add, mul_left_comm, mul_conj, conj_ofReal,
        conj_ofReal, ← ofReal_mul, add_im, ofReal_im, zero_add, inv_mul_eq_iff_eq_mul₀ hz]
      simp only [ofReal_im, ofReal_re, mul_im, zero_add, mul_zero]
  have hf' : IsClosedEmbedding f := f.isClosedEmbedding_of_injective hf
  have h₂ : Tendsto (fun p : Fin 2 → ℤ => ((↑) : ℤ → ℝ) ∘ p) cofinite (cocompact _) := by
    convert Tendsto.pi_map_coprodᵢ fun _ => Int.tendsto_coe_cofinite
    · rw [coprodᵢ_cofinite]
    · rw [coprodᵢ_cocompact]
  exact tendsto_normSq_cocompact_atTop.comp (hf'.tendsto_cocompact.comp h₂)

/-- Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
def lcRow0 (p : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
  ((p 0 : ℝ) • LinearMap.proj (0 : Fin 2) +
      (p 1 : ℝ) • LinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
    (LinearMap.proj 0)

@[simp]
theorem lcRow0_apply (p : Fin 2 → ℤ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    lcRow0 p g = p 0 * g 0 0 + p 1 * g 0 1 :=
  rfl

/-- Linear map sending the matrix [a, b; c, d] to the matrix [ac₀ + bd₀, - ad₀ + bc₀; c, d], for
some fixed `(c₀, d₀)`. -/
@[simps!]
def lcRow0Extend {cd : Fin 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearEquiv.piCongrRight
    ![by
      refine
        LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (Fin 2 → ℝ)
          (GeneralLinearGroup.toLin (planeConformalMatrix (cd 0 : ℝ) (-(cd 1 : ℝ)) ?_))
      norm_cast
      rw [neg_sq]
      exact hcd.sq_add_sq_ne_zero, LinearEquiv.refl ℝ (Fin 2 → ℝ)]

set_option backward.isDefEq.respectTransparency false in
/-- The map `lcRow0` is proper, that is, preimages of cocompact sets are finite in
`[[* , *], [c, d]]`. -/
theorem tendsto_lcRow0 {cd : Fin 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    Tendsto (fun g : { g : SL(2, ℤ) // g 1 = cd } => lcRow0 cd ↑(↑g : SL(2, ℝ))) cofinite
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
  have hf₂ : IsClosedEmbedding (lcRow0Extend hcd) :=
    (lcRow0Extend hcd).toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding
  convert hf₂.tendsto_cocompact.comp (hf₁.comp Subtype.coe_injective.tendsto_cofinite) using 1
  ext ⟨g, rfl⟩ i j : 3
  fin_cases i <;> [fin_cases j; skip]
  -- the following are proved by `simp`, but it is replaced by `simp only` to avoid timeouts.
  · simp only [Fin.isValue, Int.cast_one, map_apply_coe, RingHom.mapMatrix_apply,
      Int.coe_castRingHom, lcRow0_apply, map_apply, Fin.zero_eta, Function.comp_apply,
      of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one, lcRow0Extend_apply,
      LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, GeneralLinearGroup.coe_toLin,
      val_planeConformalMatrix, neg_neg, mulVecLin_apply, mulVec, dotProduct, Fin.sum_univ_two,
      cons_val_one, mB, f₁]
  · convert congr_arg (fun n : ℤ => (-n : ℝ)) g.det_coe.symm using 1
    simp only [Fin.zero_eta, Function.comp_apply, lcRow0Extend_apply, cons_val_zero,
      LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, GeneralLinearGroup.coe_toLin,
      mulVecLin_apply, mulVec, dotProduct, det_fin_two, f₁]
    simp only [Fin.isValue, Fin.mk_one, val_planeConformalMatrix, neg_neg, of_apply, cons_val',
      empty_val', cons_val_fin_one, cons_val_one, map_apply, Fin.sum_univ_two,
      cons_val_zero, neg_mul, Int.cast_sub, Int.cast_mul, neg_sub]
    ring
  · rfl

/-- This replaces `(g•z).re = a/c + *` in the standard theory with the following novel identity:
  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`
  which does not need to be decomposed depending on whether `c = 0`. -/
theorem smul_eq_lcRow0_add {p : Fin 2 → ℤ} (hp : IsCoprime (p 0) (p 1)) (hg : g 1 = p) :
    ↑(g • z) =
      (lcRow0 p ↑(g : SL(2, ℝ)) : ℂ) / ((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) +
        ((p 1 : ℂ) * z - p 0) / (((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) * (p 0 * z + p 1)) := by
  have nonZ1 : (p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2 ≠ 0 := mod_cast hp.sq_add_sq_ne_zero
  have : ((↑) : ℤ → ℝ) ∘ p ≠ 0 := fun h => hp.ne_zero (by ext i; simpa using congr_fun h i)
  have nonZ2 : (p 0 : ℂ) * z + p 1 ≠ 0 := by simpa using linear_ne_zero z this
  subst hg
  rw [coe_specialLinearGroup_apply]
  replace nonZ2 : z * (g 1 0 : ℂ) + g 1 1 ≠ 0 := by convert nonZ2 using 1; ring
  have H := congr(Int.cast (R := ℂ) $(det_fin_two g))
  simp at H
  simp [field]
  linear_combination -((z : ℂ) * (g 1 1 : ℂ) - g 1 0) * H

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_abs_re_smul {p : Fin 2 → ℤ} (hp : IsCoprime (p 0) (p 1)) :
    Tendsto
      (fun g : { g : SL(2, ℤ) // g 1 = p } => |((g : SL(2, ℤ)) • z).re|) cofinite atTop := by
  suffices
    Tendsto (fun g : (fun g : SL(2, ℤ) => g 1) ⁻¹' {p} => ((g : SL(2, ℤ)) • z).re) cofinite
      (cocompact ℝ)
    by exact tendsto_norm_cocompact_atTop.comp this
  have : ((p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact mod_cast hp.sq_add_sq_ne_zero
  let f := Homeomorph.mulRight₀ _ this
  let ff := Homeomorph.addRight
    (((p 1 : ℂ) * z - p 0) / (((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) * (p 0 * z + p 1))).re
  convert (f.trans ff).isClosedEmbedding.tendsto_cocompact.comp (tendsto_lcRow0 hp) with _ _ g
  change
    ((g : SL(2, ℤ)) • z).re =
      lcRow0 p ↑(↑g : SL(2, ℝ)) / ((p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2) +
        Complex.re (((p 1 : ℂ) * z - p 0) / (((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) * (p 0 * z + p 1)))
  exact mod_cast congr_arg Complex.re (smul_eq_lcRow0_add z hp g.2)

end TendstoLemmas

section FundamentalDomain


attribute [local simp] UpperHalfPlane.coe_specialLinearGroup_apply

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
    div_le_div_iff_of_pos_left]
  · simpa [← hg] using hp (g' 1) (bottom_row_coprime g')
  · exact z.im_pos
  · exact normSq_denom_pos g' z.im_ne_zero
  · exact normSq_denom_pos g z.im_ne_zero

/-- Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
  `|(g•z).re|`. -/
theorem exists_row_one_eq_and_min_re {cd : Fin 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    ∃ g : SL(2, ℤ), g 1 = cd ∧ ∀ g' : SL(2, ℤ), g 1 = g' 1 →
      |(g • z).re| ≤ |(g' • z).re| := by
  haveI : Nonempty { g : SL(2, ℤ) // g 1 = cd } :=
    let ⟨x, hx⟩ := bottom_row_surj hcd
    ⟨⟨x, hx.2⟩⟩
  obtain ⟨g, hg⟩ := Filter.Tendsto.exists_forall_le (tendsto_abs_re_smul z hcd)
  refine ⟨g, g.2, ?_⟩
  intro g1 hg1
  have : g1 ∈ (fun g : SL(2, ℤ) => g 1) ⁻¹' {cd} := by
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact Eq.trans hg1.symm (Set.mem_singleton_iff.mp (Set.mem_preimage.mp g.2))
  exact hg ⟨g1, this⟩

theorem coe_T_zpow_smul_eq {n : ℤ} : (↑(T ^ n • z) : ℂ) = z + n := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [coe_T_zpow, -map_zpow]

theorem re_T_zpow_smul (n : ℤ) : (T ^ n • z).re = z.re + n := by
  rw [← coe_re, coe_T_zpow_smul_eq, add_re, intCast_re, coe_re]

theorem im_T_zpow_smul (n : ℤ) : (T ^ n • z).im = z.im := by
  rw [← coe_im, coe_T_zpow_smul_eq, add_im, intCast_im, add_zero, coe_im]

theorem re_T_smul : (T • z).re = z.re + 1 := by simpa using re_T_zpow_smul z 1

theorem im_T_smul : (T • z).im = z.im := by simpa using im_T_zpow_smul z 1

theorem re_T_inv_smul : (T⁻¹ • z).re = z.re - 1 := by simpa using re_T_zpow_smul z (-1)

theorem im_T_inv_smul : (T⁻¹ • z).im = z.im := by simpa using im_T_zpow_smul z (-1)

variable {z}

-- If instead we had `g` and `T` of type `PSL(2, ℤ)`, then we could simply state `g = T^n`.
theorem exists_eq_T_zpow_of_c_eq_zero (hc : g 1 0 = 0) :
    ∃ n : ℤ, ∀ z : ℍ, g • z = T ^ n • z := by
  have had := g.det_coe
  replace had : g 0 0 * g 1 1 = 1 := by rw [det_fin_two, hc] at had; lia
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · use g 0 1
    suffices g = T ^ g 0 1 by intro z; conv_lhs => rw [this]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  · use -(g 0 1)
    suffices g = -T ^ (-(g 0 1)) by intro z; conv_lhs => rw [this, SL_neg_smul]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]

-- If `c = 1`, then `g` factorises into a product terms involving only `T` and `S`.
theorem g_eq_of_c_eq_one (hc : g 1 0 = 1) : g = T ^ g 0 0 * S * T ^ g 1 1 := by
  have hg := g.det_coe.symm
  replace hg : g 0 1 = g 0 0 * g 1 1 - 1 := by rw [det_fin_two, hc] at hg; lia
  refine Subtype.ext ?_
  conv_lhs => rw [(g : Matrix _ _ ℤ).eta_fin_two]
  simp only [hg, sub_eq_add_neg, hc, coe_mul, coe_T_zpow, coe_S, mul_fin_two, mul_zero, mul_one,
    zero_add, one_mul, add_zero, zero_mul]

/-- If `1 < |z|`, then `|S • z| < 1`. -/
theorem normSq_S_smul_lt_one (h : 1 < normSq z) : normSq ↑(S • z) < 1 := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simpa [coe_S, num, denom] using (inv_lt_inv₀ z.normSq_pos zero_lt_one).mpr h

/-- If `|z| < 1`, then applying `S` strictly decreases `im`. -/
theorem im_lt_im_S_smul (h : normSq z < 1) : z.im < (S • z).im := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have : z.im < z.im / normSq (z : ℂ) := by
    have imz : 0 < z.im := im_pos z
    apply (lt_div_iff₀ z.normSq_pos).mpr
    nlinarith
  simpa [denom, coe_S, SpecialLinearGroup.toGL]

/-- The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
def fd : Set ℍ :=
  {z | 1 ≤ normSq (z : ℂ) ∧ |z.re| ≤ (1 : ℝ) / 2}

/-- The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
def fdo : Set ℍ :=
  {z | 1 < normSq (z : ℂ) ∧ |z.re| < (1 : ℝ) / 2}

@[inherit_doc ModularGroup.fd]
scoped[Modular] notation "𝒟" => ModularGroup.fd

@[inherit_doc ModularGroup.fdo]
scoped[Modular] notation "𝒟ᵒ" => ModularGroup.fdo

open scoped Modular

theorem abs_two_mul_re_lt_one_of_mem_fdo (h : z ∈ 𝒟ᵒ) : |2 * z.re| < 1 := by
  rw [abs_mul, abs_two, ← lt_div_iff₀' (zero_lt_two' ℝ)]
  exact h.2

theorem three_lt_four_mul_im_sq_of_mem_fdo (h : z ∈ 𝒟ᵒ) : 3 < 4 * z.im ^ 2 := by
  have : 1 < z.re * z.re + z.im * z.im := by simpa [Complex.normSq_apply] using h.1
  have := h.2
  cases abs_cases z.re <;> nlinarith

/-- non-strict variant of `ModularGroup.three_le_four_mul_im_sq_of_mem_fdo` -/
theorem three_le_four_mul_im_sq_of_mem_fd {τ : ℍ} (h : τ ∈ 𝒟) : 3 ≤ 4 * τ.im ^ 2 := by
  have : 1 ≤ τ.re * τ.re + τ.im * τ.im := by simpa [Complex.normSq_apply] using h.1
  cases abs_cases τ.re <;> nlinarith [h.2]

/-- If `z ∈ 𝒟ᵒ`, and `n : ℤ`, then `|z + n| > 1`. -/
theorem one_lt_normSq_T_zpow_smul (hz : z ∈ 𝒟ᵒ) (n : ℤ) : 1 < normSq (T ^ n • z : ℍ) := by
  rw [coe_T_zpow_smul_eq]
  have hz₁ : 1 < z.re * z.re + z.im * z.im := hz.1
  have hzn := Int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le
  have : 1 < (z.re + ↑n) * (z.re + ↑n) + z.im * z.im := by linarith
  simpa [normSq, num, denom]

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
  · change |(g • z).re| ≤ 1 / 2
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

section UniqueRepresentative

/-- An auxiliary result en route to `ModularGroup.c_eq_zero`. -/
theorem abs_c_le_one (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : |g 1 0| ≤ 1 := by
  let c' : ℤ := g 1 0
  let c := (c' : ℝ)
  suffices 3 * c ^ 2 < 4 by
    rw [← Int.cast_pow, ← Int.cast_three, ← Int.cast_four, ← Int.cast_mul, Int.cast_lt] at this
    replace this : c' ^ 2 ≤ 1 ^ 2 := by lia
    rwa [sq_le_sq, abs_one] at this
  suffices c ≠ 0 → 9 * c ^ 4 < 16 by
    rcases eq_or_ne c 0 with (hc | hc)
    · rw [hc]; simp
    · refine (abs_lt_of_sq_lt_sq' ?_ (by simp)).2
      specialize this hc
      linarith
  intro hc
  have h₁ : 3 * 3 * c ^ 4 < 4 * (g • z).im ^ 2 * (4 * z.im ^ 2) * c ^ 4 := by
    gcongr <;> apply three_lt_four_mul_im_sq_of_mem_fdo <;> assumption
  have h₂ : (c * z.im) ^ 4 / normSq (denom (↑g) z) ^ 2 ≤ 1 :=
    div_le_one_of_le₀
      (pow_four_le_pow_two_of_pow_two_le (z.c_mul_im_sq_le_normSq_denom g))
      (sq_nonneg _)
  let nsq := normSq (denom g z)
  calc
    9 * c ^ 4 < c ^ 4 * z.im ^ 2 * (g • z).im ^ 2 * 16 := by linarith
    _ = c ^ 4 * z.im ^ 4 / nsq ^ 2 * 16 := by
      rw [im_smul_eq_div_normSq, div_pow]
      ring
    _ ≤ 16 := by rw [← mul_pow]; linarith

/-- An auxiliary result en route to `ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo`. -/
theorem c_eq_zero (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : g 1 0 = 0 := by
  have hp : ∀ {g' : SL(2, ℤ)}, g' • z ∈ 𝒟ᵒ → g' 1 0 ≠ 1 := by
    intro g' hg'
    by_contra hc
    let a := g' 0 0
    let d := g' 1 1
    have had : T ^ (-a) * g' = S * T ^ d := by
      rw [g_eq_of_c_eq_one hc]
      dsimp [a, d]
      group
    let w := T ^ (-a) • g' • z
    have h₁ : w = S • T ^ d • z := by simp only [w, ← mul_smul, had]
    replace h₁ : normSq w < 1 := h₁.symm ▸ normSq_S_smul_lt_one (one_lt_normSq_T_zpow_smul hz d)
    have h₂ : 1 < normSq w := one_lt_normSq_T_zpow_smul hg' (-a)
    linarith
  have hn : g 1 0 ≠ -1 := by
    intro hc
    replace hc : (-g) 1 0 = 1 := by simp [← neg_eq_iff_eq_neg.mpr hc]
    replace hg : -g • z ∈ 𝒟ᵒ := (SL_neg_smul g z).symm ▸ hg
    exact hp hg hc
  specialize hp hg
  rcases Int.abs_le_one_iff.mp <| abs_c_le_one hz hg with ⟨⟩ <;> tauto

/-- Second Fundamental Domain Lemma: if both `z` and `g • z` are in the open domain `𝒟ᵒ`,
where `z : ℍ` and `g : SL(2,ℤ)`, then `z = g • z`. -/
theorem eq_smul_self_of_mem_fdo_mem_fdo (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero (c_eq_zero hz hg)
  rw [hn] at hg ⊢
  simp [eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hz hg, one_smul]

end UniqueRepresentative

section Topology

lemma fdo_subset_fd : 𝒟ᵒ ⊆ 𝒟 := fun _ ⟨hx, hx'⟩ ↦ ⟨hx.le, hx'.le⟩

lemma isClosed_fd : IsClosed 𝒟 := by
  refine .inter (.preimage (by fun_prop) isClosed_Ici) ?_
  exact isClosed_le (f := fun z : ℍ ↦ |z.re|) (by fun_prop) continuous_const

lemma isOpen_fdo : IsOpen 𝒟ᵒ := by
  refine .inter (.preimage (by fun_prop) isOpen_Ioi) ?_
  exact isOpen_lt (f := fun z : ℍ ↦ |z.re|) (by fun_prop) continuous_const

/-- Explicit formula for the image of `ModularGroup.fdo` in `ℂ`. -/
lemma coe_fdo : (↑) '' 𝒟ᵒ = {z : ℂ | 0 < z.im ∧ 1 < ‖z‖ ∧ |z.re| < 1/2} := by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ ↦ ⟨⟨x, hxim⟩, ⟨one_lt_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_lt_normSq_iff.mp hτ.1, hτ.2⟩

/-- Explicit formula for the image of `ModularGroup.fd` in `ℂ`. -/
lemma coe_fd : (↑) '' 𝒟 = {z : ℂ | 0 < z.im ∧ 1 ≤ ‖z‖ ∧ |z.re| ≤ 1/2} := by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ ↦ ⟨⟨x, hxim⟩, ⟨one_le_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_le_normSq_iff.mp hτ.1, hτ.2⟩

/--
The image of the fundamental domain `𝒟` in `ℂ` is closed.
This is not immediate (unlike the analogous statement for `𝒟ᵒ`),
since the inclusion of `ℍ` in `ℂ` is an open but not a closed map.
-/
lemma isClosed_coe_fd : IsClosed ((↑) '' 𝒟 : Set ℂ) := by
  rw [coe_fd]
  have : IsClosed {z : ℂ | 0 ≤ z.im ∧ 1 ≤ ‖z‖ ∧ |z.re| ≤ 1/2} := by
    refine .inter ?_ (.inter ?_ ?_)
    · exact isClosed_le continuous_const Complex.continuous_im
    · exact isClosed_le continuous_const continuous_norm
    · exact isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
  convert this using 1
  ext x
  refine ⟨fun ⟨him, hre, hnorm⟩ ↦ ⟨him.le, hre, hnorm⟩, fun ⟨him, hre, hnorm⟩ ↦ ⟨?_, hre, hnorm⟩⟩
  exact him.lt_of_ne' <| by grind [abs_re_eq_norm]

/--
The points on the fundamental domain that aren't on the bottom "arc"
are in the closure of the open fundamental domain.
-/
private lemma mem_closure_of_one_lt_norm {x : ℍ} (hxnorm : 1 < ‖(x : ℂ)‖) (hxre : |x.re| ≤ 1 / 2) :
    x ∈ closure 𝒟ᵒ := by
  -- Need to show that any `x` in this set is a limit of points in `𝒟ᵒ`.
  -- Idea is to use a line segment through the origin and `x`, and show that points
  -- a little below `x` are in `𝒟ᵒ`. There are some annoyances due
  -- to subtypes, etc.
  apply mem_closure_of_frequently_of_tendsto (α := ℝ)
      (b := 𝓝[<] 1) (f := fun t ↦ ofComplex (t * x))
  · apply Filter.Eventually.frequently
    simp only [fdo, Set.mem_setOf, Filter.eventually_and, one_lt_normSq_iff]
    refine ⟨Filter.Tendsto.eventually_const_lt hxnorm (.mono_left ?_ nhdsWithin_le_nhds), ?_⟩
    · have : ContinuousAt (fun a : ℝ ↦ (ofComplex (a * x : ℂ) : ℂ)) 1 := by
        refine .comp (by fun_prop) ((OpenPartialHomeomorph.continuousAt _ ?_).comp (by fun_prop))
        simpa [ofComplex] using x.coe_im_pos
      simpa [ofComplex_apply_of_im_pos x.coe_im_pos] using this.tendsto.norm
    · simp only [eventually_nhdsWithin_iff]
      filter_upwards [eventually_gt_nhds zero_lt_one] with a ha ha'
      rw [← coe_re, ofComplex_apply_of_im_pos (by simpa using mul_pos ha x.coe_im_pos)]
      suffices a * |x.re| < 1 / 2 by simpa [abs_of_pos ha]
      nlinarith [Set.mem_Iio.mp ha']
  · refine .mono_left ?_ nhdsWithin_le_nhds
    rw [isOpenEmbedding_coe.tendsto_nhds_iff, Function.comp_def]
    have : Filter.Tendsto (fun t : ℝ ↦ t * (x : ℂ)) (𝓝 1) (𝓝 (x : ℂ)) := by
      rw [show 𝓝 (x : ℂ) = 𝓝 ((1 : ℝ) * (x : ℂ)) by simp]
      exact Continuous.tendsto (by fun_prop) _
    refine this.congr' ?_
    filter_upwards [eventually_gt_nhds zero_lt_one] with a ha
    rw [ofComplex_apply_of_im_pos (by simpa using mul_pos ha x.coe_im_pos)]

open scoped NNReal in
/-- The points on the bottom "arc" of the fundamental domain are in the closure
of the open fundamental domain. -/
private lemma mem_closure_of_arc {x : ℍ} (hxnorm : ‖(x : ℂ)‖ = 1) (hxre : |x.re| ≤ 1 / 2) :
    x ∈ closure 𝒟ᵒ := by
  -- We show that `x` is a limit of points known to be in the closure.
  rw [← closure_closure]
  -- Consider a vertical line going upwards from `x` (parametrized by `ℝ≥0`)
  apply mem_closure_of_frequently_of_tendsto (b := 𝓝[>] 0)
    (f := fun t : ℝ≥0 ↦ ⟨x + t * Complex.I, by
      simpa using add_pos_of_pos_of_nonneg x.coe_im_pos t.property⟩)
  · apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    refine mem_closure_of_one_lt_norm ?_ (by simpa using hxre)
    suffices 1 < ‖(x : ℂ)‖ ^ 2 + a ^ 2 + 2 * a * x.im by
      rw [← one_lt_normSq_iff]
      convert this
      simp [← normSq_eq_norm_sq, normSq_apply]
      ring
    rw [hxnorm, one_pow, add_assoc, lt_add_iff_pos_right]
    positivity
  · refine .mono_left ?_ nhdsWithin_le_nhds
    simpa [show 𝓝 (x : ℂ) = 𝓝 (x + (((0 : ℝ≥0) : ℝ) : ℂ) * Complex.I) by simp,
      isOpenEmbedding_coe.tendsto_nhds_iff] using Continuous.tendsto (by fun_prop) _

lemma fd_eq_closure_fdo : 𝒟 = closure 𝒟ᵒ := by
  refine subset_antisymm ?_ (isClosed_fd.closure_subset_iff.mpr fdo_subset_fd)
  intro x ⟨hx, hx'⟩
  rw [one_le_normSq_iff] at hx
  rcases lt_or_eq_of_le hx with hx | hx
  · exact mem_closure_of_one_lt_norm hx hx'
  · exact mem_closure_of_arc hx.symm hx'

lemma fdo_eq_interior_fd : 𝒟ᵒ = interior 𝒟 := by
  refine subset_antisymm (isOpen_fdo.subset_interior_iff.mpr fdo_subset_fd) ?_
  have ho1 := isOpenMap_re.image_interior_subset 𝒟
  have ho2 := isOpenMap_norm.image_interior_subset 𝒟
  intro x hx
  rw [Set.image_subset_iff] at *
  constructor
  · rw [one_lt_normSq_iff, ← Set.mem_Ioi, ← interior_Ici]
    apply Set.mem_of_mem_of_subset (Set.mem_preimage.mp (ho2 hx)) (interior_mono ?_)
    rw [Set.image_subset_iff]
    intro ξ hξ
    simpa [Set.mem_preimage, Set.mem_Ici, one_le_normSq_iff] using hξ.1
  · rw [abs_lt, ← Set.mem_Ioo, ← interior_Icc]
    apply Set.mem_of_mem_of_subset ((Set.mem_preimage.mp (ho1 hx))) (interior_mono ?_)
    rw [Set.image_subset_iff]
    intro ξ hξ
    simpa [Set.mem_preimage, Set.mem_Icc, abs_le] using hξ.2

end Topology

section Truncated

/-- The standard fundamental domain truncated at height `y`. -/
def truncatedFundamentalDomain (y : ℝ) : Set ℍ := { τ | τ ∈ 𝒟 ∧ τ.im ≤ y }

/-- Explicit description of the truncated fundamental domain as a subset of `ℂ`, given by
obviously closed conditions. -/
lemma coe_truncatedFundamentalDomain (y : ℝ) :
    UpperHalfPlane.coe '' truncatedFundamentalDomain y =
    {z | 0 ≤ z.im ∧ z.im ≤ y ∧ |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖} := by
  ext z
  constructor
  · rintro ⟨⟨z, hz⟩, h, rfl⟩
    exact ⟨hz.le, h.2, h.1.2, by simpa [Complex.normSq_eq_norm_sq] using h.1.1⟩
  · rintro ⟨hz, h1, h2, h3⟩
    have hz' : 0 < z.im := by
      apply hz.lt_of_ne
      contrapose! h3
      simpa [← sq_lt_one_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq, Complex.normSq,
        ← h3, ← sq] using h2.trans_lt (by norm_num)
    exact ⟨⟨z, hz'⟩, ⟨⟨by simpa [Complex.normSq_eq_norm_sq], h2⟩, h1⟩, rfl⟩

/-- For any `y : ℝ`, the standard fundamental domain truncated at height `y` is compact. -/
lemma isCompact_truncatedFundamentalDomain (y : ℝ) :
    IsCompact (truncatedFundamentalDomain y) := by
  rw [isEmbedding_coe.isCompact_iff, coe_truncatedFundamentalDomain,
    Metric.isCompact_iff_isClosed_bounded]
  constructor
  · -- show closed
    apply (isClosed_le continuous_const Complex.continuous_im).inter
    apply (isClosed_le Complex.continuous_im continuous_const).inter
    apply (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    exact isClosed_le continuous_const continuous_norm
  · -- show bounded
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨√((1 / 2) ^ 2 + y ^ 2), fun z hz ↦ ?_⟩
    simp only [mem_closedBall_zero_iff]
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [Real.sq_sqrt (by positivity), Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
    apply add_le_add
    · rw [sq_le_sq, abs_of_pos <| one_half_pos (α := ℝ)]
      exact hz.2.2.1
    · rw [sq_le_sq₀ hz.1 (hz.1.trans hz.2.1)]
      exact hz.2.1


end Truncated

end FundamentalDomain

lemma exists_one_half_le_im_smul (τ : ℍ) : ∃ γ : SL(2, ℤ), 1 / 2 ≤ im (γ • τ) := by
  obtain ⟨γ, hγ⟩ := exists_smul_mem_fd τ
  use γ
  nlinarith [three_le_four_mul_im_sq_of_mem_fd hγ, im_pos (γ • τ)]

/-- For every `τ : ℍ` there is some `γ ∈ SL(2, ℤ)` that sends it to an element whose
imaginary part is at least `1/2` and such that `denom γ τ` has norm at most 1. -/
lemma exists_one_half_le_im_smul_and_norm_denom_le (τ : ℍ) :
    ∃ γ : SL(2, ℤ), 1 / 2 ≤ im (γ • τ) ∧ ‖denom γ τ‖ ≤ 1 := by
  rcases le_total (1 / 2) τ.im with h | h
  · exact ⟨1, (one_smul SL(2, ℤ) τ).symm ▸ h, by
      simp only [map_one, denom_one, norm_one, le_refl]⟩
  · refine (exists_one_half_le_im_smul τ).imp (fun γ hγ ↦ ⟨hγ, ?_⟩)
    have h1 : τ.im ≤ (γ • τ).im := h.trans hγ
    rw [im_smul_eq_div_normSq, le_div_iff₀ (normSq_denom_pos γ τ.im_ne_zero),
      normSq_eq_norm_sq] at h1
    simpa only [sq_le_one_iff_abs_le_one, abs_norm] using
      (mul_le_iff_le_one_right τ.2).mp h1

end ModularGroup
