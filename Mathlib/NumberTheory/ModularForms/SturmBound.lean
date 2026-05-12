/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# The Sturm bound for finite-index subgroups of `SL(2, ℤ)`

For any finite-index subgroup `𝒢 ⊆ SL(2, ℤ)` and `f : ModularForm 𝒢 k`, if the q-expansion of
`f` at the cusp `∞` (with cusp width `𝒢.strictWidthInfty`) vanishes for the first
`⌊k * [SL(2, ℤ) : 𝒢] / 12⌋ + 1` coefficients, then `f = 0`.

The proof lifts the level-one bound (`sturm_bound_levelOne`) via the norm map
`ModularForm.norm 𝒮ℒ : ModularForm 𝒢 k → ModularForm 𝒮ℒ (k * m)` (where `m = [SL(2,ℤ) : 𝒢]`):
the norm is identically zero precisely when `f` is, by `ModularForm.norm_eq_zero_iff`, and
sufficient vanishing of `f` at `∞` propagates to sufficient vanishing of `N(f)` at `∞`.

## Main results

* `ModularForm.sturm_bound_finiteIndex`: the Sturm bound for arbitrary finite-index `𝒢 ⊆ 𝒮ℒ`.
* `ModularForm.finiteDimensional_modularForm_finiteIndex`: as a direct corollary,
  `ModularForm 𝒢 k` is finite-dimensional over `ℂ`.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm CuspForm MatrixGroups Function Subgroup

open scoped Manifold Topology

namespace ModularForm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetPlusMinusOne] [𝒢.IsFiniteRelIndex 𝒮ℒ]
variable {k : ℤ} (f : ModularForm 𝒢 k)

omit [𝒢.HasDetPlusMinusOne] in
private lemma qExpansion_norm_order_ge_qExpansion_order
    [DiscreteTopology 𝒢.strictPeriods] :
    (qExpansion 𝒢.strictWidthInfty f).order ≤
      (qExpansion 1 (ModularForm.norm 𝒮ℒ f)).order := by
  obtain ⟨m', hm'_pos, hnRw⟩ := integerCuspWidth_eq_nat_mul_strictWidthInfty (𝒢 := 𝒢)
  have hn_pos : 0 < integerCuspWidth 𝒢 := integerCuspWidth_pos
  have hnR_pos : (0 : ℝ) < integerCuspWidth 𝒢 := by exact_mod_cast hn_pos
  have hw_pos : (0 : ℝ) < 𝒢.strictWidthInfty :=
    𝒢.strictWidthInfty_nonneg.lt_of_ne fun heq => by
      rw [← heq, mul_zero] at hnRw
      exact hnR_pos.ne' hnRw
  have hf_w_per : Function.Periodic ((f : ℍ → ℂ) ∘ ofComplex) 𝒢.strictWidthInfty :=
    SlashInvariantFormClass.periodic_comp_ofComplex f 𝒢.strictWidthInfty_mem_strictPeriods
  have hf_bdd : IsBoundedAtImInfty (f : ℍ → ℂ) := OnePoint.isBoundedAt_infty_iff.mp <|
    f.bdd_at_cusps' <|
      Subgroup.isCusp_of_mem_strictPeriods hnR_pos integerCuspWidth_mem_strictPeriods
  have hf_n_per : Function.Periodic ((f : ℍ → ℂ) ∘ ofComplex)
      ((integerCuspWidth 𝒢 : ℕ) : ℝ) := by
    rw [hnRw]
    convert hf_w_per.nat_mul m' using 1
    push_cast
    ring
  have h_w_le_n : (qExpansion 𝒢.strictWidthInfty (f : ℍ → ℂ)).order ≤
      (qExpansion ((integerCuspWidth 𝒢 : ℕ) : ℝ) (f : ℍ → ℂ)).order := by
    rw [hnRw]
    exact qExpansion_order_le_qExpansion_nat_mul_order hw_pos hm'_pos hf_w_per hf_bdd f.holo'
  obtain ⟨rest, _, h_rest_an, h_decomp⟩ := analyticAt_cuspFunction_one_norm_rest f
  have h_galois_an : AnalyticAt ℂ
      (cuspFunction 1 (galoisProd (integerCuspWidth 𝒢) (f : ℍ → ℂ))) 0 :=
    analyticAt_cuspFunction_zero one_pos (galoisProd_periodic_one hn_pos hf_n_per)
      (galoisProd_mdiff f.holo') (galoisProd_isBoundedAtImInfty hf_bdd)
  rw [show qExpansion 1 (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =
        qExpansion 1 (galoisProd (integerCuspWidth 𝒢) (f : ℍ → ℂ)) * qExpansion 1 rest by
      rw [funext h_decomp]
      exact qExpansion_mul h_galois_an h_rest_an,
    PowerSeries.order_mul,
    qExpansion_one_galoisProd_order_eq_qExpansion_self_order hn_pos hf_n_per hf_bdd f.holo']
  exact h_w_le_n.trans le_self_add

omit [𝒢.HasDetPlusMinusOne] in
/-- **Sturm bound for arithmetic subgroups of `GL(2, ℝ)` commensurable with `SL(2, ℤ)`.** A
modular form of weight `k` whose `q`-expansion at the cusp `∞` has order strictly greater
than `k · [𝒮ℒ : 𝒢] / 12` is identically zero. -/
theorem sturm_bound_finiteIndex [DiscreteTopology 𝒢.strictPeriods]
    (h : (↑((k * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)).toNat / 12) : ℕ∞) <
      (qExpansion 𝒢.strictWidthInfty f).order) : f = 0 := by
  rw [← coe_eq_zero_iff, ← ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ)]
  exact sturm_bound_levelOne (ModularForm.norm 𝒮ℒ f) <|
    h.trans_le (qExpansion_norm_order_ge_qExpansion_order f)

/-- **Classical Sturm bound for finite-index subgroups of `SL(2, ℤ)`.** -/
theorem sturm_bound_finiteIndex_SL2Z {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (h : (↑((k * Γ.index).toNat / 12) : ℕ∞) <
      (qExpansion (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty f).order) : f = 0 := by
  have h_index : Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) = Γ.index := by
    change ((Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)).subgroupOf 𝒮ℒ).index = Γ.index
    rw [← Subgroup.relIndex, MonoidHom.range_eq_map (Matrix.SpecialLinearGroup.mapGL ℝ),
      ← Subgroup.relIndex_comap,
      Subgroup.comap_map_eq_self_of_injective Matrix.SpecialLinearGroup.mapGL_injective,
      Subgroup.relIndex_top_right]
  exact sturm_bound_finiteIndex f (h_index ▸ h)

/-- **Finite-dimensionality of modular forms for arithmetic subgroups.** As a corollary of
the Sturm bound, the space `ModularForm 𝒢 k` is finite-dimensional over `ℂ` for any
arithmetic subgroup `𝒢 ⊆ GL(2, ℝ)` commensurable with `SL(2, ℤ)`. -/
instance finiteDimensional_modularForm_finiteIndex
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] [𝒢.IsFiniteRelIndex 𝒮ℒ]
    [DiscreteTopology 𝒢.strictPeriods] {k : ℤ} :
    Module.Finite ℂ (ModularForm 𝒢 k) := by
  set μ := Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)
  set N : ℕ := (k * μ).toNat / 12 + 1 with hN
  have hnR_pos : (0 : ℝ) < integerCuspWidth 𝒢 := by exact_mod_cast integerCuspWidth_pos (𝒢 := 𝒢)
  have hh : 0 < 𝒢.strictWidthInfty :=
    𝒢.strictWidthInfty_pos_iff.mpr <|
      Subgroup.isCusp_of_mem_strictPeriods hnR_pos integerCuspWidth_mem_strictPeriods
  have hΓ : 𝒢.strictWidthInfty ∈ 𝒢.strictPeriods := 𝒢.strictWidthInfty_mem_strictPeriods
  let T : ModularForm 𝒢 k →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun f i := (qExpansion 𝒢.strictWidthInfty (f : ℍ → ℂ)).coeff i
      map_add' f g := by
        ext i
        simp [ModularForm.qExpansion_add hh hΓ f g]
      map_smul' a f := by
        ext i
        simp [ModularForm.qExpansion_smul hh hΓ a f] }
  refine Module.Finite.of_injective T ((injective_iff_map_eq_zero T).mpr fun f hf => ?_)
  refine sturm_bound_finiteIndex f <| lt_of_lt_of_le ?_ <|
    PowerSeries.nat_le_order _ _ fun i hi ↦ congr_fun hf ⟨i, hi⟩
  exact_mod_cast (hN ▸ Nat.lt_succ_self ((k * μ).toNat / 12) :
    (k * μ).toNat / 12 < N)


end ModularForm

end
