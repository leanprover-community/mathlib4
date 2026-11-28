/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.OrderAtInfty

/-!
# Order at a cusp

We define the width-weighted order of a function at a cusp, prove independence of the
scaling matrix, and descend this order to cusp orbits for slash-invariant forms.

## Main definitions and results

* `UpperHalfPlane.orderAtCusp`: the width-weighted order at a point of `ℙ¹(ℝ)`.
* `UpperHalfPlane.orderAtCusp_eq`: compute the order at a cusp using any scaling matrix.
* `UpperHalfPlane.orderAtCuspOrbit`: the order of a slash-invariant form at a cusp orbit.
* `UpperHalfPlane.orderAtCusp_eq_qExpansion_order`: the order at infinity is the order of
  the `q`-expansion divided by the regularity factor.
-/

public section

open ConjAct OnePoint Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise

namespace UpperHalfPlane

/-- The width-weighted order is unchanged by an upper triangular change of cusp coordinate. -/
lemma width_mul_orderAtInfty_slash_of_upperTriangular (G : Subgroup (GL (Fin 2) ℝ))
    [DiscreteTopology G] {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) (f : ℍ → ℂ) (k : ℤ) :
    (toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) = G.widthInfty * orderAtInfty f := by
  rw [Subgroup.widthInfty_conj_of_upperTriangular G hg,
    orderAtInfty_slash_of_upperTriangular f k g hg, ← mul_assoc, ← EReal.coe_mul, div_mul_cancel₀]
  grind [g.a_ne_zero_of_c_eq_zero hg, g.d_ne_zero_of_c_eq_zero hg]

lemma width_mul_orderAtInfty_slash_eq_of_smul_infty_eq {G : Subgroup (GL (Fin 2) ℝ)}
    [DiscreteTopology G] {g h : GL (Fin 2) ℝ} (hcg : g • (∞ : OnePoint ℝ) = h • ∞)
    (f : ℍ → ℂ) (k : ℤ) :
    (toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) =
      (toConjAct h⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] h) := by
  obtain ⟨t, rfl⟩ : ∃ t, h = g * t := ⟨g⁻¹ * h, (mul_inv_cancel_left g h).symm⟩
  have ht : t 1 0 = 0 := smul_infty_eq_self_iff.mp <| by simpa [mul_smul] using hcg.symm
  rw [mul_inv_rev, toConjAct_mul, mul_smul, SlashAction.slash_mul]
  exact (width_mul_orderAtInfty_slash_of_upperTriangular _ ht _ _).symm

section Cusps

/-- Independence of the scaling matrix, allowing either orientation. -/
lemma width_mul_orderAtInfty_slash_eq_of_smul_infty_eq' (G : Subgroup (GL (Fin 2) ℝ))
    [DiscreteTopology G] {g h : GL (Fin 2) ℝ} (hcg : g • (∞ : OnePoint ℝ) = h • ∞)
    (f : ℍ → ℂ) (k : ℤ) :
    (toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) =
      (toConjAct h⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] h) := by
  let t := g⁻¹ * h
  have ht : t 1 0 = 0 := by
    simp only [← smul_infty_eq_self_iff, t, mul_smul, ← hcg, inv_smul_smul]
  have ha : |t 0 0 / t 1 1| ≠ 0 := by simpa [Matrix.det_fin_two, ht] using t.det_ne_zero
  have heq : (toConjAct t⁻¹ • (toConjAct g⁻¹ • G)).widthInfty *
      orderAtInfty ((f ∣[k] g) ∣[k] t) =
        (toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) := by
    rw [Subgroup.widthInfty_conj_of_upperTriangular _ ht,
      orderAtInfty_slash_of_upperTriangular _ k t ht, ← mul_assoc, ← EReal.coe_mul,
      div_mul_cancel₀ _ ha]
  simpa only [t, mul_inv_rev, inv_inv, ← toConjAct_mul, ← mul_smul,
    mul_inv_cancel_right, ← SlashAction.slash_mul, mul_inv_cancel_left] using heq.symm

private noncomputable def cuspScalingMatrix (c : OnePoint ℝ) : GL (Fin 2) ℝ :=
  mapGL ℝ (c.exists_mem_SL2 ℝ).choose

private lemma cuspScalingMatrix_smul (c : OnePoint ℝ) :
    cuspScalingMatrix c • ∞ = c :=
  (c.exists_mem_SL2 ℝ).choose_spec

/-- The width-weighted order at a cusp, computed using a determinant-one scaling matrix
sending infinity to `c`. For a cusp of a discrete group with determinant `±1`,
`orderAtCusp_eq` computes this using any scaling matrix, of either orientation.

The definition is made for every point of `ℙ¹(ℝ)` and every complex-valued function on `ℍ`;
the cusp and discreteness hypotheses belong to the evaluation lemmas. -/
noncomputable def orderAtCusp (G : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) (c : OnePoint ℝ)
    (f : ℍ → ℂ) : EReal :=
  (toConjAct (cuspScalingMatrix c)⁻¹ • G).widthInfty *
    orderAtInfty (f ∣[k] cuspScalingMatrix c)

/-- Compute the order at a cusp using any scaling matrix, of either orientation. -/
lemma orderAtCusp_eq {G : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology G] [G.HasDetPlusMinusOne]
    {c : OnePoint ℝ} (hc : IsCusp c G) {g : GL (Fin 2) ℝ} (hg : g • ∞ = c) (k : ℤ) (f : ℍ → ℂ) :
    orderAtCusp G k c f = (toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) := by
  have hchosen : cuspScalingMatrix c • ∞ = c := cuspScalingMatrix_smul c
  have hw : 0 < (toConjAct (cuspScalingMatrix c)⁻¹ • G).widthInfty := by
    have heq : (cuspScalingMatrix c)⁻¹ • c = ∞ := inv_smul_eq_iff.mpr hchosen.symm
    simpa only [Subgroup.widthInfty_pos_iff, heq] using hc.smul (cuspScalingMatrix c)⁻¹
  exact width_mul_orderAtInfty_slash_eq_of_smul_infty_eq' G (hchosen.trans hg.symm) f k

/-- At infinity, the order at a cusp is the width times the exponential order. -/
lemma orderAtCusp_infty {G : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology G]
    [G.HasDetPlusMinusOne] (hc : IsCusp ∞ G) (k : ℤ) (f : ℍ → ℂ) :
    orderAtCusp G k ∞ f = G.widthInfty * orderAtInfty f := by
  simpa using orderAtCusp_eq hc (g := 1) (by simp) k f

/-- Changing coordinates transports the cusp and the level, preserving the cusp order. -/
lemma orderAtCusp_slash {G : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology G]
    [G.HasDetPlusMinusOne] (k : ℤ) {c : OnePoint ℝ} (hc : IsCusp c G)
    (g : GL (Fin 2) ℝ) (f : ℍ → ℂ) :
    orderAtCusp (toConjAct g⁻¹ • G) k (g⁻¹ • c) (f ∣[k] g) =
      orderAtCusp G k c f := by
  rw [orderAtCusp_eq (hc.smul g⁻¹) (g := g⁻¹ * cuspScalingMatrix c)
    (by simp only [mul_smul, cuspScalingMatrix_smul]),
    orderAtCusp_eq hc (cuspScalingMatrix_smul c)]
  simp [← mul_smul, ← SlashAction.slash_mul]

variable {F : Type*} {G : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology G]
  [G.HasDetPlusMinusOne] {k : ℤ} [FunLike F ℍ ℂ] [SlashInvariantFormClass F G k]

/-- The order of a slash-invariant form is constant on each cusp orbit. -/
lemma orderAtCusp_smul {c : OnePoint ℝ} (hc : IsCusp c G) (f : F)
    {g : GL (Fin 2) ℝ} (hg : g ∈ G) :
    orderAtCusp G k (g • c) f = orderAtCusp G k c f := by
  have aux : (g * cuspScalingMatrix c) • ∞ = g • c := by rw [mul_smul, cuspScalingMatrix_smul]
  rw [orderAtCusp_eq (hc.smul_of_mem hg) aux, orderAtCusp_eq hc (cuspScalingMatrix_smul c)]
  simp only [mul_inv_rev, toConjAct_mul, mul_smul,
    G.conjAct_pointwise_smul_eq_self (G.le_normalizer (G.inv_mem hg)),
    SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f g hg]

variable (G k) in
/-- The width-weighted order of a slash-invariant form at a cusp orbit. -/
noncomputable def orderAtCuspOrbit (c : CuspOrbits G) (f : F) : EReal :=
  Quotient.lift (fun c ↦ orderAtCusp G k c.val f)
    (fun ⟨c, _⟩ ⟨d, hd⟩ ⟨⟨g, hG⟩, hg⟩ ↦ by
      have heq : g • d = c := congr(Subtype.val $hg)
      simpa only [heq] using orderAtCusp_smul hd f hG) c

/-- Evaluate the order at a cusp orbit on a representative. -/
@[simp] lemma orderAtCuspOrbit_mk (c : cuspsSubMulAction G) (f : F) :
    orderAtCuspOrbit G k ⟦c⟧ f = orderAtCusp G k c f := by
  simp [orderAtCuspOrbit]

/-- Any cusp representing an orbit computes the order at that orbit. -/
lemma orderAtCuspOrbit_eq (c : CuspOrbits G) (d : cuspsSubMulAction G)
    (hd : ⟦d⟧ = c) (f : F) :
    orderAtCuspOrbit G k c f = orderAtCusp G k d f := by
  simp [orderAtCuspOrbit, ← hd]

end Cusps

variable {F : Type*} {G : Subgroup (GL (Fin 2) ℝ)}
  [G.HasDetPlusMinusOne] (k : ℤ) [FunLike F ℍ ℂ] [ModularFormClass F G k]

lemma orderAtCusp_eq_qExpansion_order [DiscreteTopology G] [Fact (IsCusp ∞ G)] (f : F) :
    orderAtCusp G k ∞ f = (qExpansion G.strictWidthInfty f).order / G.regularityFactorInfty := by
  rw [orderAtCusp_infty Fact.out,
      orderAtInfty_eq_qExpansion_order (Subgroup.strictWidthInfty_pos_iff.mpr Fact.out)
        (SlashInvariantFormClass.periodic_comp_ofComplex f G.strictWidthInfty_mem_strictPeriods)
        (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)]
  rw [G.strictWidthInfty_eq_regularityFactorInfty_mul_widthInfty,
    EReal.coe_mul, EReal.coe_natCast, EReal.mul_div, mul_comm (G.widthInfty : EReal),
    EReal.mul_div_mul_cancel (EReal.coe_ne_bot _) (EReal.coe_ne_top _)]
  exact EReal.coe_ne_zero.mpr (Subgroup.widthInfty_pos_iff.mpr Fact.out).ne'

omit [G.HasDetPlusMinusOne] in
/-- A modular form has nonnegative order at every cusp. -/
lemma orderAtCusp_nonneg {c : OnePoint ℝ} (hc : IsCusp c G) (f : F) :
    0 ≤ orderAtCusp G k c f := by
  have hsc : (cuspScalingMatrix c)⁻¹ • c = ∞ :=
    inv_smul_eq_iff.mpr (cuspScalingMatrix_smul c).symm
  have : Fact (IsCusp ∞ (toConjAct (cuspScalingMatrix c)⁻¹ • G)) :=
    ⟨by simpa [hsc] using hc.smul (cuspScalingMatrix c)⁻¹⟩
  have : 0 ≤ orderAtInfty (⇑f ∣[k] cuspScalingMatrix c) := by
    simpa only [ModularForm.coe_translate] using (ModularFormClass.bdd_at_infty
      (ModularForm.translate f (cuspScalingMatrix c))).orderAtInfty_nonneg
  exact mul_nonneg (mod_cast Subgroup.widthInfty_nonneg _) this

/-- A modular form has nonnegative order at every cusp orbit. -/
lemma orderAtCuspOrbit_nonneg [DiscreteTopology G] (c : CuspOrbits G) (f : F) :
    0 ≤ orderAtCuspOrbit G k c f :=
  Quotient.inductionOn c (orderAtCusp_nonneg k ·.property f)

variable (G) in
/--
The total order of vanishing of `F` at all cusp orbits.

(This quantity plays a key role in the proof of the finite-dimensionality of modular forms spaces.)
-/
@[expose] noncomputable def totalCuspOrder [G.IsArithmetic] (f : F) : EReal :=
  letI : Fintype (CuspOrbits G) := Fintype.ofFinite _
  ∑ c : CuspOrbits G, orderAtCuspOrbit G k c f

/-- The contribution of one cusp orbit is at most the total cusp order. -/
lemma orderAtCuspOrbit_le_totalCuspOrder [G.IsArithmetic] (c : CuspOrbits G) (f : F) :
    orderAtCuspOrbit G k c f ≤ totalCuspOrder G k f := by
  let : Fintype (CuspOrbits G) := Fintype.ofFinite _
  exact Finset.single_le_sum (fun d _ ↦ orderAtCuspOrbit_nonneg k d f) (Finset.mem_univ c)

lemma totalCuspOrder_nonneg [G.IsArithmetic] (f : F) : 0 ≤ totalCuspOrder G k f :=
  Finset.sum_nonneg fun c _ ↦ orderAtCuspOrbit_nonneg k c f

/-- Translation preserves the order at the corresponding cusp orbit. -/
lemma orderAtCuspOrbit_translate [DiscreteTopology G] (c : CuspOrbits G)
    (g : GL (Fin 2) ℝ) (f : F) :
    orderAtCuspOrbit (toConjAct g⁻¹ • G) k (CuspOrbits.conj G g⁻¹ c)
      (ModularForm.translate f g) = orderAtCuspOrbit G k c f := by
  induction c using Quotient.inductionOn with | h c =>
  simpa only [CuspOrbits.conj_mk, orderAtCuspOrbit_mk, ModularForm.coe_translate] using
    orderAtCusp_slash k c.property g f

/-- Translation preserves the total cusp order. -/
lemma totalCuspOrder_translate [G.IsArithmetic] (f : F) (g : GL (Fin 2) ℝ)
    [(toConjAct g⁻¹ • G).IsArithmetic] :
    totalCuspOrder (toConjAct g⁻¹ • G) k (ModularForm.translate f g) = totalCuspOrder G k f := by
  let := Fintype.ofFinite (CuspOrbits G)
  let := Fintype.ofFinite (CuspOrbits (toConjAct g⁻¹ • G))
  exact (Fintype.sum_bijective _ (CuspOrbits.conj_bijective G g⁻¹)
    _ _ (fun c ↦ (orderAtCuspOrbit_translate k c g f).symm)).symm

lemma qExpansion_order_le_totalCuspOrder [G.IsArithmetic] (f : F) :
    (qExpansion G.strictWidthInfty f).order ≤ G.regularityFactorInfty * totalCuspOrder G k f := by
  have hpos : 0 < G.regularityFactorInfty := by by_cases G.IsRegularAtInfty <;>
    grind [G.regularityFactorInfty_eq_one_of_isRegularAtInfty,
      G.regularityFactorInfty_eq_two_of_not_isRegularAtInfty]
  rw [← EReal.div_le_iff_le_mul (mod_cast hpos) (EReal.natCast_ne_top _),
    ← orderAtCusp_eq_qExpansion_order]
  exact orderAtCuspOrbit_le_totalCuspOrder k ⟦⟨∞, (Fact.out : IsCusp _ G)⟩⟧ f

/-- At level one there is a single cusp `∞`, of width one, so the total cusp order is equal to the
order at `∞`. -/
lemma totalCuspOrder_SL2Z {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    totalCuspOrder 𝒮ℒ k f = orderAtInfty f := by
  simp [-Finset.univ_unique, totalCuspOrder, Fintype.sum_subsingleton _ cuspOrbitInfty,
    orderAtCusp_infty Fact.out]

end UpperHalfPlane
