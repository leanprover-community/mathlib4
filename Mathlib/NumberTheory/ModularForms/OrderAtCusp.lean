/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

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

namespace UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise in
/-- The width-weighted order is unchanged by an upper triangular change of cusp coordinate. -/
lemma width_mul_orderAtInfty_slash_of_upperTriangular
    (G : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology G] (hw : 0 < G.widthInfty)
    (f : ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ) (hg : g 1 0 = 0)
    (ha : 0 < g 0 0 / g 1 1) :
    (ConjAct.toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) =
      G.widthInfty * orderAtInfty f := by
  rw [Subgroup.widthInfty_conj_of_upperTriangular hw hg ha,
    orderAtInfty_slash_of_upperTriangular f k g hg, abs_of_pos ha,
    ← mul_assoc, ← EReal.coe_mul, div_mul_cancel₀ _ ha.ne']

open OnePoint in
open scoped MatrixGroups ModularForm Pointwise in
lemma width_mul_orderAtInfty_slash_eq_of_smul_infty_eq
    (G : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology G]
    (f : ℍ → ℂ) (k : ℤ) (g h : GL (Fin 2) ℝ)
    (hw : 0 < (ConjAct.toConjAct g⁻¹ • G).widthInfty)
    (hcg : g • (∞ : OnePoint ℝ) = h • ∞)
    (hdg : 0 < g.det.val) (hdh : 0 < h.det.val) :
    (ConjAct.toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) =
      (ConjAct.toConjAct h⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] h) := by
  let t := g⁻¹ * h
  have ht : t 1 0 = 0 := by
    apply OnePoint.smul_infty_eq_self_iff.mp
    simp only [t, mul_smul, ← hcg, inv_smul_smul]
  have hd : 0 < t.det.val := by
    simpa only [t, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val] using
      mul_pos (inv_pos.mpr hdg) hdh
  have ha : 0 < t 0 0 / t 1 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, ht, mul_zero,
      sub_zero] at hd
    exact div_pos_iff.mpr (mul_pos_iff.mp hd)
  have heq := width_mul_orderAtInfty_slash_of_upperTriangular
    (ConjAct.toConjAct g⁻¹ • G) hw (f ∣[k] g) k t ht ha
  simpa only [t, mul_inv_rev, inv_inv, ← ConjAct.toConjAct_mul, ← mul_smul,
    mul_inv_cancel_right, ← SlashAction.slash_mul, mul_inv_cancel_left] using heq.symm

section Cusps

open OnePoint Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise

/-- Independence of the scaling matrix, allowing either orientation. -/
lemma width_mul_orderAtInfty_slash_eq_of_smul_infty_eq'
    (G : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology G]
    (f : ℍ → ℂ) (k : ℤ) (g h : GL (Fin 2) ℝ)
    (hw : 0 < (ConjAct.toConjAct g⁻¹ • G).widthInfty)
    (hcg : g • (∞ : OnePoint ℝ) = h • ∞) :
    (ConjAct.toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) =
      (ConjAct.toConjAct h⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] h) := by
  let t := g⁻¹ * h
  have ht : t 1 0 = 0 := by
    apply OnePoint.smul_infty_eq_self_iff.mp
    simp only [t, mul_smul, ← hcg, inv_smul_smul]
  have ha : 0 < |t 0 0 / t 1 1| := by
    simpa [Matrix.det_fin_two, ht] using t.det_ne_zero
  have heq : (ConjAct.toConjAct t⁻¹ • (ConjAct.toConjAct g⁻¹ • G)).widthInfty *
      orderAtInfty ((f ∣[k] g) ∣[k] t) =
        (ConjAct.toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) := by
    rw [Subgroup.widthInfty_conj_of_upperTriangular_abs hw ht,
      orderAtInfty_slash_of_upperTriangular _ k t ht,
      ← mul_assoc, ← EReal.coe_mul, div_mul_cancel₀ _ ha.ne']
  simpa only [t, mul_inv_rev, inv_inv, ← ConjAct.toConjAct_mul, ← mul_smul,
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
  (ConjAct.toConjAct (cuspScalingMatrix c)⁻¹ • G).widthInfty *
    orderAtInfty (f ∣[k] cuspScalingMatrix c)

/-- Compute the order at a cusp using any scaling matrix, of either orientation. -/
lemma orderAtCusp_eq (G : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology G]
    [G.HasDetPlusMinusOne] (k : ℤ) {c : OnePoint ℝ} (hc : IsCusp c G)
    (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) (hg : g • ∞ = c) :
    orderAtCusp G k c f = (ConjAct.toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) := by
  have hchosen : cuspScalingMatrix c • ∞ = c := cuspScalingMatrix_smul c
  have hw : 0 < (ConjAct.toConjAct (cuspScalingMatrix c)⁻¹ • G).widthInfty := by
    have heq : (cuspScalingMatrix c)⁻¹ • c = ∞ := inv_smul_eq_iff.mpr hchosen.symm
    simpa only [Subgroup.widthInfty_pos_iff, heq] using hc.smul (cuspScalingMatrix c)⁻¹
  exact width_mul_orderAtInfty_slash_eq_of_smul_infty_eq' G f k
    (cuspScalingMatrix c) g hw (hchosen.trans hg.symm)

/-- At infinity, the order at a cusp is the width times the exponential order. -/
lemma orderAtCusp_infty (G : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology G]
    [G.HasDetPlusMinusOne] (k : ℤ) (hc : IsCusp ∞ G) (f : ℍ → ℂ) :
    orderAtCusp G k ∞ f = G.widthInfty * orderAtInfty f := by
  simpa using orderAtCusp_eq G k hc f 1 (by simp)

/-- Changing coordinates transports the cusp and the level, preserving the cusp order. -/
lemma orderAtCusp_slash (G : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology G]
    [G.HasDetPlusMinusOne] (k : ℤ) {c : OnePoint ℝ} (hc : IsCusp c G)
    (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) :
    orderAtCusp (ConjAct.toConjAct g⁻¹ • G) k (g⁻¹ • c) (f ∣[k] g) =
      orderAtCusp G k c f := by
  rw [orderAtCusp_eq _ k (hc.smul g⁻¹) _ (g⁻¹ * cuspScalingMatrix c)
      (by simp only [mul_smul, cuspScalingMatrix_smul]),
    orderAtCusp_eq G k hc f (cuspScalingMatrix c) (cuspScalingMatrix_smul c)]
  simp only [mul_inv_rev, inv_inv, ← ConjAct.toConjAct_mul, ← mul_smul,
    mul_inv_cancel_right, ← SlashAction.slash_mul, mul_inv_cancel_left]

variable {F : Type*} (G : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology G]
  [G.HasDetPlusMinusOne] (k : ℤ) [FunLike F ℍ ℂ] [SlashInvariantFormClass F G k]

/-- The order of a slash-invariant form is constant on each cusp orbit. -/
lemma orderAtCusp_smul {c : OnePoint ℝ} (hc : IsCusp c G) (f : F)
    {g : GL (Fin 2) ℝ} (hg : g ∈ G) :
    orderAtCusp G k (g • c) f = orderAtCusp G k c f := by
  rw [orderAtCusp_eq G k (hc.smul_of_mem hg) f (g * cuspScalingMatrix c)
    (by rw [mul_smul, cuspScalingMatrix_smul]),
    orderAtCusp_eq G k hc f (cuspScalingMatrix c) (cuspScalingMatrix_smul c)]
  simp only [mul_inv_rev, ConjAct.toConjAct_mul, mul_smul,
    G.conjAct_pointwise_smul_eq_self (G.le_normalizer (G.inv_mem hg)),
    SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f g hg]

/-- The width-weighted order of a slash-invariant form at a cusp orbit. -/
noncomputable def orderAtCuspOrbit (c : CuspOrbits G) (f : F) : EReal :=
  Quotient.lift (fun c ↦ orderAtCusp G k c.val f)
    (fun ⟨c, _⟩ ⟨d, hd⟩ ⟨⟨g, hG⟩, hg⟩ ↦ by
      have heq : g • d = c := congr(Subtype.val $hg)
      simpa only [heq] using orderAtCusp_smul G k hd f hG) c

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

open scoped MatrixGroups ModularForm

variable {F : Type*} (G : Subgroup (GL (Fin 2) ℝ))
  [G.HasDetPlusMinusOne] (k : ℤ) [FunLike F ℍ ℂ] [ModularFormClass F G k]

lemma orderAtCusp_eq_qExpansion_order [DiscreteTopology G] [Fact (IsCusp OnePoint.infty G)]
    (f : F) : orderAtCusp G k OnePoint.infty f =
      (qExpansion G.strictWidthInfty f).order / G.regularityFactorInfty := by
  rw [orderAtCusp_infty _ _ Fact.out,
      orderAtInfty_eq_qExpansion_order (Subgroup.strictWidthInfty_pos_iff.mpr Fact.out)
        (SlashInvariantFormClass.periodic_comp_ofComplex f G.strictWidthInfty_mem_strictPeriods)
        (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)]
  rw [G.strictWidthInfty_eq_regularityFactorInfty_mul_widthInfty,
    EReal.coe_mul, EReal.coe_natCast, EReal.mul_div, mul_comm (G.widthInfty : EReal),
    EReal.mul_div_mul_cancel (EReal.coe_ne_bot _) (EReal.coe_ne_top _)]
  exact EReal.coe_ne_zero.mpr (Subgroup.widthInfty_pos_iff.mpr Fact.out).ne'

open scoped Pointwise in
omit [G.HasDetPlusMinusOne] in
/-- A modular form has nonnegative order at every cusp. -/
lemma orderAtCusp_nonneg {c : OnePoint ℝ} (hc : IsCusp c G)
    (f : F) : 0 ≤ orderAtCusp G k c f := by
  have hsc : (cuspScalingMatrix c)⁻¹ • c = OnePoint.infty :=
    inv_smul_eq_iff.mpr (cuspScalingMatrix_smul c).symm
  have : Fact (IsCusp OnePoint.infty
      (ConjAct.toConjAct (cuspScalingMatrix c)⁻¹ • G)) :=
    ⟨by simpa only [hsc] using hc.smul (cuspScalingMatrix c)⁻¹⟩
  exact mul_nonneg (EReal.coe_nonneg.mpr (Subgroup.widthInfty_nonneg _))
    (ModularFormClass.bdd_at_infty
      (ModularForm.translate f (cuspScalingMatrix c))).orderAtInfty_nonneg

/-- A modular form has nonnegative order at every cusp orbit. -/
lemma orderAtCuspOrbit_nonneg [DiscreteTopology G] (c : CuspOrbits G) (f : F) :
    0 ≤ orderAtCuspOrbit G k c f :=
  Quotient.inductionOn c (orderAtCusp_nonneg G k ·.property f)

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
  exact Finset.single_le_sum (fun d _ ↦ orderAtCuspOrbit_nonneg G k d f) (Finset.mem_univ c)

lemma totalCuspOrder_nonneg [G.IsArithmetic] (f : F) : 0 ≤ totalCuspOrder G k f :=
  Finset.sum_nonneg fun c _ ↦ orderAtCuspOrbit_nonneg G k c f

open scoped Pointwise in
/-- Translation preserves the order at the corresponding cusp orbit. -/
lemma orderAtCuspOrbit_translate [DiscreteTopology G] (c : CuspOrbits G) (f : F)
    (g : GL (Fin 2) ℝ) :
    orderAtCuspOrbit (ConjAct.toConjAct g⁻¹ • G) k (CuspOrbits.conj G g⁻¹ c)
      (ModularForm.translate f g) = orderAtCuspOrbit G k c f := by
  induction c using Quotient.inductionOn with
  | h c =>
    simpa only [CuspOrbits.conj_mk, orderAtCuspOrbit_mk, ModularForm.coe_translate] using
      orderAtCusp_slash G k c.property f g

open scoped Pointwise in
/-- Translation preserves the total cusp order. -/
lemma totalCuspOrder_translate [G.IsArithmetic] (f : F) (g : GL (Fin 2) ℝ)
    [(ConjAct.toConjAct g⁻¹ • G).IsArithmetic] :
    totalCuspOrder (ConjAct.toConjAct g⁻¹ • G) k (ModularForm.translate f g) =
      totalCuspOrder G k f := by
  classical
  let := Fintype.ofFinite (CuspOrbits G)
  let := Fintype.ofFinite (CuspOrbits (ConjAct.toConjAct g⁻¹ • G))
  exact (Fintype.sum_bijective _ (CuspOrbits.conj_bijective G g⁻¹)
    _ _ (fun c ↦ (orderAtCuspOrbit_translate G k c f g).symm)).symm

lemma qExpansion_order_le_totalCuspOrder [G.IsArithmetic] (f : F) :
    (qExpansion G.strictWidthInfty f).order ≤ G.regularityFactorInfty * totalCuspOrder G k f := by
  have hpos : 0 < G.regularityFactorInfty := by
    simp [Subgroup.regularityFactorInfty, apply_ite]
  rw [← EReal.div_le_iff_le_mul (mod_cast hpos) (EReal.natCast_ne_top _),
    ← orderAtCusp_eq_qExpansion_order]
  exact orderAtCuspOrbit_le_totalCuspOrder G k
    ⟦⟨OnePoint.infty, (Fact.out : IsCusp OnePoint.infty G)⟩⟧ f

omit [G.HasDetPlusMinusOne] [FunLike F ℍ ℂ] [ModularFormClass F G k] in
/-- At level one there is a single cusp, of width one. -/
lemma totalCuspOrder_SL2Z {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    totalCuspOrder 𝒮ℒ k f = orderAtInfty f := by
  classical
  let c : CuspOrbits 𝒮ℒ := ⟦⟨OnePoint.infty, (Fact.out : IsCusp OnePoint.infty 𝒮ℒ)⟩⟧
  have hc (d : CuspOrbits 𝒮ℒ) : d = c := by
    induction d using Quotient.inductionOn with | h d =>
    obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp d.property
    exact Quotient.eq.mpr ⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ g, ⟨g, rfl⟩⟩,
      Subtype.ext hg.symm⟩
  let : Unique (CuspOrbits 𝒮ℒ) := ⟨⟨c⟩, hc⟩
  have hneg : (-1 : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=
    ⟨-1, by ext i j; simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]⟩
  simp only [totalCuspOrder, Finset.univ_unique, Finset.sum_singleton, hc default]
  simp [c, orderAtCusp_infty _ _ Fact.out, Subgroup.widthInfty,
    Subgroup.adjoinNegOne_eq_self_iff.mpr hneg, Subgroup.strictWidthInfty_SL2Z]

end UpperHalfPlane
