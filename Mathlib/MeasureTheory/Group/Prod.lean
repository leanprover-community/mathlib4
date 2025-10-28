/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measure theory in the product of groups
In this file we show properties about measure theory in products of measurable groups
and properties of iterated integrals in measurable groups.

These lemmas show the uniqueness of left invariant measures on measurable groups, up to
scaling. In this file we follow the proof and refer to the book *Measure Theory* by Paul Halmos.

The idea of the proof is to use the translation invariance of measures to prove `μ(t) = c * μ(s)`
for two sets `s` and `t`, where `c` is a constant that does not depend on `μ`. Let `e` and `f` be
the characteristic functions of `s` and `t`.
Assume that `μ` and `ν` are left-invariant measures. Then the map `(x, y) ↦ (y * x, x⁻¹)`
preserves the measure `μ × ν`, which means that
```
  ∫ x, ∫ y, h x y ∂ν ∂μ = ∫ x, ∫ y, h (y * x) x⁻¹ ∂ν ∂μ
```
If we apply this to `h x y := e x * f y⁻¹ / ν ((fun h ↦ h * y⁻¹) ⁻¹' s)`, we can rewrite the RHS to
`μ(t)`, and the LHS to `c * μ(s)`, where `c = c(ν)` does not depend on `μ`.
Applying this to `μ` and to `ν` gives `μ (t) / μ (s) = ν (t) / ν (s)`, which is the uniqueness up to
scalar multiplication.

The proof in [Halmos] seems to contain an omission in §60 Th. A, see
`MeasureTheory.measure_lintegral_div_measure`.

Note that this theory only applies in measurable groups, i.e., when multiplication and inversion
are measurable. This is not the case in general in locally compact groups, or even in compact
groups, when the topology is not second-countable. For arguments along the same line, but using
continuous functions instead of measurable sets and working in the general locally compact
setting, see the file `Mathlib/MeasureTheory/Measure/Haar/Unique.lean`.
-/


noncomputable section

open Set hiding prod_eq

open Function MeasureTheory

open Filter hiding map

open scoped ENNReal Pointwise MeasureTheory

variable (G : Type*) [MeasurableSpace G]
variable [Group G] [MeasurableMul₂ G]
variable (μ ν : Measure G) [SFinite ν] [SFinite μ] {s : Set G}

/-- The map `(x, y) ↦ (x, xy)` as a `MeasurableEquiv`. -/
@[to_additive /-- The map `(x, y) ↦ (x, x + y)` as a `MeasurableEquiv`. -/]
protected def MeasurableEquiv.shearMulRight [MeasurableInv G] : G × G ≃ᵐ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with
    measurable_toFun := measurable_fst.prodMk measurable_mul
    measurable_invFun := measurable_fst.prodMk <| measurable_fst.inv.mul measurable_snd }

/-- The map `(x, y) ↦ (x, y / x)` as a `MeasurableEquiv` with as inverse `(x, y) ↦ (x, yx)` -/
@[to_additive
/-- The map `(x, y) ↦ (x, y - x)` as a `MeasurableEquiv` with as inverse `(x, y) ↦ (x, y + x)`. -/]
protected def MeasurableEquiv.shearDivRight [MeasurableInv G] : G × G ≃ᵐ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.divRight with
    measurable_toFun := measurable_fst.prodMk <| measurable_snd.div measurable_fst
    measurable_invFun := measurable_fst.prodMk <| measurable_snd.mul measurable_fst }

variable {G}

namespace MeasureTheory

open Measure

section LeftInvariant

/-- The multiplicative shear mapping `(x, y) ↦ (x, xy)` preserves the measure `μ × ν`.
This condition is part of the definition of a measurable group in [Halmos, §59].
There, the map in this lemma is called `S`. -/
@[to_additive measurePreserving_prod_add
/-- The shear mapping `(x, y) ↦ (x, x + y)` preserves the measure `μ × ν`. -/]
theorem measurePreserving_prod_mul [IsMulLeftInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.1 * z.2)) (μ.prod ν) (μ.prod ν) :=
  (MeasurePreserving.id μ).skew_product measurable_mul <|
    Filter.Eventually.of_forall <| map_mul_left_eq_self ν

/-- The map `(x, y) ↦ (y, yx)` sends the measure `μ × ν` to `ν × μ`.
This is the map `SR` in [Halmos, §59].
`S` is the map `(x, y) ↦ (x, xy)` and `R` is `Prod.swap`. -/
@[to_additive measurePreserving_prod_add_swap
/-- The map `(x, y) ↦ (y, y + x)` sends the measure `μ × ν` to `ν × μ`. -/]
theorem measurePreserving_prod_mul_swap [IsMulLeftInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.2, z.2 * z.1)) (μ.prod ν) (ν.prod μ) :=
  (measurePreserving_prod_mul ν μ).comp measurePreserving_swap

@[to_additive]
theorem measurable_measure_mul_right (hs : MeasurableSet s) :
    Measurable fun x => μ ((fun y => y * x) ⁻¹' s) := by
  suffices
    Measurable fun y =>
      μ ((fun x => (x, y)) ⁻¹' ((fun z : G × G => ((1 : G), z.1 * z.2)) ⁻¹' univ ×ˢ s))
    by convert this using 1; ext1 x; congr 1 with y : 1; simp
  apply measurable_measure_prodMk_right
  apply measurable_const.prodMk measurable_mul (MeasurableSet.univ.prod hs)
  infer_instance

variable [MeasurableInv G]

/-- The map `(x, y) ↦ (x, x⁻¹y)` is measure-preserving.
This is the function `S⁻¹` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)`. -/
@[to_additive measurePreserving_prod_neg_add
/-- The map `(x, y) ↦ (x, - x + y)` is measure-preserving. -/]
theorem measurePreserving_prod_inv_mul [IsMulLeftInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.1⁻¹ * z.2)) (μ.prod ν) (μ.prod ν) :=
  (measurePreserving_prod_mul μ ν).symm <| MeasurableEquiv.shearMulRight G

variable [IsMulLeftInvariant μ]

/-- The map `(x, y) ↦ (y, y⁻¹x)` sends `μ × ν` to `ν × μ`.
This is the function `S⁻¹R` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)` and `R` is `Prod.swap`. -/
@[to_additive measurePreserving_prod_neg_add_swap
/-- The map `(x, y) ↦ (y, - y + x)` sends `μ × ν` to `ν × μ`. -/]
theorem measurePreserving_prod_inv_mul_swap :
    MeasurePreserving (fun z : G × G => (z.2, z.2⁻¹ * z.1)) (μ.prod ν) (ν.prod μ) :=
  (measurePreserving_prod_inv_mul ν μ).comp measurePreserving_swap

/-- The map `(x, y) ↦ (yx, x⁻¹)` is measure-preserving.
This is the function `S⁻¹RSR` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)` and `R` is `Prod.swap`. -/
@[to_additive measurePreserving_add_prod_neg
/-- The map `(x, y) ↦ (y + x, - x)` is measure-preserving. -/]
theorem measurePreserving_mul_prod_inv [IsMulLeftInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.prod ν) (μ.prod ν) := by
  convert (measurePreserving_prod_inv_mul_swap ν μ).comp (measurePreserving_prod_mul_swap μ ν)
    using 1
  ext1 ⟨x, y⟩
  simp_rw [Function.comp_apply, mul_inv_rev, inv_mul_cancel_right]

@[to_additive (attr := fun_prop)]
theorem quasiMeasurePreserving_inv : QuasiMeasurePreserving (Inv.inv : G → G) μ μ := by
  refine ⟨measurable_inv, AbsolutelyContinuous.mk fun s hsm hμs => ?_⟩
  rw [map_apply measurable_inv hsm, inv_preimage]
  have hf : Measurable fun z : G × G => (z.2 * z.1, z.1⁻¹) :=
    (measurable_snd.mul measurable_fst).prodMk measurable_fst.inv
  suffices map (fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.prod μ) (s⁻¹ ×ˢ s⁻¹) = 0 by
    simpa only [(measurePreserving_mul_prod_inv μ μ).map_eq, prod_prod, mul_eq_zero (M₀ := ℝ≥0∞),
      or_self_iff] using this
  have hsm' : MeasurableSet (s⁻¹ ×ˢ s⁻¹) := hsm.inv.prod hsm.inv
  simp_rw [map_apply hf hsm', prod_apply_symm (μ := μ) (ν := μ) (hf hsm'), preimage_preimage,
    mk_preimage_prod, inv_preimage, inv_inv, measure_mono_null inter_subset_right hμs,
    lintegral_zero]

@[to_additive (attr := simp)]
theorem measure_inv_null : μ s⁻¹ = 0 ↔ μ s = 0 := by
  refine ⟨fun hs => ?_, (quasiMeasurePreserving_inv μ).preimage_null⟩
  rw [← inv_inv s]
  exact (quasiMeasurePreserving_inv μ).preimage_null hs

@[to_additive (attr := simp)]
theorem inv_ae : (ae μ)⁻¹ = ae μ := by
  refine le_antisymm (quasiMeasurePreserving_inv μ).tendsto_ae ?_
  nth_rewrite 1 [← inv_inv (ae μ)]
  exact Filter.map_mono (quasiMeasurePreserving_inv μ).tendsto_ae

@[to_additive (attr := simp)]
theorem eventuallyConst_inv_set_ae :
    EventuallyConst (s⁻¹ : Set G) (ae μ) ↔ EventuallyConst s (ae μ) := by
  rw [← inv_preimage, eventuallyConst_preimage, Filter.map_inv, inv_ae]

@[to_additive]
theorem inv_absolutelyContinuous : μ.inv ≪ μ :=
  (quasiMeasurePreserving_inv μ).absolutelyContinuous

@[to_additive]
theorem absolutelyContinuous_inv : μ ≪ μ.inv := by
  refine AbsolutelyContinuous.mk fun s _ => ?_
  simp_rw [inv_apply μ s, measure_inv_null, imp_self]

@[to_additive]
theorem lintegral_lintegral_mul_inv [IsMulLeftInvariant ν] (f : G → G → ℝ≥0∞)
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    (∫⁻ x, ∫⁻ y, f (y * x) x⁻¹ ∂ν ∂μ) = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ := by
  have h : Measurable fun z : G × G => (z.2 * z.1, z.1⁻¹) :=
    (measurable_snd.mul measurable_fst).prodMk measurable_fst.inv
  have h2f : AEMeasurable (uncurry fun x y => f (y * x) x⁻¹) (μ.prod ν) :=
    hf.comp_quasiMeasurePreserving (measurePreserving_mul_prod_inv μ ν).quasiMeasurePreserving
  simp_rw [lintegral_lintegral h2f, lintegral_lintegral hf]
  conv_rhs => rw [← (measurePreserving_mul_prod_inv μ ν).map_eq]
  symm
  exact
    lintegral_map' (hf.mono' (measurePreserving_mul_prod_inv μ ν).map_eq.absolutelyContinuous)
      h.aemeasurable

@[to_additive]
theorem measure_mul_right_null (y : G) : μ ((fun x => x * y) ⁻¹' s) = 0 ↔ μ s = 0 :=
  calc
    μ ((fun x => x * y) ⁻¹' s) = 0 ↔ μ ((fun x => y⁻¹ * x) ⁻¹' s⁻¹)⁻¹ = 0 := by
      simp_rw [← inv_preimage, preimage_preimage, mul_inv_rev, inv_inv]
    _ ↔ μ s = 0 := by simp only [measure_inv_null μ, measure_preimage_mul]

@[to_additive]
theorem measure_mul_right_ne_zero (h2s : μ s ≠ 0) (y : G) : μ ((fun x => x * y) ⁻¹' s) ≠ 0 :=
  (not_congr (measure_mul_right_null μ y)).mpr h2s

@[to_additive]
theorem absolutelyContinuous_map_mul_right (g : G) : μ ≪ map (· * g) μ := by
  refine AbsolutelyContinuous.mk fun s hs => ?_
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null]; exact id

@[to_additive]
theorem absolutelyContinuous_map_div_left (g : G) : μ ≪ map (fun h => g / h) μ := by
  simp_rw [div_eq_mul_inv]
  have := map_map (μ := μ) (measurable_const_mul g) measurable_inv
  simp only [Function.comp_def] at this
  rw [← this]
  conv_lhs => rw [← map_mul_left_eq_self μ g]
  exact (absolutelyContinuous_inv μ).map (measurable_const_mul g)

/-- This is the computation performed in the proof of [Halmos, §60 Th. A]. -/
@[to_additive /-- This is the computation performed in the proof of [Halmos, §60 Th. A]. -/]
theorem measure_mul_lintegral_eq [IsMulLeftInvariant ν] (sm : MeasurableSet s) (f : G → ℝ≥0∞)
    (hf : Measurable f) : (μ s * ∫⁻ y, f y ∂ν) = ∫⁻ x, ν ((fun z => z * x) ⁻¹' s) * f x⁻¹ ∂μ := by
  rw [← setLIntegral_one, ← lintegral_indicator sm,
    ← lintegral_lintegral_mul (measurable_const.indicator sm).aemeasurable hf.aemeasurable,
    ← lintegral_lintegral_mul_inv μ ν]
  swap
  · exact (((measurable_const.indicator sm).comp measurable_fst).mul
      (hf.comp measurable_snd)).aemeasurable
  have ms :
    ∀ x : G, Measurable fun y => ((fun z => z * x) ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) y :=
    fun x => measurable_const.indicator (measurable_mul_const _ sm)
  have : ∀ x y, s.indicator (fun _ : G => (1 : ℝ≥0∞)) (y * x) =
      ((fun z => z * x) ⁻¹' s).indicator (fun b : G => 1) y := by
    intro x y; symm; convert indicator_comp_right (M := ℝ≥0∞) fun y => y * x using 2; ext1; rfl
  simp_rw [this, lintegral_mul_const _ (ms _), lintegral_indicator (measurable_mul_const _ sm),
    setLIntegral_one]

/-- Any two nonzero left-invariant measures are absolutely continuous w.r.t. each other. -/
@[to_additive
/-- Any two nonzero left-invariant measures are absolutely continuous w.r.t. each other. -/]
theorem absolutelyContinuous_of_isMulLeftInvariant [IsMulLeftInvariant ν] (hν : ν ≠ 0) : μ ≪ ν := by
  refine AbsolutelyContinuous.mk fun s sm hνs => ?_
  have h1 := measure_mul_lintegral_eq μ ν sm 1 measurable_one
  simp_rw [Pi.one_apply, lintegral_one, mul_one, (measure_mul_right_null ν _).mpr hνs,
    lintegral_zero, mul_eq_zero (M₀ := ℝ≥0∞), measure_univ_eq_zero.not.mpr hν, or_false] at h1
  exact h1

section SigmaFinite

variable (μ' ν' : Measure G) [SigmaFinite μ'] [SigmaFinite ν'] [IsMulLeftInvariant μ']
  [IsMulLeftInvariant ν']

@[to_additive]
theorem ae_measure_preimage_mul_right_lt_top (hμs : μ' s ≠ ∞) :
    ∀ᵐ x ∂μ', ν' ((· * x) ⁻¹' s) < ∞ := by
  wlog sm : MeasurableSet s generalizing s
  · filter_upwards [this ((measure_toMeasurable _).trans_ne hμs) (measurableSet_toMeasurable ..)]
      with x hx using lt_of_le_of_lt (by gcongr; apply subset_toMeasurable) hx
  refine ae_of_forall_measure_lt_top_ae_restrict' ν'.inv _ ?_
  intro A hA _ h3A
  simp only [ν'.inv_apply] at h3A
  apply ae_lt_top (measurable_measure_mul_right ν' sm)
  have h1 := measure_mul_lintegral_eq μ' ν' sm (A⁻¹.indicator 1) (measurable_one.indicator hA.inv)
  rw [lintegral_indicator hA.inv] at h1
  simp_rw [Pi.one_apply, setLIntegral_one, ← image_inv_eq_inv, indicator_image inv_injective,
    image_inv_eq_inv, ← indicator_mul_right _ fun x => ν' ((· * x) ⁻¹' s), Function.comp,
    Pi.one_apply, mul_one] at h1
  rw [← lintegral_indicator hA, ← h1]
  finiteness

@[to_additive]
theorem ae_measure_preimage_mul_right_lt_top_of_ne_zero (h2s : ν' s ≠ 0) (h3s : ν' s ≠ ∞) :
    ∀ᵐ x ∂μ', ν' ((fun y => y * x) ⁻¹' s) < ∞ := by
  refine (ae_measure_preimage_mul_right_lt_top ν' ν' h3s).filter_mono ?_
  refine (absolutelyContinuous_of_isMulLeftInvariant μ' ν' ?_).ae_le
  refine mt ?_ h2s
  intro hν
  rw [hν, Measure.coe_zero, Pi.zero_apply]

/-- A technical lemma relating two different measures. This is basically [Halmos, §60 Th. A].
  Note that if `f` is the characteristic function of a measurable set `t` this states that
  `μ t = c * μ s` for a constant `c` that does not depend on `μ`.

  Note: There is a gap in the last step of the proof in [Halmos].
  In the last line, the equality `g(x⁻¹)ν(sx⁻¹) = f(x)` holds if we can prove that
  `0 < ν(sx⁻¹) < ∞`. The first inequality follows from §59, Th. D, but the second inequality is
  not justified. We prove this inequality for almost all `x` in
  `MeasureTheory.ae_measure_preimage_mul_right_lt_top_of_ne_zero`. -/
@[to_additive
/-- A technical lemma relating two different measures. This is basically [Halmos, §60 Th. A]. Note
that if `f` is the characteristic function of a measurable set `t` this states that `μ t = c * μ s`
for a constant `c` that does not depend on `μ`.

Note: There is a gap in the last step of the proof in [Halmos]. In the last line, the equality
`g(-x) + ν(s - x) = f(x)` holds if we can prove that `0 < ν(s - x) < ∞`. The first inequality
follows from §59, Th. D, but the second inequality is not justified. We prove this inequality for
almost all `x` in `MeasureTheory.ae_measure_preimage_add_right_lt_top_of_ne_zero`. -/]
theorem measure_lintegral_div_measure (sm : MeasurableSet s) (h2s : ν' s ≠ 0) (h3s : ν' s ≠ ∞)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (μ' s * ∫⁻ y, f y⁻¹ / ν' ((· * y⁻¹) ⁻¹' s) ∂ν') = ∫⁻ x, f x ∂μ' := by
  set g := fun y => f y⁻¹ / ν' ((fun x => x * y⁻¹) ⁻¹' s)
  have hg : Measurable g :=
    (hf.comp measurable_inv).div ((measurable_measure_mul_right ν' sm).comp measurable_inv)
  simp_rw [measure_mul_lintegral_eq μ' ν' sm g hg, g, inv_inv]
  refine lintegral_congr_ae ?_
  refine (ae_measure_preimage_mul_right_lt_top_of_ne_zero μ' ν' h2s h3s).mono fun x hx => ?_
  simp_rw [ENNReal.mul_div_cancel (measure_mul_right_ne_zero ν' h2s _) hx.ne]

@[to_additive]
theorem measure_mul_measure_eq (s t : Set G) (h2s : ν' s ≠ 0) (h3s : ν' s ≠ ∞) :
    μ' s * ν' t = ν' s * μ' t := by
  wlog hs : MeasurableSet s generalizing s
  · rcases exists_measurable_superset₂ μ' ν' s with ⟨s', -, hm, hμ, hν⟩
    rw [← hμ, ← hν, this s' _ _ hm] <;> rwa [hν]
  wlog ht : MeasurableSet t generalizing t
  · rcases exists_measurable_superset₂ μ' ν' t with ⟨t', -, hm, hμ, hν⟩
    rw [← hμ, ← hν, this _ hm]
  have h1 := measure_lintegral_div_measure ν' ν' hs h2s h3s (t.indicator fun _ => 1)
    (measurable_const.indicator ht)
  have h2 := measure_lintegral_div_measure μ' ν' hs h2s h3s (t.indicator fun _ => 1)
    (measurable_const.indicator ht)
  rw [lintegral_indicator ht, setLIntegral_one] at h1 h2
  rw [← h1, mul_left_comm, h2]

/-- Left invariant Borel measures on a measurable group are unique (up to a scalar). -/
@[to_additive
/-- Left invariant Borel measures on an additive measurable group are unique (up to a scalar). -/]
theorem measure_eq_div_smul (h2s : ν' s ≠ 0) (h3s : ν' s ≠ ∞) :
    μ' = (μ' s / ν' s) • ν' := by
  ext1 t -
  rw [smul_apply, smul_eq_mul, mul_comm, ← mul_div_assoc, mul_comm,
    measure_mul_measure_eq μ' ν' s t h2s h3s, mul_div_assoc, ENNReal.mul_div_cancel h2s h3s]

end SigmaFinite

end LeftInvariant

section RightInvariant

@[to_additive measurePreserving_prod_add_right]
theorem measurePreserving_prod_mul_right [IsMulRightInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.2 * z.1)) (μ.prod ν) (μ.prod ν) :=
  MeasurePreserving.skew_product (g := fun x y => y * x) (MeasurePreserving.id μ)
    (measurable_snd.mul measurable_fst) <| Filter.Eventually.of_forall <| map_mul_right_eq_self ν

/-- The map `(x, y) ↦ (y, xy)` sends the measure `μ × ν` to `ν × μ`. -/
@[to_additive measurePreserving_prod_add_swap_right
/-- The map `(x, y) ↦ (y, x + y)` sends the measure `μ × ν` to `ν × μ`. -/]
theorem measurePreserving_prod_mul_swap_right [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.2, z.1 * z.2)) (μ.prod ν) (ν.prod μ) :=
  (measurePreserving_prod_mul_right ν μ).comp measurePreserving_swap

/-- The map `(x, y) ↦ (xy, y)` preserves the measure `μ × ν`. -/
@[to_additive measurePreserving_add_prod
/-- The map `(x, y) ↦ (x + y, y)` preserves the measure `μ × ν`. -/]
theorem measurePreserving_mul_prod [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.1 * z.2, z.2)) (μ.prod ν) (μ.prod ν) :=
  measurePreserving_swap.comp (measurePreserving_prod_mul_swap_right μ ν)

variable [MeasurableInv G]

/-- The map `(x, y) ↦ (x, y / x)` is measure-preserving. -/
@[to_additive measurePreserving_prod_sub
/-- The map `(x, y) ↦ (x, y - x)` is measure-preserving. -/]
theorem measurePreserving_prod_div [IsMulRightInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.2 / z.1)) (μ.prod ν) (μ.prod ν) :=
  (measurePreserving_prod_mul_right μ ν).symm (MeasurableEquiv.shearDivRight G).symm

/-- The map `(x, y) ↦ (y, x / y)` sends `μ × ν` to `ν × μ`. -/
@[to_additive measurePreserving_prod_sub_swap
/-- The map `(x, y) ↦ (y, x - y)` sends `μ × ν` to `ν × μ`. -/]
theorem measurePreserving_prod_div_swap [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.2, z.1 / z.2)) (μ.prod ν) (ν.prod μ) :=
  (measurePreserving_prod_div ν μ).comp measurePreserving_swap

/-- The map `(x, y) ↦ (x / y, y)` preserves the measure `μ × ν`. -/
@[to_additive measurePreserving_sub_prod
/-- The map `(x, y) ↦ (x - y, y)` preserves the measure `μ × ν`. -/]
theorem measurePreserving_div_prod [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.1 / z.2, z.2)) (μ.prod ν) (μ.prod ν) :=
  measurePreserving_swap.comp (measurePreserving_prod_div_swap μ ν)

/-- The map `(x, y) ↦ (xy, x⁻¹)` is measure-preserving. -/
@[to_additive measurePreserving_add_prod_neg_right
/-- The map `(x, y) ↦ (x + y, - x)` is measure-preserving. -/]
theorem measurePreserving_mul_prod_inv_right [IsMulRightInvariant μ] [IsMulRightInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1 * z.2, z.1⁻¹)) (μ.prod ν) (μ.prod ν) := by
  convert (measurePreserving_prod_div_swap ν μ).comp (measurePreserving_prod_mul_swap_right μ ν)
    using 1
  ext1 ⟨x, y⟩
  simp_rw [Function.comp_apply, div_mul_eq_div_div_swap, div_self', one_div]

end RightInvariant

section QuasiMeasurePreserving

/-- The map `(x, y) ↦ x * y` is quasi-measure-preserving. -/
@[to_additive (attr := fun_prop) /-- The map `(x, y) ↦ x + y` is quasi-measure-preserving. -/]
theorem quasiMeasurePreserving_mul [IsMulLeftInvariant ν] :
    QuasiMeasurePreserving (fun p ↦ p.1 * p.2) (μ.prod ν) ν :=
  quasiMeasurePreserving_snd.comp (measurePreserving_prod_mul _ _).quasiMeasurePreserving

/-- The map `(x, y) ↦ y * x` is quasi-measure-preserving. -/
@[to_additive (attr := fun_prop) /-- The map `(x, y) ↦ y + x` is quasi-measure-preserving. -/]
theorem quasiMeasurePreserving_mul_swap [IsMulLeftInvariant μ] :
    QuasiMeasurePreserving (fun p ↦ p.2 * p.1) (μ.prod ν) μ :=
  quasiMeasurePreserving_snd.comp (measurePreserving_prod_mul_swap _ _).quasiMeasurePreserving

section MeasurableInv

variable [MeasurableInv G]

/-- The map `(x, y) ↦ x⁻¹ * y` is quasi-measure-preserving. -/
@[to_additive (attr := fun_prop) /-- The map `(x, y) ↦ -x + y` is quasi-measure-preserving. -/]
theorem quasiMeasurePreserving_inv_mul [IsMulLeftInvariant ν] :
    QuasiMeasurePreserving (fun p ↦ p.1⁻¹ * p.2) (μ.prod ν) ν :=
  quasiMeasurePreserving_snd.comp (measurePreserving_prod_inv_mul _ _).quasiMeasurePreserving

/-- The map `(x, y) ↦ y⁻¹ * x` is quasi-measure-preserving. -/
@[to_additive (attr := fun_prop) /-- The map `(x, y) ↦ -y + x` is quasi-measure-preserving. -/]
theorem quasiMeasurePreserving_inv_mul_swap [IsMulLeftInvariant μ] :
    QuasiMeasurePreserving (fun p ↦ p.2⁻¹ * p.1) (μ.prod ν) μ :=
  quasiMeasurePreserving_snd.comp (measurePreserving_prod_inv_mul_swap _ _).quasiMeasurePreserving

@[to_additive (attr := fun_prop)]
theorem quasiMeasurePreserving_inv_of_right_invariant [IsMulRightInvariant μ] :
    QuasiMeasurePreserving (Inv.inv : G → G) μ μ := by
  rw [← μ.inv_inv]
  exact
    (quasiMeasurePreserving_inv μ.inv).mono (inv_absolutelyContinuous μ.inv)
      (absolutelyContinuous_inv μ.inv)

@[to_additive]
theorem quasiMeasurePreserving_div_left [IsMulLeftInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => g / h) μ μ := by
  simp_rw [div_eq_mul_inv]
  exact
    (measurePreserving_mul_left μ g).quasiMeasurePreserving.comp (quasiMeasurePreserving_inv μ)

@[to_additive]
theorem quasiMeasurePreserving_div_left_of_right_invariant [IsMulRightInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => g / h) μ μ := by
  rw [← μ.inv_inv]
  exact
    (quasiMeasurePreserving_div_left μ.inv g).mono (inv_absolutelyContinuous μ.inv)
      (absolutelyContinuous_inv μ.inv)

@[to_additive]
theorem quasiMeasurePreserving_div_of_right_invariant [IsMulRightInvariant μ] :
    QuasiMeasurePreserving (fun p : G × G => p.1 / p.2) (μ.prod ν) μ := by
  refine QuasiMeasurePreserving.prod_of_left measurable_div (Eventually.of_forall fun y => ?_)
  exact (measurePreserving_div_right μ y).quasiMeasurePreserving

@[to_additive]
theorem quasiMeasurePreserving_div [IsMulLeftInvariant μ] :
    QuasiMeasurePreserving (fun p : G × G => p.1 / p.2) (μ.prod ν) μ :=
  (quasiMeasurePreserving_div_of_right_invariant μ.inv ν).mono
    ((absolutelyContinuous_inv μ).prod AbsolutelyContinuous.rfl) (inv_absolutelyContinuous μ)

/-- A *left*-invariant measure is quasi-preserved by *right*-multiplication.
This should not be confused with `(measurePreserving_mul_right μ g).quasiMeasurePreserving`. -/
@[to_additive (attr := fun_prop)
/-- A *left*-invariant measure is quasi-preserved by *right*-addition.
This should not be confused with `(measurePreserving_add_right μ g).quasiMeasurePreserving`. -/]
theorem quasiMeasurePreserving_mul_right [IsMulLeftInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => h * g) μ μ := by
  refine ⟨measurable_mul_const g, AbsolutelyContinuous.mk fun s hs => ?_⟩
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null]; exact id

/-- A *right*-invariant measure is quasi-preserved by *left*-multiplication.
This should not be confused with `(measurePreserving_mul_left μ g).quasiMeasurePreserving`. -/
@[to_additive (attr := fun_prop)
/-- A *right*-invariant measure is quasi-preserved by *left*-addition.
This should not be confused with `(measurePreserving_add_left μ g).quasiMeasurePreserving`. -/]
theorem quasiMeasurePreserving_mul_left [IsMulRightInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => g * h) μ μ := by
  have :=
    (quasiMeasurePreserving_mul_right μ.inv g⁻¹).mono (inv_absolutelyContinuous μ.inv)
      (absolutelyContinuous_inv μ.inv)
  rw [μ.inv_inv] at this
  have :=
    (quasiMeasurePreserving_inv_of_right_invariant μ).comp
      (this.comp (quasiMeasurePreserving_inv_of_right_invariant μ))
  simp_rw [Function.comp_def, mul_inv_rev, inv_inv] at this
  exact this

end MeasurableInv

end QuasiMeasurePreserving

end MeasureTheory
