/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Data.Complex.Abs
import Mathlib.MeasureTheory.Constructions.Polish
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Measurable parametric Stieltjes functions

We provide tools to build a measurable function `α → StieltjesFunction` with limits 0 at -∞ and 1 at
+∞ for all `a : α` from a measurable function `f : α → ℚ → ℝ`. These measurable parametric Stieltjes
functions are cumulative distribution functions (CDF) of transition kernels.
The reason for going through `ℚ` instead of defining directly a Stieltjes function is that since
`ℚ` is countable, building a measurable function is easier and we can obtain properties of the
form `∀ᵐ (a : α) ∂μ, ∀ (q : ℚ), ...` (for some measure `μ` on `α`) by proving the weaker
`∀ (q : ℚ), ∀ᵐ (a : α) ∂μ, ...`.

This construction will be possible if `f a : ℚ → ℝ` satisfies a package of properties for all `a`:
monotonicity, limits at +-∞ and a continuity property. We define `IsRatStieltjesPoint f a` to state
that this is the case at `a` and define the property `IsRatCDF f` that `f` is measurable and
`IsRatStieltjesPoint f a` for all `a`.
The function `α → StieltjesFunction` obtained by extending `f` by continuity from the right is then
called `IsRatCDF.stieltjesFunction`.

In applications, we will often only have `IsRatStieltjesPoint f a` almost surely with respect to
some measure. In order to turn that almost everywhere property into an everywhere property we define
`toRatCDF (f : α → ℚ → ℝ) := fun a q ↦ if IsRatStieltjesPoint f a then f a q else defaultRatCDF q`,
which satisfies the property `IsRatCDF (toRatCDF f)`.

Finally, we define `stieltjesOfMeasurableRat`, composition of `toRatCDF` and
`IsRatCDF.stieltjesFunction`.

## Main definitions

* `stieltjesOfMeasurableRat`: turn a measurable function `f : α → ℚ → ℝ` into a measurable
  function `α → StieltjesFunction`.

-/

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace ProbabilityTheory

variable {α β ι : Type*} [MeasurableSpace α]

section IsRatCDF

variable {f : α → ℚ → ℝ}

/-- `a : α` is a Stieltjes point for `f : α → ℚ → ℝ` if `f a` is monotone with limit 0 at -∞
and 1 at +∞ and satisfies a continuity property. -/
structure IsRatStieltjesPoint (f : α → ℚ → ℝ) (a : α) : Prop where
  mono : Monotone (f a)
  tendsto_atTop_one : Tendsto (f a) atTop (𝓝 1)
  tendsto_atBot_zero : Tendsto (f a) atBot (𝓝 0)
  iInf_rat_gt_eq : ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t

lemma isRatStieltjesPoint_unit_prod_iff (f : α → ℚ → ℝ) (a : α) :
    IsRatStieltjesPoint (fun p : Unit × α ↦ f p.2) ((), a)
      ↔ IsRatStieltjesPoint f a := by
  constructor <;>
    exact fun h ↦ ⟨h.mono, h.tendsto_atTop_one, h.tendsto_atBot_zero, h.iInf_rat_gt_eq⟩

lemma measurableSet_isRatStieltjesPoint (hf : Measurable f) :
    MeasurableSet {a | IsRatStieltjesPoint f a} := by
  have h1 : MeasurableSet {a | Monotone (f a)} := by
    change MeasurableSet {a | ∀ q r (_ : q ≤ r), f a q ≤ f a r}
    simp_rw [Set.setOf_forall]
    refine MeasurableSet.iInter (fun q ↦ ?_)
    refine MeasurableSet.iInter (fun r ↦ ?_)
    refine MeasurableSet.iInter (fun _ ↦ ?_)
    exact measurableSet_le hf.eval hf.eval
  have h2 : MeasurableSet {a | Tendsto (f a) atTop (𝓝 1)} :=
    measurableSet_tendsto _ (fun q ↦ hf.eval)
  have h3 : MeasurableSet {a | Tendsto (f a) atBot (𝓝 0)} :=
    measurableSet_tendsto _ (fun q ↦ hf.eval)
  have h4 : MeasurableSet {a | ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter (fun q ↦ ?_)
    exact measurableSet_eq_fun (measurable_iInf fun _ ↦ hf.eval) hf.eval
  suffices {a | IsRatStieltjesPoint f a}
      = ({a | Monotone (f a)} ∩ {a | Tendsto (f a) atTop (𝓝 1)} ∩ {a | Tendsto (f a) atBot (𝓝 0)}
        ∩ {a | ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t}) by
    rw [this]
    exact (((h1.inter h2).inter h3).inter h4)
  ext a
  simp only [mem_setOf_eq, mem_inter_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨⟨⟨h.mono, h.tendsto_atTop_one⟩, h.tendsto_atBot_zero⟩, h.iInf_rat_gt_eq⟩
  · exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

lemma IsRatStieltjesPoint.ite {f g : α → ℚ → ℝ} {a : α} (p : α → Prop) [DecidablePred p]
    (hf : p a → IsRatStieltjesPoint f a) (hg : ¬ p a → IsRatStieltjesPoint g a):
    IsRatStieltjesPoint (fun a ↦ if p a then f a else g a) a where
  mono := by split_ifs with h; exacts [(hf h).mono, (hg h).mono]
  tendsto_atTop_one := by
    split_ifs with h; exacts [(hf h).tendsto_atTop_one, (hg h).tendsto_atTop_one]
  tendsto_atBot_zero := by
    split_ifs with h; exacts [(hf h).tendsto_atBot_zero, (hg h).tendsto_atBot_zero]
  iInf_rat_gt_eq := by split_ifs with h; exacts [(hf h).iInf_rat_gt_eq, (hg h).iInf_rat_gt_eq]


/-- A function `f : α → ℚ → ℝ` is a (kernel) rational cumulative distribution function if it is
measurable in the first argument and if `f a` satisfies a list of properties for all `a : α`:
monotonicity between 0 at -∞ and 1 at +∞ and a form of continuity.

A function with these properties can be extended to a measurable function `α → StieltjesFunction`.
See `ProbabilityTheory.IsRatCDF.stieltjesFunction`.
-/
structure IsRatCDF (f : α → ℚ → ℝ) : Prop where
  isRatStieltjesPoint : ∀ a, IsRatStieltjesPoint f a
  measurable : Measurable f

lemma IsRatCDF.nonneg {f : α → ℚ → ℝ} (hf : IsRatCDF f) (a : α) (q : ℚ) : 0 ≤ f a q :=
  Monotone.le_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atBot_zero q

lemma IsRatCDF.le_one {f : α → ℚ → ℝ} (hf : IsRatCDF f) (a : α) (q : ℚ) : f a q ≤ 1 :=
  Monotone.ge_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atTop_one q

lemma IsRatCDF.tendsto_atTop_one {f : α → ℚ → ℝ} (hf : IsRatCDF f) (a : α) :
    Tendsto (f a) atTop (𝓝 1) := (hf.isRatStieltjesPoint a).tendsto_atTop_one

lemma IsRatCDF.tendsto_atBot_zero {f : α → ℚ → ℝ} (hf : IsRatCDF f) (a : α) :
    Tendsto (f a) atBot (𝓝 0) := (hf.isRatStieltjesPoint a).tendsto_atBot_zero

lemma IsRatCDF.iInf_rat_gt_eq {f : α → ℚ → ℝ} (hf : IsRatCDF f) (a : α) (q : ℚ) :
    ⨅ r : Ioi q, f a r = f a q := (hf.isRatStieltjesPoint a).iInf_rat_gt_eq q

end IsRatCDF

section DefaultRatCDF

/-- A function with the property `IsRatCDF`.
Used in a piecewise construction to convert a function which only satisfies the properties
defining `IsRatCDF` on some set into a true `IsRatCDF`. -/
def defaultRatCDF (q : ℚ) := if q < 0 then (0 : ℝ) else 1

lemma monotone_defaultRatCDF : Monotone defaultRatCDF := by
  unfold defaultRatCDF
  intro x y hxy
  dsimp only
  split_ifs with h_1 h_2 h_2
  exacts [le_rfl, zero_le_one, absurd (hxy.trans_lt h_2) h_1, le_rfl]

lemma defaultRatCDF_nonneg (q : ℚ) : 0 ≤ defaultRatCDF q := by
  unfold defaultRatCDF
  split_ifs
  exacts [le_rfl, zero_le_one]

lemma defaultRatCDF_le_one (q : ℚ) : defaultRatCDF q ≤ 1 := by
  unfold defaultRatCDF
  split_ifs <;> simp

lemma tendsto_defaultRatCDF_atTop : Tendsto defaultRatCDF atTop (𝓝 1) := by
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  rw [EventuallyEq, eventually_atTop]
  exact ⟨0, fun q hq => (if_neg (not_lt.mpr hq)).symm⟩

lemma tendsto_defaultRatCDF_atBot : Tendsto defaultRatCDF atBot (𝓝 0) := by
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  rw [EventuallyEq, eventually_atBot]
  refine ⟨-1, fun q hq => (if_pos (hq.trans_lt ?_)).symm⟩
  linarith

lemma iInf_rat_gt_defaultRatCDF (t : ℚ) :
    ⨅ r : Ioi t, defaultRatCDF r = defaultRatCDF t := by
  simp only [defaultRatCDF]
  have h_bdd : BddBelow (range fun r : ↥(Ioi t) ↦ ite ((r : ℚ) < 0) (0 : ℝ) 1) := by
    refine ⟨0, fun x hx ↦ ?_⟩
    obtain ⟨y, rfl⟩ := mem_range.mpr hx
    dsimp only
    split_ifs
    exacts [le_rfl, zero_le_one]
  split_ifs with h
  · refine le_antisymm ?_ (le_ciInf fun x ↦ ?_)
    · obtain ⟨q, htq, hq_neg⟩ : ∃ q, t < q ∧ q < 0 := ⟨t / 2, by linarith, by linarith⟩
      refine (ciInf_le h_bdd ⟨q, htq⟩).trans ?_
      rw [if_pos]
      rwa [Subtype.coe_mk]
    · split_ifs
      exacts [le_rfl, zero_le_one]
  · refine le_antisymm ?_ ?_
    · refine (ciInf_le h_bdd ⟨t + 1, lt_add_one t⟩).trans ?_
      split_ifs
      exacts [zero_le_one, le_rfl]
    · refine le_ciInf fun x ↦ ?_
      rw [if_neg]
      rw [not_lt] at h ⊢
      exact h.trans (mem_Ioi.mp x.prop).le

lemma isRatStieltjesPoint_defaultRatCDF (a : α) :
    IsRatStieltjesPoint (fun (_ : α) ↦ defaultRatCDF) a where
  mono := monotone_defaultRatCDF
  tendsto_atTop_one := tendsto_defaultRatCDF_atTop
  tendsto_atBot_zero := tendsto_defaultRatCDF_atBot
  iInf_rat_gt_eq := iInf_rat_gt_defaultRatCDF

lemma IsRatCDF_defaultRatCDF (α : Type*) [MeasurableSpace α] :
    IsRatCDF (fun (_ : α) (q : ℚ) ↦ defaultRatCDF q) where
  isRatStieltjesPoint := isRatStieltjesPoint_defaultRatCDF
  measurable := measurable_const

end DefaultRatCDF

section ToRatCDF

variable {f : α → ℚ → ℝ}

open Classical in
/-- Turn a function `f : α → ℚ → ℝ` into another with the property `IsRatCDF`.
Mainly useful when `f` satisfies the property `IsRatStieltjesPoint f a` almost everywhere. -/
noncomputable
def toRatCDF (f : α → ℚ → ℝ) : α → ℚ → ℝ := fun a ↦
  if IsRatStieltjesPoint f a then f a else defaultRatCDF

lemma toRatCDF_of_isRatStieltjesPoint {a : α} (h : IsRatStieltjesPoint f a) (q : ℚ) :
    toRatCDF f a q = f a q := by
  rw [toRatCDF, if_pos h]

lemma measurable_toRatCDF (hf : Measurable f) : Measurable (toRatCDF f) :=
  Measurable.ite (measurableSet_isRatStieltjesPoint hf) hf measurable_const

lemma IsRatCDF_toRatCDF (hf : Measurable f) :
    IsRatCDF (toRatCDF f) where
  isRatStieltjesPoint a := by
    classical
    exact IsRatStieltjesPoint.ite (IsRatStieltjesPoint f) id
      (fun _ ↦ isRatStieltjesPoint_defaultRatCDF a)
  measurable := measurable_toRatCDF hf

lemma toRatCDF_unit_prod (a : α) :
    toRatCDF (fun (p : Unit × α) ↦ f p.2) ((), a) = toRatCDF f a := by
  unfold toRatCDF
  rw [isRatStieltjesPoint_unit_prod_iff]

end ToRatCDF

section IsRatCDF.stieltjesFunction

variable {f : α → ℚ → ℝ} (hf : IsRatCDF f)

/-- Auxiliary definition for `IsRatCDF.stieltjesFunction`: turn `f : α → ℚ → ℝ` into a function
`α → ℝ → ℝ` by assigning to `f a x` the infimum of `f a q` over `q : ℚ` with `x < q`. -/
noncomputable irreducible_def IsRatCDF.stieltjesFunctionAux (f : α → ℚ → ℝ) : α → ℝ → ℝ :=
  fun a x ↦ ⨅ q : { q' : ℚ // x < q' }, f a q

lemma IsRatCDF.stieltjesFunctionAux_def' (f : α → ℚ → ℝ) (a : α) :
    IsRatCDF.stieltjesFunctionAux f a = fun (t : ℝ) ↦ ⨅ r : { r' : ℚ // t < r' }, f a r := by
  ext t; exact IsRatCDF.stieltjesFunctionAux_def f a t

lemma IsRatCDF.stieltjesFunctionAux_eq (a : α) (r : ℚ) :
    IsRatCDF.stieltjesFunctionAux f a r = f a r := by
  rw [← hf.iInf_rat_gt_eq a r, IsRatCDF.stieltjesFunctionAux]
  refine Equiv.iInf_congr ?_ ?_
  · exact
      { toFun := fun t ↦ ⟨t.1, mod_cast t.2⟩
        invFun := fun t ↦ ⟨t.1, mod_cast t.2⟩
        left_inv := fun t ↦ by simp only [Subtype.coe_eta]
        right_inv := fun t ↦ by simp only [Subtype.coe_eta] }
  · intro t
    simp only [Equiv.coe_fn_mk, Subtype.coe_mk]

lemma IsRatCDF.stieltjesFunctionAux_unit_prod (a : α) :
    IsRatCDF.stieltjesFunctionAux (fun (p : Unit × α) ↦ f p.2) ((), a) =
      IsRatCDF.stieltjesFunctionAux f a :=
  by simp_rw [IsRatCDF.stieltjesFunctionAux_def']

lemma IsRatCDF.stieltjesFunctionAux_nonneg (a : α) (r : ℝ) :
    0 ≤ IsRatCDF.stieltjesFunctionAux f a r := by
  have : Nonempty { r' : ℚ // r < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt r
    exact ⟨⟨r, hrx⟩⟩
  rw [IsRatCDF.stieltjesFunctionAux_def]
  exact le_ciInf fun r' ↦ hf.nonneg a _

lemma IsRatCDF.monotone_stieltjesFunctionAux (a : α) :
    Monotone (IsRatCDF.stieltjesFunctionAux f a) := by
  intro x y hxy
  have : Nonempty { r' : ℚ // y < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt y
    exact ⟨⟨r, hrx⟩⟩
  simp_rw [IsRatCDF.stieltjesFunctionAux_def]
  refine le_ciInf fun r ↦ (ciInf_le ?_ ?_).trans_eq ?_
  · refine ⟨0, fun z ↦ ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _
  · exact ⟨r.1, hxy.trans_lt r.prop⟩
  · rfl

lemma IsRatCDF.continuousWithinAt_stieltjesFunctionAux_Ici (a : α) (x : ℝ) :
    ContinuousWithinAt (IsRatCDF.stieltjesFunctionAux f a) (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  convert Monotone.tendsto_nhdsWithin_Ioi (monotone_stieltjesFunctionAux hf a) x
  rw [sInf_image']
  have h' : ⨅ r : Ioi x, stieltjesFunctionAux f a r
      = ⨅ r : { r' : ℚ // x < r' }, stieltjesFunctionAux f a r := by
    refine Real.iInf_Ioi_eq_iInf_rat_gt x ?_ (monotone_stieltjesFunctionAux hf a)
    refine ⟨0, fun z ↦ ?_⟩
    rintro ⟨u, -, rfl⟩
    exact stieltjesFunctionAux_nonneg hf a u
  have h'' :
    ⨅ r : { r' : ℚ // x < r' }, stieltjesFunctionAux f a r =
      ⨅ r : { r' : ℚ // x < r' }, f a r := by
    congr with r
    exact stieltjesFunctionAux_eq hf a r
  rw [h', h'', ContinuousWithinAt]
  congr!
  rw [stieltjesFunctionAux_def]

/-- Extend a function `f : α → ℚ → ℝ` with property `IsRatCDF` from `ℚ` to `ℝ`, to a function
`α → StieltjesFunction`. -/
noncomputable def IsRatCDF.stieltjesFunction (a : α) : StieltjesFunction where
  toFun := stieltjesFunctionAux f a
  mono' := monotone_stieltjesFunctionAux hf a
  right_continuous' x := continuousWithinAt_stieltjesFunctionAux_Ici hf a x

lemma IsRatCDF.stieltjesFunction_eq (a : α) (r : ℚ) : hf.stieltjesFunction a r = f a r :=
  stieltjesFunctionAux_eq hf a r

lemma IsRatCDF.stieltjesFunction_nonneg (a : α) (r : ℝ) : 0 ≤ hf.stieltjesFunction a r :=
  stieltjesFunctionAux_nonneg hf a r

lemma IsRatCDF.stieltjesFunction_le_one (a : α) (x : ℝ) : hf.stieltjesFunction a x ≤ 1 := by
  obtain ⟨r, hrx⟩ := exists_rat_gt x
  rw [← StieltjesFunction.iInf_rat_gt_eq]
  simp_rw [IsRatCDF.stieltjesFunction_eq]
  refine ciInf_le_of_le ?_ ?_ (hf.le_one _ _)
  · refine ⟨0, fun z ↦ ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _
  · exact ⟨r, hrx⟩

lemma IsRatCDF.tendsto_stieltjesFunction_atBot (a : α) :
    Tendsto (hf.stieltjesFunction a) atBot (𝓝 0) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x < q ∧ ↑q < x + 1 := fun x ↦ exists_rat_btwn (lt_add_one x)
  let qs : ℝ → ℚ := fun x ↦ (h_exists x).choose
  have hqs_tendsto : Tendsto qs atBot atBot := by
    rw [tendsto_atBot_atBot]
    refine fun q ↦ ⟨q - 1, fun y hy ↦ ?_⟩
    have h_le : ↑(qs y) ≤ (q : ℝ) - 1 + 1 :=
      (h_exists y).choose_spec.2.le.trans (add_le_add hy le_rfl)
    rw [sub_add_cancel] at h_le
    exact mod_cast h_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((hf.tendsto_atBot_zero a).comp hqs_tendsto) (stieltjesFunction_nonneg hf a) fun x ↦ ?_
  rw [Function.comp_apply, ← stieltjesFunction_eq hf]
  exact (hf.stieltjesFunction a).mono (h_exists x).choose_spec.1.le

lemma IsRatCDF.tendsto_stieltjesFunction_atTop (a : α) :
    Tendsto (hf.stieltjesFunction a) atTop (𝓝 1) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x - 1 < q ∧ ↑q < x := fun x ↦ exists_rat_btwn (sub_one_lt x)
  let qs : ℝ → ℚ := fun x ↦ (h_exists x).choose
  have hqs_tendsto : Tendsto qs atTop atTop := by
    rw [tendsto_atTop_atTop]
    refine fun q ↦ ⟨q + 1, fun y hy ↦ ?_⟩
    have h_le : y - 1 ≤ qs y := (h_exists y).choose_spec.1.le
    rw [sub_le_iff_le_add] at h_le
    exact_mod_cast le_of_add_le_add_right (hy.trans h_le)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ((hf.tendsto_atTop_one a).comp hqs_tendsto)
      tendsto_const_nhds ?_ (stieltjesFunction_le_one hf a)
  intro x
  rw [Function.comp_apply, ← stieltjesFunction_eq hf]
  exact (hf.stieltjesFunction a).mono (le_of_lt (h_exists x).choose_spec.2)

lemma IsRatCDF.measurable_stieltjesFunction (x : ℝ) :
    Measurable fun a ↦ hf.stieltjesFunction a x := by
  have : (fun a ↦ hf.stieltjesFunction a x) = fun a ↦ ⨅ r : { r' : ℚ // x < r' }, f a ↑r := by
    ext1 a
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr with q
    rw [stieltjesFunction_eq]
  rw [this]
  exact measurable_iInf (fun q ↦ hf.measurable.eval)

lemma IsRatCDF.stronglyMeasurable_stieltjesFunction (x : ℝ) :
    StronglyMeasurable fun a ↦ hf.stieltjesFunction a x :=
  (measurable_stieltjesFunction hf x).stronglyMeasurable

section Measure

lemma IsRatCDF.measure_stieltjesFunction_Iic (a : α) (x : ℝ) :
    (hf.stieltjesFunction a).measure (Iic x) = ENNReal.ofReal (hf.stieltjesFunction a x) := by
  rw [← sub_zero (hf.stieltjesFunction a x)]
  exact (hf.stieltjesFunction a).measure_Iic (tendsto_stieltjesFunction_atBot hf a) _

lemma IsRatCDF.measure_stieltjesFunction_univ (a : α) :
    (hf.stieltjesFunction a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  exact StieltjesFunction.measure_univ _ (tendsto_stieltjesFunction_atBot hf a)
    (tendsto_stieltjesFunction_atTop hf a)

instance IsRatCDF.instIsProbabilityMeasure_stieltjesFunction (a : α) :
    IsProbabilityMeasure (hf.stieltjesFunction a).measure :=
  ⟨measure_stieltjesFunction_univ hf a⟩

lemma IsRatCDF.measurable_measure_stieltjesFunction :
    Measurable fun a ↦ (hf.stieltjesFunction a).measure := by
  rw [Measure.measurable_measure]
  refine fun s hs ↦ MeasurableSpace.induction_on_inter
    (C := fun s ↦ Measurable fun b ↦ StieltjesFunction.measure (hf.stieltjesFunction b) s)
    (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic ?_ ?_ ?_ ?_ hs
  · simp only [measure_empty, measurable_const]
  · rintro S ⟨u, rfl⟩
    simp_rw [measure_stieltjesFunction_Iic hf _ u]
    exact (measurable_stieltjesFunction hf u).ennreal_ofReal
  · intro t ht ht_cd_meas
    have : (fun a ↦ (hf.stieltjesFunction a).measure tᶜ) =
        (fun a ↦ (hf.stieltjesFunction a).measure univ)
          - fun a ↦ (hf.stieltjesFunction a).measure t := by
      ext1 a
      rw [measure_compl ht (measure_ne_top (hf.stieltjesFunction a).measure _), Pi.sub_apply]
    simp_rw [this, measure_stieltjesFunction_univ hf]
    exact Measurable.sub measurable_const ht_cd_meas
  · intro f hf_disj hf_meas hf_cd_meas
    simp_rw [measure_iUnion hf_disj hf_meas]
    exact Measurable.ennreal_tsum hf_cd_meas

end Measure

end IsRatCDF.stieltjesFunction

section stieltjesOfMeasurableRat

variable {f : α → ℚ → ℝ}

/-- Turn a measurable function `f : α → ℚ → ℝ` into a measurable function `α → StieltjesFunction`.
Composition of `toRatCDF` and `IsRatCDF.stieltjesFunction`. -/
noncomputable
def stieltjesOfMeasurableRat (f : α → ℚ → ℝ) (hf : Measurable f) : α → StieltjesFunction :=
  (IsRatCDF_toRatCDF hf).stieltjesFunction

lemma stieltjesOfMeasurableRat_eq (hf : Measurable f) (a : α) (r : ℚ) :
    stieltjesOfMeasurableRat f hf a r = toRatCDF f a r := IsRatCDF.stieltjesFunction_eq _ a r

lemma stieltjesOfMeasurableRat_unit_prod (hf : Measurable f) (a : α) :
    stieltjesOfMeasurableRat (fun (p : Unit × α) ↦ f p.2) (hf.comp measurable_snd) ((), a)
      = stieltjesOfMeasurableRat f hf a := by
  simp_rw [stieltjesOfMeasurableRat,IsRatCDF.stieltjesFunction,
    ← IsRatCDF.stieltjesFunctionAux_unit_prod a]
  congr with x
  congr 1 with p : 1
  cases p with
  | mk _ b => rw [← toRatCDF_unit_prod b]

lemma stieltjesOfMeasurableRat_nonneg (hf : Measurable f) (a : α) (r : ℝ) :
    0 ≤ stieltjesOfMeasurableRat f hf a r := IsRatCDF.stieltjesFunction_nonneg _ a r

lemma stieltjesOfMeasurableRat_le_one (hf : Measurable f) (a : α) (x : ℝ) :
    stieltjesOfMeasurableRat f hf a x ≤ 1 := IsRatCDF.stieltjesFunction_le_one _ a x

lemma tendsto_stieltjesOfMeasurableRat_atBot (hf : Measurable f) (a : α) :
    Tendsto (stieltjesOfMeasurableRat f hf a) atBot (𝓝 0) :=
  IsRatCDF.tendsto_stieltjesFunction_atBot _ a

lemma tendsto_stieltjesOfMeasurableRat_atTop (hf : Measurable f) (a : α) :
    Tendsto (stieltjesOfMeasurableRat f hf a) atTop (𝓝 1) :=
  IsRatCDF.tendsto_stieltjesFunction_atTop _ a

lemma measurable_stieltjesOfMeasurableRat (hf : Measurable f) (x : ℝ) :
    Measurable fun a ↦ stieltjesOfMeasurableRat f hf a x :=
  IsRatCDF.measurable_stieltjesFunction _ x

lemma stronglyMeasurable_stieltjesOfMeasurableRat (hf : Measurable f) (x : ℝ) :
    StronglyMeasurable fun a ↦ stieltjesOfMeasurableRat f hf a x :=
  IsRatCDF.stronglyMeasurable_stieltjesFunction _ x

section Measure

lemma measure_stieltjesOfMeasurableRat_Iic (hf : Measurable f) (a : α) (x : ℝ) :
    (stieltjesOfMeasurableRat f hf a).measure (Iic x)
      = ENNReal.ofReal (stieltjesOfMeasurableRat f hf a x) :=
  IsRatCDF.measure_stieltjesFunction_Iic _ _ _

lemma measure_stieltjesOfMeasurableRat_univ (hf : Measurable f) (a : α) :
    (stieltjesOfMeasurableRat f hf a).measure univ = 1 :=
  IsRatCDF.measure_stieltjesFunction_univ _ _

instance instIsProbabilityMeasure_stieltjesOfMeasurableRat
    (hf : Measurable f) (a : α) :
    IsProbabilityMeasure (stieltjesOfMeasurableRat f hf a).measure :=
  IsRatCDF.instIsProbabilityMeasure_stieltjesFunction _ _

lemma measurable_measure_stieltjesOfMeasurableRat (hf : Measurable f) :
    Measurable fun a ↦ (stieltjesOfMeasurableRat f hf a).measure :=
  IsRatCDF.measurable_measure_stieltjesFunction _

end Measure

end stieltjesOfMeasurableRat
