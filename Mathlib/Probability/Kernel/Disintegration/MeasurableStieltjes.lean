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
import Mathlib.Probability.Kernel.Disintegration.AuxLemmas

/-!
# Cumulative distributions functions of Markov kernels

-/


open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace ProbabilityTheory

variable {α β ι : Type*} [MeasurableSpace α]

section IsCDFLike

variable {f : α → ℚ → ℝ}

structure IsRatStieltjesPoint (f : α → ℚ → ℝ) (a : α) : Prop where
  mono : Monotone (f a)
  nonneg : ∀ q, 0 ≤ f a q
  le_one : ∀ q, f a q ≤ 1
  tendsto_atTop_one : Tendsto (f a) atTop (𝓝 1)
  tendsto_atBot_zero : Tendsto (f a) atBot (𝓝 0)
  iInf_rat_gt_eq : ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t

lemma isRatStieltjesPoint_unit_prod_iff (f : α → ℚ → ℝ) (a : α) :
    IsRatStieltjesPoint (fun p : Unit × α ↦ f p.2) ((), a)
      ↔ IsRatStieltjesPoint f a := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨h.mono, h.nonneg, h.le_one, h.tendsto_atTop_one, h.tendsto_atBot_zero,
      h.iInf_rat_gt_eq⟩
  · exact ⟨h.mono, h.nonneg, h.le_one, h.tendsto_atTop_one, h.tendsto_atBot_zero,
      h.iInf_rat_gt_eq⟩

lemma measurableSet_isRatStieltjesPoint (hf : ∀ q, Measurable (fun a ↦ f a q)) :
    MeasurableSet {a | IsRatStieltjesPoint f a} := by
  have h1 : MeasurableSet {a | Monotone (f a)} := by
    change MeasurableSet {a | ∀ q r (_ : q ≤ r), f a q ≤ f a r}
    simp_rw [Set.setOf_forall]
    refine MeasurableSet.iInter (fun q ↦ ?_)
    refine MeasurableSet.iInter (fun r ↦ ?_)
    refine MeasurableSet.iInter (fun _ ↦ ?_)
    exact measurableSet_le (hf q) (hf r)
  have h2 : MeasurableSet {a | ∀ q, 0 ≤ f a q} := by
    simp_rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun q ↦ measurableSet_le measurable_const (hf q))
  have h3 : MeasurableSet {a | ∀ q, f a q ≤ 1} := by
    simp_rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun q ↦ measurableSet_le (hf q) measurable_const)
  have h4 : MeasurableSet {a | Tendsto (f a) atTop (𝓝 1)} :=
    measurableSet_tendsto_nhds (fun q ↦ hf q) 1
  have h5 : MeasurableSet {a | Tendsto (f a) atBot (𝓝 0)} :=
    measurableSet_tendsto_nhds (fun q ↦ hf q) 0
  have h6 : MeasurableSet {a | ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter (fun q ↦ ?_)
    exact measurableSet_eq_fun (measurable_iInf fun _ ↦ hf _) (hf _)
  suffices {a | IsRatStieltjesPoint f a}
      = ({a | Monotone (f a)} ∩ {a | ∀ (q : ℚ), 0 ≤ f a q} ∩ {a | ∀ (q : ℚ), f a q ≤ 1}
        ∩ {a | Tendsto (f a) atTop (𝓝 1)} ∩ {a | Tendsto (f a) atBot (𝓝 0)} ∩
        {a | ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t}) by
    rw [this]
    exact ((((h1.inter h2).inter h3).inter h4).inter h5).inter h6
  ext a
  simp only [mem_setOf_eq, mem_inter_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨⟨⟨⟨⟨h.mono, h.nonneg⟩, h.le_one⟩, h.tendsto_atTop_one⟩, h.tendsto_atBot_zero⟩,
      h.iInf_rat_gt_eq⟩
  · exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

structure IsCDFLike (f : α → ℚ → ℝ) : Prop where
  mono : ∀ a, Monotone (f a)
  nonneg : ∀ a q, 0 ≤ f a q
  le_one : ∀ a q, f a q ≤ 1
  tendsto_atTop_one : ∀ a, Tendsto (f a) atTop (𝓝 1)
  tendsto_atBot_zero : ∀ a, Tendsto (f a) atBot (𝓝 0)
  iInf_rat_gt_eq : ∀ a, ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t
  measurable : ∀ q, Measurable (fun a ↦ f a q)

end IsCDFLike

section DefaultRatCDF

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

lemma inf_gt_rat_defaultRatCDF (t : ℚ) :
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

lemma measurable_defaultRatCDF (α : Type*) [MeasurableSpace α] (q : ℚ) :
    Measurable (fun (_ : α) ↦ defaultRatCDF q) := measurable_const

lemma isCDFLike_defaultRatCDF (α : Type*) [MeasurableSpace α] :
    IsCDFLike (fun (_ : α) (q : ℚ) ↦ defaultRatCDF q) where
  mono _ := monotone_defaultRatCDF
  nonneg _ := defaultRatCDF_nonneg
  le_one _ := defaultRatCDF_le_one
  tendsto_atBot_zero _ := tendsto_defaultRatCDF_atBot
  tendsto_atTop_one _ := tendsto_defaultRatCDF_atTop
  iInf_rat_gt_eq _ := inf_gt_rat_defaultRatCDF
  measurable := measurable_defaultRatCDF α

end DefaultRatCDF

section ToCDFLike

variable {f : α → ℚ → ℝ}

open Classical in
noncomputable
def toCDFLike (f : α → ℚ → ℝ) : α → ℚ → ℝ := fun a q ↦
  if IsRatStieltjesPoint f a then f a q else defaultRatCDF q

lemma toCDFLike_of_isRatStieltjesPoint {a : α} (h : IsRatStieltjesPoint f a) (q : ℚ) :
    toCDFLike f a q = f a q := by
  unfold toCDFLike; simp [h]

lemma isCDFLike_toCDFLike (hf : ∀ q, Measurable fun a ↦ f a q) :
    IsCDFLike (toCDFLike f) where
  mono a := by unfold toCDFLike; split_ifs with h; exacts [h.mono, monotone_defaultRatCDF]
  nonneg a := by unfold toCDFLike; split_ifs with h; exacts [h.nonneg, defaultRatCDF_nonneg]
  le_one a := by unfold toCDFLike; split_ifs with h; exacts [h.le_one, defaultRatCDF_le_one]
  tendsto_atTop_one a := by
    unfold toCDFLike; split_ifs with h; exacts [h.tendsto_atTop_one, tendsto_defaultRatCDF_atTop]
  tendsto_atBot_zero a := by
    unfold toCDFLike; split_ifs with h; exacts [h.tendsto_atBot_zero, tendsto_defaultRatCDF_atBot]
  iInf_rat_gt_eq a := by
    unfold toCDFLike; split_ifs with h; exacts [h.iInf_rat_gt_eq, inf_gt_rat_defaultRatCDF]
  measurable q :=
    Measurable.ite (measurableSet_isRatStieltjesPoint hf) (hf q) (measurable_defaultRatCDF α q)

lemma toCDFLike_unit_prod (a : α) :
    toCDFLike (fun (p : Unit × α) ↦ f p.2) ((), a) = toCDFLike f a := by
  unfold toCDFLike
  rw [isRatStieltjesPoint_unit_prod_iff]

end ToCDFLike

section IsCDFLike.stieltjesFunction

variable {f : α → ℚ → ℝ} (hf : IsCDFLike f)

noncomputable irreducible_def IsCDFLike.stieltjesFunctionAux (f : α → ℚ → ℝ) : α → ℝ → ℝ :=
  fun a t ↦ ⨅ r : { r' : ℚ // t < r' }, f a r

lemma IsCDFLike.stieltjesFunctionAux_def' (f : α → ℚ → ℝ) (a : α) :
    IsCDFLike.stieltjesFunctionAux f a = fun (t : ℝ) ↦ ⨅ r : { r' : ℚ // t < r' }, f a r := by
  ext t; exact IsCDFLike.stieltjesFunctionAux_def f a t

lemma IsCDFLike.stieltjesFunctionAux_eq (a : α) (r : ℚ) :
    IsCDFLike.stieltjesFunctionAux f a r = f a r := by
  rw [← hf.iInf_rat_gt_eq a r, IsCDFLike.stieltjesFunctionAux]
  refine Equiv.iInf_congr ?_ ?_
  · exact
      { toFun := fun t ↦ ⟨t.1, mod_cast t.2⟩
        invFun := fun t ↦ ⟨t.1, mod_cast t.2⟩
        left_inv := fun t ↦ by simp only [Subtype.coe_eta]
        right_inv := fun t ↦ by simp only [Subtype.coe_eta] }
  · intro t
    simp only [Equiv.coe_fn_mk, Subtype.coe_mk]

lemma IsCDFLike.stieltjesFunctionAux_unit_prod (a : α) :
    IsCDFLike.stieltjesFunctionAux (fun (p : Unit × α) ↦ f p.2) ((), a) =
  IsCDFLike.stieltjesFunctionAux f a := by simp_rw [IsCDFLike.stieltjesFunctionAux_def']

lemma IsCDFLike.stieltjesFunctionAux_nonneg (a : α) (r : ℝ) :
    0 ≤ IsCDFLike.stieltjesFunctionAux f a r := by
  have : Nonempty { r' : ℚ // r < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt r
    exact ⟨⟨r, hrx⟩⟩
  rw [IsCDFLike.stieltjesFunctionAux_def]
  exact le_ciInf fun r' ↦ hf.nonneg a _

lemma bddBelow_range_gt (a : α) (x : ℝ) :
    BddBelow (range fun r : { r' : ℚ // x < ↑r' } ↦ f a r) := by
  refine ⟨0, fun z ↦ ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _

lemma IsCDFLike.monotone_stieltjesFunctionAux (a : α) :
    Monotone (IsCDFLike.stieltjesFunctionAux f a) := by
  intro x y hxy
  have : Nonempty { r' : ℚ // y < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt y
    exact ⟨⟨r, hrx⟩⟩
  simp_rw [IsCDFLike.stieltjesFunctionAux_def]
  refine le_ciInf fun r ↦ (ciInf_le ?_ ?_).trans_eq ?_
  · exact bddBelow_range_gt hf a x
  · exact ⟨r.1, hxy.trans_lt r.prop⟩
  · rfl

lemma  IsCDFLike.continuousWithinAt_stieltjesFunctionAux_Ici (a : α) (x : ℝ) :
    ContinuousWithinAt (IsCDFLike.stieltjesFunctionAux f a) (Ici x) x := by
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

noncomputable def IsCDFLike.stieltjesFunction (a : α) : StieltjesFunction where
  toFun := stieltjesFunctionAux f a
  mono' := monotone_stieltjesFunctionAux hf a
  right_continuous' x := continuousWithinAt_stieltjesFunctionAux_Ici hf a x

lemma IsCDFLike.stieltjesFunction_eq (a : α) (r : ℚ) : hf.stieltjesFunction a r = f a r :=
  stieltjesFunctionAux_eq hf a r

lemma IsCDFLike.stieltjesFunction_nonneg (a : α) (r : ℝ) : 0 ≤ hf.stieltjesFunction a r :=
  stieltjesFunctionAux_nonneg hf a r

lemma IsCDFLike.stieltjesFunction_le_one (a : α) (x : ℝ) : hf.stieltjesFunction a x ≤ 1 := by
  obtain ⟨r, hrx⟩ := exists_rat_gt x
  rw [← StieltjesFunction.iInf_rat_gt_eq]
  simp_rw [IsCDFLike.stieltjesFunction_eq]
  refine ciInf_le_of_le (bddBelow_range_gt hf a x) ?_ (hf.le_one _ _)
  exact ⟨r, hrx⟩

lemma IsCDFLike.tendsto_stieltjesFunction_atBot (a : α) :
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

lemma IsCDFLike.tendsto_stieltjesFunction_atTop (a : α) :
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

lemma IsCDFLike.measurable_stieltjesFunction (x : ℝ) :
    Measurable fun a ↦ hf.stieltjesFunction a x := by
  have : (fun a ↦ hf.stieltjesFunction a x) = fun a ↦ ⨅ r : { r' : ℚ // x < r' }, f a ↑r := by
    ext1 a
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr with q
    rw [stieltjesFunction_eq]
  rw [this]
  exact measurable_iInf (fun q ↦ hf.measurable q)

lemma IsCDFLike.stronglyMeasurable_stieltjesFunction (x : ℝ) :
    StronglyMeasurable fun a ↦ hf.stieltjesFunction a x :=
  (measurable_stieltjesFunction hf x).stronglyMeasurable

section Measure

lemma IsCDFLike.measure_stieltjesFunction_Iic (a : α) (x : ℝ) :
    (hf.stieltjesFunction a).measure (Iic x) = ENNReal.ofReal (hf.stieltjesFunction a x) := by
  rw [← sub_zero (hf.stieltjesFunction a x)]
  exact (hf.stieltjesFunction a).measure_Iic (tendsto_stieltjesFunction_atBot hf a) _

lemma IsCDFLike.measure_stieltjesFunction_univ (a : α) :
    (hf.stieltjesFunction a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  exact StieltjesFunction.measure_univ _ (tendsto_stieltjesFunction_atBot hf a)
    (tendsto_stieltjesFunction_atTop hf a)

instance IsCDFLike.instIsProbabilityMeasure_stieltjesFunction (a : α) :
    IsProbabilityMeasure (hf.stieltjesFunction a).measure :=
  ⟨measure_stieltjesFunction_univ hf a⟩

lemma IsCDFLike.measurable_measure_stieltjesFunction :
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

end IsCDFLike.stieltjesFunction

section stieltjesOfMeasurableRat

variable {f : α → ℚ → ℝ}

noncomputable
def stieltjesOfMeasurableRat (f : α → ℚ → ℝ) (hf : ∀ q, Measurable fun a ↦ f a q) :
    α → StieltjesFunction :=
  (isCDFLike_toCDFLike hf).stieltjesFunction

lemma stieltjesOfMeasurableRat_eq (hf : ∀ q, Measurable fun a ↦ f a q) (a : α) (r : ℚ) :
    stieltjesOfMeasurableRat f hf a r = toCDFLike f a r := IsCDFLike.stieltjesFunction_eq _ a r

lemma stieltjesOfMeasurableRat_unit_prod (hf : ∀ q, Measurable fun a ↦ f a q) (a : α) :
    stieltjesOfMeasurableRat (fun (p : Unit × α) ↦ f p.2)
        (fun q ↦ (hf q).comp measurable_snd) ((), a)
      = stieltjesOfMeasurableRat f hf a := by
  simp_rw [stieltjesOfMeasurableRat,IsCDFLike.stieltjesFunction,
    ← IsCDFLike.stieltjesFunctionAux_unit_prod a]
  congr with x
  congr 1 with p : 1
  cases p with
  | mk _ b => rw [← toCDFLike_unit_prod b]

lemma stieltjesOfMeasurableRat_nonneg (hf : ∀ q, Measurable fun a ↦ f a q) (a : α) (r : ℝ) :
    0 ≤ stieltjesOfMeasurableRat f hf a r := IsCDFLike.stieltjesFunction_nonneg _ a r

lemma stieltjesOfMeasurableRat_le_one (hf : ∀ q, Measurable fun a ↦ f a q) (a : α) (x : ℝ) :
    stieltjesOfMeasurableRat f hf a x ≤ 1 := IsCDFLike.stieltjesFunction_le_one _ a x

lemma tendsto_stieltjesOfMeasurableRat_atBot (hf : ∀ q, Measurable fun a ↦ f a q) (a : α) :
    Tendsto (stieltjesOfMeasurableRat f hf a) atBot (𝓝 0) :=
  IsCDFLike.tendsto_stieltjesFunction_atBot _ a

lemma tendsto_stieltjesOfMeasurableRat_atTop (hf : ∀ q, Measurable fun a ↦ f a q) (a : α) :
    Tendsto (stieltjesOfMeasurableRat f hf a) atTop (𝓝 1) :=
  IsCDFLike.tendsto_stieltjesFunction_atTop _ a

lemma measurable_stieltjesOfMeasurableRat (hf : ∀ q, Measurable fun a ↦ f a q) (x : ℝ) :
    Measurable fun a ↦ stieltjesOfMeasurableRat f hf a x :=
  IsCDFLike.measurable_stieltjesFunction _ x

lemma stronglyMeasurable_stieltjesOfMeasurableRat (hf : ∀ q, Measurable fun a ↦ f a q) (x : ℝ) :
    StronglyMeasurable fun a ↦ stieltjesOfMeasurableRat f hf a x :=
  IsCDFLike.stronglyMeasurable_stieltjesFunction _ x

section Measure

lemma measure_stieltjesOfMeasurableRat_Iic (hf : ∀ q, Measurable fun a ↦ f a q) (a : α) (x : ℝ) :
    (stieltjesOfMeasurableRat f hf a).measure (Iic x)
      = ENNReal.ofReal (stieltjesOfMeasurableRat f hf a x) :=
  IsCDFLike.measure_stieltjesFunction_Iic _ _ _

lemma measure_stieltjesOfMeasurableRat_univ (hf : ∀ q, Measurable fun a ↦ f a q) (a : α) :
    (stieltjesOfMeasurableRat f hf a).measure univ = 1 :=
  IsCDFLike.measure_stieltjesFunction_univ _ _

instance instIsProbabilityMeasure_stieltjesOfMeasurableRat
    (hf : ∀ q, Measurable fun a ↦ f a q) (a : α) :
    IsProbabilityMeasure (stieltjesOfMeasurableRat f hf a).measure :=
  IsCDFLike.instIsProbabilityMeasure_stieltjesFunction _ _

lemma measurable_measure_stieltjesOfMeasurableRat (hf : ∀ q, Measurable fun a ↦ f a q) :
    Measurable fun a ↦ (stieltjesOfMeasurableRat f hf a).measure :=
  IsCDFLike.measurable_measure_stieltjesFunction _

end Measure

end stieltjesOfMeasurableRat
