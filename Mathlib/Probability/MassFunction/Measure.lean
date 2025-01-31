import Mathlib.Probability.MassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Dirac

section OuterMeasure

open MeasureTheory MeasureTheory.OuterMeasure

variable {α : Type*}

open BigOperators ENNReal

namespace SPMF

/-

section OuterMeasure

noncomputable def toOuterMeasure (d : SPMF α) : OuterMeasure α :=
  OuterMeasure.sum fun x : α => d x • dirac x

variable (d : SPMF α) (s t : Set α)

theorem toOuterMeasure_apply : d.toOuterMeasure s = d.massOf s :=
  tsum_congr fun x => smul_dirac_apply (d x) x s

@[simp]
theorem coe_toOuterMeasure_eq_massOf : d.toOuterMeasure = d.massOf := by
  ext
  simp_rw [toOuterMeasure_apply]

@[simp]
theorem toOuterMeasure_caratheodory : d.toOuterMeasure.caratheodory = ⊤ := by
  simp_rw [MeasurableSpace.ext_iff, MeasurableSpace.measurableSet_top, iff_true]
  refine' fun u v => _
  simp_rw [coe_toOuterMeasure_eq_massOf]
  exact d.massOf_caratheodory u v

@[simp]
theorem toOuterMeasure_apply_finset (s : Finset α) : d.toOuterMeasure s = ∑ x in s, d x := by
  simp_rw [coe_toOuterMeasure_eq_massOf, massOf_finset]


theorem toOuterMeasure_apply_singleton (a : α) : d.toOuterMeasure {a} = d a := by
  simp_rw [coe_toOuterMeasure_eq_massOf, massOf_singleton]

theorem toOuterMeasure_injective : (toOuterMeasure : SPMF α → OuterMeasure α).Injective :=
    fun p q h => by
  apply (massOf_injective)
  simp_rw [← coe_toOuterMeasure_eq_massOf, h]

@[simp]
theorem toOuterMeasure_inj {p q : SPMF α} : p.toOuterMeasure = q.toOuterMeasure ↔ p = q :=
  toOuterMeasure_injective.eq_iff

theorem toOuterMeasure_apply_eq_zero_iff : d.toOuterMeasure s = 0 ↔ Disjoint d.support s := by
  rw [coe_toOuterMeasure_eq_massOf, massOf_eq_zero_iff_support_disjoint]

theorem toOuterMeasure_apply_eq_mass_iff : d.toOuterMeasure s = d.mass ↔ d.support ⊆ s := by
  rw [coe_toOuterMeasure_eq_massOf, apply_massOf_eq_mass_iff]

@[simp]
theorem toOuterMeasure_apply_inter_support :
    d.toOuterMeasure (s ∩ d.support) = d.toOuterMeasure s := by
  rw [coe_toOuterMeasure_eq_massOf, massOf_apply_inter_support]

/-- Slightly stronger than `OuterMeasure.mono` having an intersection with `p.support`. -/
theorem toOuterMeasure_mono {s t : Set α} (h : s ∩ d.support ⊆ t) :
    d.toOuterMeasure s ≤ d.toOuterMeasure t := by
  simp_rw [coe_toOuterMeasure_eq_massOf]
  exact d.massOf_mono' h

theorem toOuterMeasure_apply_eq_of_inter_support_eq {s t : Set α}
    (h : s ∩ d.support = t ∩ d.support) : d.toOuterMeasure s = d.toOuterMeasure t := by
  simp_rw [coe_toOuterMeasure_eq_massOf]
  exact d.massOf_apply_eq_of_inter_support_eq h

@[simp]
theorem toOuterMeasure_apply_fintype [Fintype α] : d.toOuterMeasure s = ∑ x, s.indicator d x := by
  rw [coe_toOuterMeasure_eq_massOf, massOf_fintype]

end OuterMeasure



section Measure

variable (s : Set α)

@[simp]
theorem toOuterMeasure_pure_apply : (pure a).toOuterMeasure s = if a ∈ s then 1 else 0 := by
  refine' (toOuterMeasure_apply (pure a) s).trans _
  split_ifs with ha
  · refine' (tsum_congr fun b => _).trans (tsum_ite_eq a 1)
    exact ite_eq_left_iff.2 fun hb => symm (ite_eq_right_iff.2 fun h => (hb <| h.symm ▸ ha).elim)
  · refine' (tsum_congr fun b => _).trans tsum_zero
    exact ite_eq_right_iff.2 fun hb => ite_eq_right_iff.2 fun h => (ha <| h ▸ hb).elim
#align SPMF.to_outer_measure_pure_apply SPMF.toOuterMeasure_pure_apply

variable [MeasurableSpace α]

/-- The measure of a set under `pure a` is `1` for sets containing `a` and `0` otherwise. -/
@[simp]
theorem toMeasure_pure_apply (hs : MeasurableSet s) :
    (pure a).toMeasure s = if a ∈ s then 1 else 0 :=
  (toMeasure_apply_eq_toOuterMeasure_apply (pure a) s hs).trans (toOuterMeasure_pure_apply a s)
#align SPMF.to_measure_pure_apply SPMF.toMeasure_pure_apply

theorem toMeasure_pure : (pure a).toMeasure = Measure.dirac a :=
  Measure.ext fun s hs => by rw [toMeasure_pure_apply a s hs, Measure.dirac_apply' a hs]; rfl
#align SPMF.to_measure_pure SPMF.toMeasure_pure

@[simp]
theorem toSPMF_dirac [Countable α] [h : MeasurableSingletonClass α] :
    (Measure.dirac a).toSPMF = pure a := by
  rw [toSPMF_eq_iff_toMeasure_eq, toMeasure_pure]
#align SPMF.to_SPMF_dirac SPMF.toSPMF_dirac

end Measure

-/



/-

section Measure

variable (s : Set β)

@[simp]
theorem toOuterMeasure_bind_apply :
    (p.bind f).toOuterMeasure s = ∑' a, p a * (f a).toOuterMeasure s :=
  calc
    (p.bind f).toOuterMeasure s = ∑' b, if b ∈ s then ∑' a, p a * f a b else 0 := by
      simp [toOuterMeasure_apply, Set.indicator_apply]
    _ = ∑' (b) (a), p a * if b ∈ s then f a b else 0 := tsum_congr fun b => by split_ifs <;> simp
    _ = ∑' (a) (b), p a * if b ∈ s then f a b else 0 :=
      (tsum_comm' ENNReal.summable (fun _ => ENNReal.summable) fun _ => ENNReal.summable)
    _ = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 := tsum_congr fun a => ENNReal.tsum_mul_left
    _ = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 :=
      (tsum_congr fun a => (congr_arg fun x => p a * x) <| tsum_congr fun b => by split_ifs <;> rfl)
    _ = ∑' a, p a * (f a).toOuterMeasure s :=
      tsum_congr fun a => by simp only [toOuterMeasure_apply, Set.indicator_apply]
#align SPMF.to_outer_measure_bind_apply SPMF.toOuterMeasure_bind_apply

/-- The measure of a set under `p.bind f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a`. -/
@[simp]
theorem toMeasure_bind_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bind f).toMeasure s = ∑' a, p a * (f a).toMeasure s :=
  (toMeasure_apply_eq_toOuterMeasure_apply (p.bind f) s hs).trans
    ((toOuterMeasure_bind_apply p f s).trans
      (tsum_congr fun a =>
        congr_arg (fun x => p a * x) (toMeasure_apply_eq_toOuterMeasure_apply (f a) s hs).symm))
#align SPMF.to_measure_bind_apply SPMF.toMeasure_bind_apply

end Measure
-/

/-

section Measure

variable (s : Set β)

@[simp]
theorem toOuterMeasure_bindOnSupport_apply :
    (p.bindOnSupport f).toOuterMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toOuterMeasure s := by
  simp only [toOuterMeasure_apply, Set.indicator_apply, bindOnSupport_apply]
  calc
    (∑' b, ite (b ∈ s) (∑' a, p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0) =
        ∑' (b) (a), ite (b ∈ s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      tsum_congr fun b => by split_ifs with hbs <;> simp only [eq_self_iff_true, tsum_zero]
    _ = ∑' (a) (b), ite (b ∈ s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, ite (b ∈ s) (dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      (tsum_congr fun a => by simp only [← ENNReal.tsum_mul_left, mul_ite, mul_zero])
    _ = ∑' a, p a * dite (p a = 0) (fun h => 0) fun h => ∑' b, ite (b ∈ s) (f a h b) 0 :=
      tsum_congr fun a => by split_ifs with ha <;> simp only [ite_self, tsum_zero, eq_self_iff_true]
#align SPMF.to_outer_measure_bind_on_support_apply SPMF.toOuterMeasure_bindOnSupport_apply

/-- The measure of a set under `p.bindOnSupport f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a _`.
  The additional if statement is needed since `f` is only a partial function. -/
@[simp]
theorem toMeasure_bindOnSupport_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bindOnSupport f).toMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toMeasure s := by
  simp only [toMeasure_apply_eq_toOuterMeasure_apply _ _ hs, toOuterMeasure_bindOnSupport_apply]
#align SPMF.to_measure_bind_on_support_apply SPMF.toMeasure_bindOnSupport_apply

end Measure
-/

/-
section Measure

variable (s : Set β)

@[simp]
theorem toOuterMeasure_map_apply : (d.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s) := by
  simp [map, Set.indicator, toOuterMeasure_apply p (f ⁻¹' s)]
#align SPMF.to_outer_measure_map_apply SPMF.toOuterMeasure_map_apply

@[simp]
theorem toMeasure_map_apply [MeasurableSpace α] [MeasurableSpace β] (hf : Measurable f)
    (hs : MeasurableSet s) : (d.map f).toMeasure s = p.toMeasure (f ⁻¹' s) := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ s hs,
    toMeasure_apply_eq_toOuterMeasure_apply _ (f ⁻¹' s) (measurableSet_preimage hf hs)]
  exact toOuterMeasure_map_apply f p s
#align SPMF.to_measure_map_apply SPMF.toMeasure_map_apply

end Measure
-/

/-


section Measure

variable (t : Set α)

@[simp]
theorem toOuterMeasure_ofFinset_apply :
    (ofFinset f s h h').toOuterMeasure t = ∑' x, t.indicator f x :=
  toOuterMeasure_apply (ofFinset f s h h') t
#align SPMF.to_outer_measure_of_finset_apply SPMF.toOuterMeasure_ofFinset_apply

@[simp]
theorem toMeasure_ofFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofFinset f s h h').toMeasure t = ∑' x, t.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ t ht).trans (toOuterMeasure_ofFinset_apply h h' t)
#align SPMF.to_measure_of_finset_apply SPMF.toMeasure_ofFinset_apply

end Measure
-/

/-
section Measure

variable (s : Set α)

@[simp high]
theorem toOuterMeasure_ofFintype_apply : (ofFintype f h).toOuterMeasure s = ∑' x, s.indicator f x :=
  toOuterMeasure_apply (ofFintype f h) s
#align SPMF.to_outer_measure_of_fintype_apply SPMF.toOuterMeasure_ofFintype_apply

@[simp]
theorem toMeasure_ofFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (ofFintype f h).toMeasure s = ∑' x, s.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ s hs).trans (toOuterMeasure_ofFintype_apply h s)
#align SPMF.to_measure_of_fintype_apply SPMF.toMeasure_ofFintype_apply

end Measure
-/

end SPMF
