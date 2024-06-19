/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.OuterMeasure.Operations
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Outer measures from functions

Given an arbitrary function `m : Set α → ℝ≥0∞` that sends `∅` to `0` we can define an outer
measure on `α` that on `s` is defined to be the infimum of `∑ᵢ, m (sᵢ)` for all collections of sets
`sᵢ` that cover `s`. This is the unique maximal outer measure that is at most the given function.

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `OuterMeasure.boundedBy` is the greatest outer measure that is at most the given function.
  If you know that the given function sends `∅` to `0`, then `OuterMeasure.ofFunction` is a
  special case.
* `sInf_eq_boundedBy_sInfGen` is a characterization of the infimum of outer measures.

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

outer measure, Carathéodory-measurable, Carathéodory's criterion

-/

#align_import measure_theory.measure.outer_measure from "leanprover-community/mathlib"@"343e80208d29d2d15f8050b929aa50fe4ce71b55"

noncomputable section

open Set Function Filter
open scoped Classical NNReal Topology ENNReal

namespace MeasureTheory
namespace OuterMeasure

section OfFunction

-- Porting note: "set_option eqn_compiler.zeta true" removed

variable {α : Type*} (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0)

/-- Given any function `m` assigning measures to sets satisying `m ∅ = 0`, there is
  a unique maximal outer measure `μ` satisfying `μ s ≤ m s` for all `s : Set α`. -/
protected def ofFunction : OuterMeasure α :=
  let μ s := ⨅ (f : ℕ → Set α) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i)
  { measureOf := μ
    empty :=
      le_antisymm
        ((iInf_le_of_le fun _ => ∅) <| iInf_le_of_le (empty_subset _) <| by simp [m_empty])
        (zero_le _)
    mono := fun {s₁ s₂} hs => iInf_mono fun f => iInf_mono' fun hb => ⟨hs.trans hb, le_rfl⟩
    iUnion_nat := fun s _ =>
      ENNReal.le_of_forall_pos_le_add <| by
        intro ε hε (hb : (∑' i, μ (s i)) < ∞)
        rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 hε).ne' ℕ with ⟨ε', hε', hl⟩
        refine le_trans ?_ (add_le_add_left (le_of_lt hl) _)
        rw [← ENNReal.tsum_add]
        choose f hf using
          show ∀ i, ∃ f : ℕ → Set α, (s i ⊆ ⋃ i, f i) ∧ (∑' i, m (f i)) < μ (s i) + ε' i by
            intro i
            have : μ (s i) < μ (s i) + ε' i :=
              ENNReal.lt_add_right (ne_top_of_le_ne_top hb.ne <| ENNReal.le_tsum _)
                (by simpa using (hε' i).ne')
            rcases iInf_lt_iff.mp this with ⟨t, ht⟩
            exists t
            contrapose! ht
            exact le_iInf ht
        refine le_trans ?_ (ENNReal.tsum_le_tsum fun i => le_of_lt (hf i).2)
        rw [← ENNReal.tsum_prod, ← Nat.pairEquiv.symm.tsum_eq]
        refine iInf_le_of_le _ (iInf_le _ ?_)
        apply iUnion_subset
        intro i
        apply Subset.trans (hf i).1
        apply iUnion_subset
        simp only [Nat.pairEquiv_symm_apply]
        rw [iUnion_unpair]
        intro j
        apply subset_iUnion₂ i }
#align measure_theory.outer_measure.of_function MeasureTheory.OuterMeasure.ofFunction

theorem ofFunction_apply (s : Set α) :
    OuterMeasure.ofFunction m m_empty s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, m (t n) :=
  rfl
#align measure_theory.outer_measure.of_function_apply MeasureTheory.OuterMeasure.ofFunction_apply

variable {m m_empty}

theorem ofFunction_le (s : Set α) : OuterMeasure.ofFunction m m_empty s ≤ m s :=
  let f : ℕ → Set α := fun i => Nat.casesOn i s fun _ => ∅
  iInf_le_of_le f <|
    iInf_le_of_le (subset_iUnion f 0) <|
      le_of_eq <| tsum_eq_single 0 <| by
        rintro (_ | i)
        · simp
        · simp [m_empty]
#align measure_theory.outer_measure.of_function_le MeasureTheory.OuterMeasure.ofFunction_le

theorem ofFunction_eq (s : Set α) (m_mono : ∀ ⦃t : Set α⦄, s ⊆ t → m s ≤ m t)
    (m_subadd : ∀ s : ℕ → Set α, m (⋃ i, s i) ≤ ∑' i, m (s i)) :
    OuterMeasure.ofFunction m m_empty s = m s :=
  le_antisymm (ofFunction_le s) <|
    le_iInf fun f => le_iInf fun hf => le_trans (m_mono hf) (m_subadd f)
#align measure_theory.outer_measure.of_function_eq MeasureTheory.OuterMeasure.ofFunction_eq

theorem le_ofFunction {μ : OuterMeasure α} :
    μ ≤ OuterMeasure.ofFunction m m_empty ↔ ∀ s, μ s ≤ m s :=
  ⟨fun H s => le_trans (H s) (ofFunction_le s), fun H _ =>
    le_iInf fun f =>
      le_iInf fun hs =>
        le_trans (μ.mono hs) <| le_trans (measure_iUnion_le f) <| ENNReal.tsum_le_tsum fun _ => H _⟩
#align measure_theory.outer_measure.le_of_function MeasureTheory.OuterMeasure.le_ofFunction

theorem isGreatest_ofFunction :
    IsGreatest { μ : OuterMeasure α | ∀ s, μ s ≤ m s } (OuterMeasure.ofFunction m m_empty) :=
  ⟨fun _ => ofFunction_le _, fun _ => le_ofFunction.2⟩
#align measure_theory.outer_measure.is_greatest_of_function MeasureTheory.OuterMeasure.isGreatest_ofFunction

theorem ofFunction_eq_sSup : OuterMeasure.ofFunction m m_empty = sSup { μ | ∀ s, μ s ≤ m s } :=
  (@isGreatest_ofFunction α m m_empty).isLUB.sSup_eq.symm
#align measure_theory.outer_measure.of_function_eq_Sup MeasureTheory.OuterMeasure.ofFunction_eq_sSup

/-- If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = MeasureTheory.OuterMeasure.ofFunction m m_empty`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, then this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s`
and `y ∈ t`.  -/
theorem ofFunction_union_of_top_of_nonempty_inter {s t : Set α}
    (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → m u = ∞) :
    OuterMeasure.ofFunction m m_empty (s ∪ t) =
      OuterMeasure.ofFunction m m_empty s + OuterMeasure.ofFunction m m_empty t := by
  refine le_antisymm (measure_union_le _ _) (le_iInf₂ fun f hf ↦ ?_)
  set μ := OuterMeasure.ofFunction m m_empty
  rcases Classical.em (∃ i, (s ∩ f i).Nonempty ∧ (t ∩ f i).Nonempty) with (⟨i, hs, ht⟩ | he)
  · calc
      μ s + μ t ≤ ∞ := le_top
      _ = m (f i) := (h (f i) hs ht).symm
      _ ≤ ∑' i, m (f i) := ENNReal.le_tsum i

  set I := fun s => { i : ℕ | (s ∩ f i).Nonempty }
  have hd : Disjoint (I s) (I t) := disjoint_iff_inf_le.mpr fun i hi => he ⟨i, hi⟩
  have hI : ∀ u ⊆ s ∪ t, μ u ≤ ∑' i : I u, μ (f i) := fun u hu =>
    calc
      μ u ≤ μ (⋃ i : I u, f i) :=
        μ.mono fun x hx =>
          let ⟨i, hi⟩ := mem_iUnion.1 (hf (hu hx))
          mem_iUnion.2 ⟨⟨i, ⟨x, hx, hi⟩⟩, hi⟩
      _ ≤ ∑' i : I u, μ (f i) := measure_iUnion_le _

  calc
    μ s + μ t ≤ (∑' i : I s, μ (f i)) + ∑' i : I t, μ (f i) :=
      add_le_add (hI _ subset_union_left) (hI _ subset_union_right)
    _ = ∑' i : ↑(I s ∪ I t), μ (f i) :=
      (tsum_union_disjoint (f := fun i => μ (f i)) hd ENNReal.summable ENNReal.summable).symm
    _ ≤ ∑' i, μ (f i) :=
      (tsum_le_tsum_of_inj (↑) Subtype.coe_injective (fun _ _ => zero_le _) (fun _ => le_rfl)
        ENNReal.summable ENNReal.summable)
    _ ≤ ∑' i, m (f i) := ENNReal.tsum_le_tsum fun i => ofFunction_le _
#align measure_theory.outer_measure.of_function_union_of_top_of_nonempty_inter MeasureTheory.OuterMeasure.ofFunction_union_of_top_of_nonempty_inter

theorem comap_ofFunction {β} (f : β → α) (h : Monotone m ∨ Surjective f) :
    comap f (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun s => m (f '' s)) (by simp; simp [m_empty]) := by
  refine le_antisymm (le_ofFunction.2 fun s => ?_) fun s => ?_
  · rw [comap_apply]
    apply ofFunction_le
  · rw [comap_apply, ofFunction_apply, ofFunction_apply]
    refine iInf_mono' fun t => ⟨fun k => f ⁻¹' t k, ?_⟩
    refine iInf_mono' fun ht => ?_
    rw [Set.image_subset_iff, preimage_iUnion] at ht
    refine ⟨ht, ENNReal.tsum_le_tsum fun n => ?_⟩
    cases' h with hl hr
    exacts [hl (image_preimage_subset _ _), (congr_arg m (hr.image_preimage (t n))).le]
#align measure_theory.outer_measure.comap_of_function MeasureTheory.OuterMeasure.comap_ofFunction

theorem map_ofFunction_le {β} (f : α → β) :
    map f (OuterMeasure.ofFunction m m_empty) ≤
      OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty :=
  le_ofFunction.2 fun s => by
    rw [map_apply]
    apply ofFunction_le
#align measure_theory.outer_measure.map_of_function_le MeasureTheory.OuterMeasure.map_ofFunction_le

theorem map_ofFunction {β} {f : α → β} (hf : Injective f) :
    map f (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty := by
  refine (map_ofFunction_le _).antisymm fun s => ?_
  simp only [ofFunction_apply, map_apply, le_iInf_iff]
  intro t ht
  refine iInf_le_of_le (fun n => (range f)ᶜ ∪ f '' t n) (iInf_le_of_le ?_ ?_)
  · rw [← union_iUnion, ← inter_subset, ← image_preimage_eq_inter_range, ← image_iUnion]
    exact image_subset _ ht
  · refine ENNReal.tsum_le_tsum fun n => le_of_eq ?_
    simp [hf.preimage_image]
#align measure_theory.outer_measure.map_of_function MeasureTheory.OuterMeasure.map_ofFunction

-- TODO (kmill): change `m (t ∩ s)` to `m (s ∩ t)`
theorem restrict_ofFunction (s : Set α) (hm : Monotone m) :
    restrict s (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun t => m (t ∩ s)) (by simp; simp [m_empty]) := by
      rw [restrict]
      simp only [inter_comm _ s, LinearMap.comp_apply]
      rw [comap_ofFunction _ (Or.inl hm)]
      simp only [map_ofFunction Subtype.coe_injective, Subtype.image_preimage_coe]
#align measure_theory.outer_measure.restrict_of_function MeasureTheory.OuterMeasure.restrict_ofFunction

theorem smul_ofFunction {c : ℝ≥0∞} (hc : c ≠ ∞) : c • OuterMeasure.ofFunction m m_empty =
    OuterMeasure.ofFunction (c • m) (by simp [m_empty]) := by
  ext1 s
  haveI : Nonempty { t : ℕ → Set α // s ⊆ ⋃ i, t i } := ⟨⟨fun _ => s, subset_iUnion (fun _ => s) 0⟩⟩
  simp only [smul_apply, ofFunction_apply, ENNReal.tsum_mul_left, Pi.smul_apply, smul_eq_mul,
  iInf_subtype']
  rw [ENNReal.iInf_mul_left fun h => (hc h).elim]
#align measure_theory.outer_measure.smul_of_function MeasureTheory.OuterMeasure.smul_ofFunction

end OfFunction

section BoundedBy

variable {α : Type*} (m : Set α → ℝ≥0∞)

/-- Given any function `m` assigning measures to sets, there is a unique maximal outer measure `μ`
  satisfying `μ s ≤ m s` for all `s : Set α`. This is the same as `OuterMeasure.ofFunction`,
  except that it doesn't require `m ∅ = 0`. -/
def boundedBy : OuterMeasure α :=
  OuterMeasure.ofFunction (fun s => ⨆ _ : s.Nonempty, m s) (by simp [Set.not_nonempty_empty])
#align measure_theory.outer_measure.bounded_by MeasureTheory.OuterMeasure.boundedBy

variable {m}

theorem boundedBy_le (s : Set α) : boundedBy m s ≤ m s :=
  (ofFunction_le _).trans iSup_const_le
#align measure_theory.outer_measure.bounded_by_le MeasureTheory.OuterMeasure.boundedBy_le

theorem boundedBy_eq_ofFunction (m_empty : m ∅ = 0) (s : Set α) :
    boundedBy m s = OuterMeasure.ofFunction m m_empty s := by
  have : (fun s : Set α => ⨆ _ : s.Nonempty, m s) = m := by
    ext1 t
    rcases t.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty, m_empty]
  simp [boundedBy, this]
#align measure_theory.outer_measure.bounded_by_eq_of_function MeasureTheory.OuterMeasure.boundedBy_eq_ofFunction

theorem boundedBy_apply (s : Set α) :
    boundedBy m s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t),
                      ∑' n, ⨆ _ : (t n).Nonempty, m (t n) := by
  simp [boundedBy, ofFunction_apply]
#align measure_theory.outer_measure.bounded_by_apply MeasureTheory.OuterMeasure.boundedBy_apply

theorem boundedBy_eq (s : Set α) (m_empty : m ∅ = 0) (m_mono : ∀ ⦃t : Set α⦄, s ⊆ t → m s ≤ m t)
    (m_subadd : ∀ s : ℕ → Set α, m (⋃ i, s i) ≤ ∑' i, m (s i)) : boundedBy m s = m s := by
  rw [boundedBy_eq_ofFunction m_empty, ofFunction_eq s m_mono m_subadd]
#align measure_theory.outer_measure.bounded_by_eq MeasureTheory.OuterMeasure.boundedBy_eq

@[simp]
theorem boundedBy_eq_self (m : OuterMeasure α) : boundedBy m = m :=
  ext fun _ => boundedBy_eq _ measure_empty (fun _ ht => measure_mono ht) measure_iUnion_le
#align measure_theory.outer_measure.bounded_by_eq_self MeasureTheory.OuterMeasure.boundedBy_eq_self

theorem le_boundedBy {μ : OuterMeasure α} : μ ≤ boundedBy m ↔ ∀ s, μ s ≤ m s := by
  rw [boundedBy , le_ofFunction, forall_congr']; intro s
  rcases s.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty]
#align measure_theory.outer_measure.le_bounded_by MeasureTheory.OuterMeasure.le_boundedBy

theorem le_boundedBy' {μ : OuterMeasure α} :
    μ ≤ boundedBy m ↔ ∀ s : Set α, s.Nonempty → μ s ≤ m s := by
  rw [le_boundedBy, forall_congr']
  intro s
  rcases s.eq_empty_or_nonempty with h | h <;> simp [h]
#align measure_theory.outer_measure.le_bounded_by' MeasureTheory.OuterMeasure.le_boundedBy'

@[simp]
theorem boundedBy_top : boundedBy (⊤ : Set α → ℝ≥0∞) = ⊤ := by
  rw [eq_top_iff, le_boundedBy']
  intro s hs
  rw [top_apply hs]
  exact le_rfl
#align measure_theory.outer_measure.bounded_by_top MeasureTheory.OuterMeasure.boundedBy_top

@[simp]
theorem boundedBy_zero : boundedBy (0 : Set α → ℝ≥0∞) = 0 := by
  rw [← coe_bot, eq_bot_iff]
  apply boundedBy_le
#align measure_theory.outer_measure.bounded_by_zero MeasureTheory.OuterMeasure.boundedBy_zero

theorem smul_boundedBy {c : ℝ≥0∞} (hc : c ≠ ∞) : c • boundedBy m = boundedBy (c • m) := by
  simp only [boundedBy , smul_ofFunction hc]
  congr 1 with s : 1
  rcases s.eq_empty_or_nonempty with (rfl | hs) <;> simp [*]
#align measure_theory.outer_measure.smul_bounded_by MeasureTheory.OuterMeasure.smul_boundedBy

theorem comap_boundedBy {β} (f : β → α)
    (h : (Monotone fun s : { s : Set α // s.Nonempty } => m s) ∨ Surjective f) :
    comap f (boundedBy m) = boundedBy fun s => m (f '' s) := by
  refine (comap_ofFunction _ ?_).trans ?_
  · refine h.imp (fun H s t hst => iSup_le fun hs => ?_) id
    have ht : t.Nonempty := hs.mono hst
    exact (@H ⟨s, hs⟩ ⟨t, ht⟩ hst).trans (le_iSup (fun _ : t.Nonempty => m t) ht)
  · dsimp only [boundedBy]
    congr with s : 1
    rw [image_nonempty]
#align measure_theory.outer_measure.comap_bounded_by MeasureTheory.OuterMeasure.comap_boundedBy

/-- If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = MeasureTheory.OuterMeasure.boundedBy m`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, then this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s`
and `y ∈ t`.  -/
theorem boundedBy_union_of_top_of_nonempty_inter {s t : Set α}
    (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → m u = ∞) :
    boundedBy m (s ∪ t) = boundedBy m s + boundedBy m t :=
  ofFunction_union_of_top_of_nonempty_inter fun u hs ht =>
    top_unique <| (h u hs ht).ge.trans <| le_iSup (fun _ => m u) (hs.mono inter_subset_right)
#align measure_theory.outer_measure.bounded_by_union_of_top_of_nonempty_inter MeasureTheory.OuterMeasure.boundedBy_union_of_top_of_nonempty_inter

end BoundedBy

section sInfGen

variable {α : Type*}

/-- Given a set of outer measures, we define a new function that on a set `s` is defined to be the
  infimum of `μ(s)` for the outer measures `μ` in the collection. We ensure that this
  function is defined to be `0` on `∅`, even if the collection of outer measures is empty.
  The outer measure generated by this function is the infimum of the given outer measures. -/
def sInfGen (m : Set (OuterMeasure α)) (s : Set α) : ℝ≥0∞ :=
  ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ s
#align measure_theory.outer_measure.Inf_gen MeasureTheory.OuterMeasure.sInfGen

theorem sInfGen_def (m : Set (OuterMeasure α)) (t : Set α) :
    sInfGen m t = ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ t :=
  rfl
#align measure_theory.outer_measure.Inf_gen_def MeasureTheory.OuterMeasure.sInfGen_def

theorem sInf_eq_boundedBy_sInfGen (m : Set (OuterMeasure α)) :
    sInf m = OuterMeasure.boundedBy (sInfGen m) := by
  refine le_antisymm ?_ ?_
  · refine le_boundedBy.2 fun s => le_iInf₂ fun μ hμ => ?_
    apply sInf_le hμ
  · refine le_sInf ?_
    intro μ hμ t
    exact le_trans (boundedBy_le t) (iInf₂_le μ hμ)
#align measure_theory.outer_measure.Inf_eq_bounded_by_Inf_gen MeasureTheory.OuterMeasure.sInf_eq_boundedBy_sInfGen

theorem iSup_sInfGen_nonempty {m : Set (OuterMeasure α)} (h : m.Nonempty) (t : Set α) :
    ⨆ _ : t.Nonempty, sInfGen m t = ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ t := by
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp [biInf_const h]
  · simp [ht, sInfGen_def]
#align measure_theory.outer_measure.supr_Inf_gen_nonempty MeasureTheory.OuterMeasure.iSup_sInfGen_nonempty

/-- The value of the Infimum of a nonempty set of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem sInf_apply {m : Set (OuterMeasure α)} {s : Set α} (h : m.Nonempty) :
    sInf m s =
      ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ (t n) := by
  simp_rw [sInf_eq_boundedBy_sInfGen, boundedBy_apply, iSup_sInfGen_nonempty h]
#align measure_theory.outer_measure.Inf_apply MeasureTheory.OuterMeasure.sInf_apply

/-- The value of the Infimum of a set of outer measures on a nonempty set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem sInf_apply' {m : Set (OuterMeasure α)} {s : Set α} (h : s.Nonempty) :
    sInf m s =
      ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ (t n) :=
  m.eq_empty_or_nonempty.elim (fun hm => by simp [hm, h]) sInf_apply
#align measure_theory.outer_measure.Inf_apply' MeasureTheory.OuterMeasure.sInf_apply'

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem iInf_apply {ι} [Nonempty ι] (m : ι → OuterMeasure α) (s : Set α) :
    (⨅ i, m i) s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ i, m i (t n) := by
  rw [iInf, sInf_apply (range_nonempty m)]
  simp only [iInf_range]
#align measure_theory.outer_measure.infi_apply MeasureTheory.OuterMeasure.iInf_apply

/-- The value of the Infimum of a family of outer measures on a nonempty set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem iInf_apply' {ι} (m : ι → OuterMeasure α) {s : Set α} (hs : s.Nonempty) :
    (⨅ i, m i) s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ i, m i (t n) := by
  rw [iInf, sInf_apply' hs]
  simp only [iInf_range]
#align measure_theory.outer_measure.infi_apply' MeasureTheory.OuterMeasure.iInf_apply'

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem biInf_apply {ι} {I : Set ι} (hI : I.Nonempty) (m : ι → OuterMeasure α) (s : Set α) :
    (⨅ i ∈ I, m i) s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ i ∈ I, m i (t n) := by
  haveI := hI.to_subtype
  simp only [← iInf_subtype'', iInf_apply]
#align measure_theory.outer_measure.binfi_apply MeasureTheory.OuterMeasure.biInf_apply

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem biInf_apply' {ι} (I : Set ι) (m : ι → OuterMeasure α) {s : Set α} (hs : s.Nonempty) :
    (⨅ i ∈ I, m i) s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ i ∈ I, m i (t n) := by
  simp only [← iInf_subtype'', iInf_apply' _ hs]
#align measure_theory.outer_measure.binfi_apply' MeasureTheory.OuterMeasure.biInf_apply'

theorem map_iInf_le {ι β} (f : α → β) (m : ι → OuterMeasure α) :
    map f (⨅ i, m i) ≤ ⨅ i, map f (m i) :=
  (map_mono f).map_iInf_le
#align measure_theory.outer_measure.map_infi_le MeasureTheory.OuterMeasure.map_iInf_le

theorem comap_iInf {ι β} (f : α → β) (m : ι → OuterMeasure β) :
    comap f (⨅ i, m i) = ⨅ i, comap f (m i) := by
  refine ext_nonempty fun s hs => ?_
  refine ((comap_mono f).map_iInf_le s).antisymm ?_
  simp only [comap_apply, iInf_apply' _ hs, iInf_apply' _ (hs.image _), le_iInf_iff,
    Set.image_subset_iff, preimage_iUnion]
  refine fun t ht => iInf_le_of_le _ (iInf_le_of_le ht <| ENNReal.tsum_le_tsum fun k => ?_)
  exact iInf_mono fun i => (m i).mono (image_preimage_subset _ _)
#align measure_theory.outer_measure.comap_infi MeasureTheory.OuterMeasure.comap_iInf

theorem map_iInf {ι β} {f : α → β} (hf : Injective f) (m : ι → OuterMeasure α) :
    map f (⨅ i, m i) = restrict (range f) (⨅ i, map f (m i)) := by
  refine Eq.trans ?_ (map_comap _ _)
  simp only [comap_iInf, comap_map hf]
#align measure_theory.outer_measure.map_infi MeasureTheory.OuterMeasure.map_iInf

theorem map_iInf_comap {ι β} [Nonempty ι] {f : α → β} (m : ι → OuterMeasure β) :
    map f (⨅ i, comap f (m i)) = ⨅ i, map f (comap f (m i)) := by
  refine (map_iInf_le _ _).antisymm fun s => ?_
  simp only [map_apply, comap_apply, iInf_apply, le_iInf_iff]
  refine fun t ht => iInf_le_of_le (fun n => f '' t n ∪ (range f)ᶜ) (iInf_le_of_le ?_ ?_)
  · rw [← iUnion_union, Set.union_comm, ← inter_subset, ← image_iUnion, ←
      image_preimage_eq_inter_range]
    exact image_subset _ ht
  · refine ENNReal.tsum_le_tsum fun n => iInf_mono fun i => (m i).mono ?_
    simp only [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
      image_subset_iff]
    exact subset_refl _
#align measure_theory.outer_measure.map_infi_comap MeasureTheory.OuterMeasure.map_iInf_comap

theorem map_biInf_comap {ι β} {I : Set ι} (hI : I.Nonempty) {f : α → β} (m : ι → OuterMeasure β) :
    map f (⨅ i ∈ I, comap f (m i)) = ⨅ i ∈ I, map f (comap f (m i)) := by
  haveI := hI.to_subtype
  rw [← iInf_subtype'', ← iInf_subtype'']
  exact map_iInf_comap _
#align measure_theory.outer_measure.map_binfi_comap MeasureTheory.OuterMeasure.map_biInf_comap

theorem restrict_iInf_restrict {ι} (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨅ i, restrict s (m i)) = restrict s (⨅ i, m i) :=
  calc restrict s (⨅ i, restrict s (m i))
    _ = restrict (range ((↑) : s → α)) (⨅ i, restrict s (m i)) := by rw [Subtype.range_coe]
    _ = map ((↑) : s → α) (⨅ i, comap (↑) (m i)) := (map_iInf Subtype.coe_injective _).symm
    _ = restrict s (⨅ i, m i) := congr_arg (map ((↑) : s → α)) (comap_iInf _ _).symm

#align measure_theory.outer_measure.restrict_infi_restrict MeasureTheory.OuterMeasure.restrict_iInf_restrict

theorem restrict_iInf {ι} [Nonempty ι] (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨅ i, m i) = ⨅ i, restrict s (m i) :=
  (congr_arg (map ((↑) : s → α)) (comap_iInf _ _)).trans (map_iInf_comap _)
#align measure_theory.outer_measure.restrict_infi MeasureTheory.OuterMeasure.restrict_iInf

theorem restrict_biInf {ι} {I : Set ι} (hI : I.Nonempty) (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨅ i ∈ I, m i) = ⨅ i ∈ I, restrict s (m i) := by
  haveI := hI.to_subtype
  rw [← iInf_subtype'', ← iInf_subtype'']
  exact restrict_iInf _ _
#align measure_theory.outer_measure.restrict_binfi MeasureTheory.OuterMeasure.restrict_biInf

/-- This proves that Inf and restrict commute for outer measures, so long as the set of
outer measures is nonempty. -/
theorem restrict_sInf_eq_sInf_restrict (m : Set (OuterMeasure α)) {s : Set α} (hm : m.Nonempty) :
    restrict s (sInf m) = sInf (restrict s '' m) := by
  simp only [sInf_eq_iInf, restrict_biInf, hm, iInf_image]
#align measure_theory.outer_measure.restrict_Inf_eq_Inf_restrict MeasureTheory.OuterMeasure.restrict_sInf_eq_sInf_restrict

end sInfGen

end OuterMeasure
