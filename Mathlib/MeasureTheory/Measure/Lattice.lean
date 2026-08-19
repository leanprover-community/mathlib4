/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Module

/-!
# Lattice operations on measures

Measures on `α` form a complete lattice.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/

@[expose] public section

noncomputable section

open Set

open Filter hiding map

open Function MeasurableSpace Topology Filter ENNReal NNReal Interval MeasureTheory
open scoped symmDiff

variable {α β γ ι R R' : Type*}

namespace MeasureTheory

section

variable {m0 : MeasurableSpace α} {mβ : MeasurableSpace β} [MeasurableSpace γ]
variable {μ μ₁ μ₂ ν ν' : Measure α} {s t : Set α}

namespace Measure

/-- Measures are partially ordered. -/
instance instPartialOrder {_ : MeasurableSpace α} : PartialOrder (Measure α) where
  le m₁ m₂ := ∀ s, m₁ s ≤ m₂ s
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ s := le_trans (h₁ s) (h₂ s)
  le_antisymm _ _ h₁ h₂ := ext fun s _ => le_antisymm (h₁ s) (h₂ s)

theorem toOuterMeasure_le : μ₁.toOuterMeasure ≤ μ₂.toOuterMeasure ↔ μ₁ ≤ μ₂ := .rfl

theorem le_iff : μ₁ ≤ μ₂ ↔ ∀ s, MeasurableSet s → μ₁ s ≤ μ₂ s := outerMeasure_le_iff

theorem le_intro (h : ∀ s, MeasurableSet s → s.Nonempty → μ₁ s ≤ μ₂ s) : μ₁ ≤ μ₂ :=
  le_iff.2 fun s hs ↦ s.eq_empty_or_nonempty.elim (by rintro rfl; simp) (h s hs)

theorem le_iff' : μ₁ ≤ μ₂ ↔ ∀ s, μ₁ s ≤ μ₂ s := .rfl

@[gcongr] theorem measure_mono_left (h : μ ≤ ν) (s : Set α) : μ s ≤ ν s := h s

@[gcongr]
theorem measure_mono_both (h₁ : μ ≤ ν) (h₂ : s ⊆ t) : μ s ≤ ν t :=
  (h₁ s).trans (measure_mono h₂)

theorem lt_iff : μ < ν ↔ μ ≤ ν ∧ ∃ s, MeasurableSet s ∧ μ s < ν s :=
  lt_iff_le_not_ge.trans <|
    and_congr Iff.rfl <| by simp only [le_iff, not_forall, not_le, exists_prop]

theorem lt_iff' : μ < ν ↔ μ ≤ ν ∧ ∃ s, μ s < ν s :=
  lt_iff_le_not_ge.trans <| and_congr Iff.rfl <| by simp only [le_iff', not_forall, not_le]

instance instIsOrderedAddMonoid {_ : MeasurableSpace α} : IsOrderedAddMonoid (Measure α) where
  add_le_add_left _ _ h _ s := add_le_add_left (h s) _

protected theorem le_add_left (h : μ ≤ ν) : μ ≤ ν' + ν := fun s => le_add_left (h s)

protected theorem le_add_right (h : μ ≤ ν) : μ ≤ ν + ν' := fun s => le_add_right (h s)

instance [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [CovariantClass R ℝ≥0∞ (· • ·) (· ≤ ·)] :
    CovariantClass R (Measure α) (· • ·) (· ≤ ·) where
  elim c μ ν hμν s := by
    simp only [smul_apply]
    gcongr

instance [SMul R ℝ≥0∞] [LE R] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [IsOrderedSMul R ℝ≥0∞] :
    IsOrderedSMul R (Measure α) where
  smul_le_smul_left μ ν hμν a s := by gcongr
  smul_le_smul_right a b hab μ s := by
    simp only [smul_apply]
    gcongr

section sInf

variable {m : Set (Measure α)}

theorem sInf_caratheodory (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet[(sInf (toOuterMeasure '' m)).caratheodory] s := by
  rw [OuterMeasure.sInf_eq_boundedBy_sInfGen]
  refine OuterMeasure.boundedBy_caratheodory fun t => ?_
  simp only [OuterMeasure.sInfGen, le_iInf_iff, forall_mem_image, measure_eq_iInf t,
    coe_toOuterMeasure]
  intro μ hμ u htu _hu
  have hm : ∀ {s t}, s ⊆ t → OuterMeasure.sInfGen (toOuterMeasure '' m) s ≤ μ t := by
    intro s t hst
    rw [OuterMeasure.sInfGen_def, iInf_image]
    exact iInf₂_le_of_le μ hμ <| measure_mono hst
  rw [← measure_inter_add_sdiff u hs]
  exact add_le_add (hm <| inter_subset_inter_left _ htu) (hm <| sdiff_subset_sdiff_left htu)

instance {_ : MeasurableSpace α} : InfSet (Measure α) :=
  ⟨fun m => (sInf (toOuterMeasure '' m)).toMeasure <| sInf_caratheodory⟩

theorem sInf_apply (hs : MeasurableSet s) : sInf m s = sInf (toOuterMeasure '' m) s :=
  toMeasure_apply _ _ hs

private theorem measure_sInf_le (h : μ ∈ m) : sInf m ≤ μ :=
  have : sInf (toOuterMeasure '' m) ≤ μ.toOuterMeasure := sInf_le (mem_image_of_mem _ h)
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s

private theorem measure_le_sInf (h : ∀ μ' ∈ m, μ ≤ μ') : μ ≤ sInf m :=
  have : μ.toOuterMeasure ≤ sInf (toOuterMeasure '' m) :=
    le_sInf <| forall_mem_image.2 fun _ hμ ↦ toOuterMeasure_le.2 <| h _ hμ
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s

instance instCompleteSemilatticeInf {_ : MeasurableSpace α} :
    CompleteSemilatticeInf (Measure α) where
  isGLB_sInf _ := private ⟨fun _ ↦ measure_sInf_le, fun _ ↦ measure_le_sInf⟩

instance instCompleteLattice {_ : MeasurableSpace α} : CompleteLattice (Measure α) :=
  { completeLatticeOfCompleteSemilatticeInf (Measure α) with
    top :=
      { toOuterMeasure := ⊤,
        m_iUnion := by
          intro f _ _
          refine (measure_iUnion_le _).antisymm ?_
          if hne : (⋃ i, f i).Nonempty then
            rw [OuterMeasure.top_apply hne]
            exact le_top
          else
            simp_all [Set.not_nonempty_iff_eq_empty]
        trim_le := le_top },
    le_top := fun _ => toOuterMeasure_le.mp le_top
    bot := 0
    bot_le := fun _a _s => bot_le }

end sInf

lemma inf_apply {s : Set α} (hs : MeasurableSet s) :
    (μ ⊓ ν) s = sInf {m | ∃ t, m = μ (t ∩ s) + ν (tᶜ ∩ s)} := by
  -- `(μ ⊓ ν) s` is defined as `⊓ (t : ℕ → Set α) (ht : s ⊆ ⋃ n, t n), ∑' n, μ (t n) ⊓ ν (t n)`
  rw [← sInf_pair, Measure.sInf_apply hs, OuterMeasure.sInf_apply
    (image_nonempty.2 <| insert_nonempty μ {ν})]
  refine le_antisymm (le_sInf fun m ⟨t, ht₁⟩ ↦ ?_) (le_iInf₂ fun t' ht' ↦ ?_)
  · subst ht₁
    -- We first show `(μ ⊓ ν) s ≤ μ (t ∩ s) + ν (tᶜ ∩ s)` for any `t : Set α`
    -- For this, define the sequence `t' : ℕ → Set α` where `t' 0 = t ∩ s`, `t' 1 = tᶜ ∩ s` and
    -- `∅` otherwise. Then, we have by construction
    -- `(μ ⊓ ν) s ≤ ∑' n, μ (t' n) ⊓ ν (t' n) ≤ μ (t' 0) + ν (t' 1) = μ (t ∩ s) + ν (tᶜ ∩ s)`.
    set t' : ℕ → Set α := fun n ↦ if n = 0 then t ∩ s else if n = 1 then tᶜ ∩ s else ∅ with ht'
    refine (iInf₂_le t' fun x hx ↦ ?_).trans ?_
    · by_cases hxt : x ∈ t
      · refine mem_iUnion.2 ⟨0, ?_⟩
        simp [hx, hxt]
      · refine mem_iUnion.2 ⟨1, ?_⟩
        simp [hx, hxt]
    · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
      rw [tsum_eq_add_tsum_ite 0, tsum_eq_add_tsum_ite 1, ite_eq_right zero_ne_one.symm,
        ENNReal.summable.tsum_eq_zero_iff.2 _, add_zero]
      · exact add_le_add (inf_le_left.trans <| by simp [ht']) (inf_le_right.trans <| by simp [ht'])
      · simp only [ite_eq_left_iff]
        intro n hn₁ hn₀
        simp only [ht', ite_eq_right hn₀, ite_eq_right hn₁, measure_empty, le_refl, inf_of_le_left]
  · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
    -- Conversely, fixing `t' : ℕ → Set α` such that `s ⊆ ⋃ n, t' n`, we construct `t : Set α`
    -- for which `μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n, μ (t' n) ⊓ ν (t' n)`.
    -- Denoting `I := {n | μ (t' n) ≤ ν (t' n)}`, we set `t = ⋃ n ∈ I, t' n`.
    -- Clearly `μ (t ∩ s) ≤ ∑' n ∈ I, μ (t' n)` and `ν (tᶜ ∩ s) ≤ ∑' n ∉ I, ν (t' n)`, so
    -- `μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n ∈ I, μ (t' n) + ∑' n ∉ I, ν (t' n)`
    -- where the RHS equals `∑' n, μ (t' n) ⊓ ν (t' n)` by the choice of `I`.
    set t := ⋃ n ∈ {k : ℕ | μ (t' k) ≤ ν (t' k)}, t' n with ht
    suffices hadd : μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n, μ (t' n) ⊓ ν (t' n) by
      exact le_trans (sInf_le ⟨t, rfl⟩) hadd
    have hle₁ : μ (t ∩ s) ≤ ∑' (n : {k | μ (t' k) ≤ ν (t' k)}), μ (t' n) :=
      (measure_mono inter_subset_left).trans <| measure_biUnion_le _ (to_countable _) _
    have hcap : tᶜ ∩ s ⊆ ⋃ n ∈ {k | ν (t' k) < μ (t' k)}, t' n := by
      simp_rw [ht, compl_iUnion]
      refine fun x ⟨hx₁, hx₂⟩ ↦ mem_iUnion₂.2 ?_
      obtain ⟨i, hi⟩ := mem_iUnion.1 <| ht' hx₂
      refine ⟨i, ?_, hi⟩
      by_contra h
      simp only [mem_ofPred_eq, not_lt] at h
      exact mem_iInter₂.1 hx₁ i h hi
    have hle₂ : ν (tᶜ ∩ s) ≤ ∑' (n : {k | ν (t' k) < μ (t' k)}), ν (t' n) :=
      (measure_mono hcap).trans (measure_biUnion_le ν (to_countable {k | ν (t' k) < μ (t' k)}) _)
    refine (add_le_add hle₁ hle₂).trans ?_
    have heq : {k | μ (t' k) ≤ ν (t' k)} ∪ {k | ν (t' k) < μ (t' k)} = univ := by
      ext k; simp [le_or_gt]
    conv in ∑' (n : ℕ), μ (t' n) ⊓ ν (t' n) => rw [← tsum_univ, ← heq]
    rw [ENNReal.summable.tsum_union_disjoint (f := fun n ↦ μ (t' n) ⊓ ν (t' n)) ?_ ENNReal.summable]
    · refine add_le_add (tsum_congr ?_).le (tsum_congr ?_).le
      · rw [Subtype.forall]
        intro n hn; simpa
      · rw [Subtype.forall]
        intro n hn
        rw [mem_ofPred_eq] at hn
        simp [le_of_lt hn]
    · rw [Set.disjoint_iff]
      rintro k ⟨hk₁, hk₂⟩
      rw [mem_ofPred_eq] at hk₁ hk₂
      exact False.elim <| hk₂.not_ge hk₁

@[simp]
theorem _root_.MeasureTheory.OuterMeasure.toMeasure_top :
    (⊤ : OuterMeasure α).toMeasure (by rw [OuterMeasure.top_caratheodory]; exact le_top) =
      (⊤ : Measure α) :=
  toOuterMeasure_toMeasure (μ := ⊤)

@[simp]
theorem toOuterMeasure_top {_ : MeasurableSpace α} :
    (⊤ : Measure α).toOuterMeasure = (⊤ : OuterMeasure α) :=
  rfl

@[simp]
theorem top_add : ⊤ + μ = ⊤ :=
  top_unique <| Measure.le_add_right le_rfl

@[simp]
theorem add_top : μ + ⊤ = ⊤ :=
  top_unique <| Measure.le_add_left le_rfl

protected theorem zero_le {_m0 : MeasurableSpace α} (μ : Measure α) : 0 ≤ μ :=
  bot_le

theorem nonpos_iff_eq_zero' : μ ≤ 0 ↔ μ = 0 :=
  μ.zero_le.ge_iff_eq'

@[simp]
theorem measure_univ_eq_zero : μ univ = 0 ↔ μ = 0 :=
  ⟨fun h => bot_unique fun s => (h ▸ measure_mono (subset_univ s) : μ s ≤ 0), fun h =>
    h.symm ▸ rfl⟩

theorem measure_univ_ne_zero : μ univ ≠ 0 ↔ μ ≠ 0 :=
  measure_univ_eq_zero.not

instance [NeZero μ] : NeZero (μ univ) := ⟨measure_univ_ne_zero.2 <| NeZero.ne μ⟩

@[simp]
theorem measure_univ_pos : 0 < μ univ ↔ μ ≠ 0 :=
  pos_iff_ne_zero.trans measure_univ_ne_zero

lemma nonempty_of_neZero (μ : Measure α) [NeZero μ] : Nonempty α :=
  (isEmpty_or_nonempty α).resolve_left fun h ↦ by
    simpa [eq_empty_of_isEmpty] using NeZero.ne (μ univ)

section Sum

variable {f : ι → Measure α}

theorem le_sum (μ : ι → Measure α) (i : ι) : μ i ≤ sum μ :=
  le_iff.2 fun s hs ↦ by simpa only [sum_apply μ hs] using ENNReal.le_tsum i

@[simp]
theorem ae_sum_eq [Countable ι] (μ : ι → Measure α) : ae (sum μ) = ⨆ i, ae (μ i) :=
  Filter.ext fun _ => ae_sum_iff.trans mem_iSup.symm

@[simp]
theorem sum_of_isEmpty [IsEmpty ι] (μ : ι → Measure α) : sum μ = 0 := by
  rw [← measure_univ_eq_zero, sum_apply _ MeasurableSet.univ, tsum_empty]

end Sum

end Measure

open Measure

open MeasureTheory

@[simp]
theorem ae_eq_bot : ae μ = ⊥ ↔ μ = 0 := by
  rw [← empty_mem_iff_bot, mem_ae_iff, compl_empty, measure_univ_eq_zero]

@[simp]
theorem ae_neBot : (ae μ).NeBot ↔ μ ≠ 0 :=
  neBot_iff.trans (not_congr ae_eq_bot)

instance Measure.ae.neBot [NeZero μ] : (ae μ).NeBot := ae_neBot.2 <| NeZero.ne μ

@[simp]
theorem ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measure α) = ⊥ :=
  ae_eq_bot.2 rfl

@[gcongr, mono]
theorem ae_mono (h : μ ≤ ν) : ae μ ≤ ae ν :=
  fun s hs ↦ bot_unique <| (h sᶜ).trans_eq hs

protected theorem AEDisjoint.of_le (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν ≤ μ) :
    AEDisjoint ν s t :=
  bot_unique <| (h' (s ∩ t)).trans_eq h

theorem NullMeasurableSet.mono (h : NullMeasurableSet s μ) (h' : ν ≤ μ) :
    NullMeasurableSet s ν := by
  obtain ⟨t, ht, hst⟩ := h
  exact ⟨t, ht, hst.filter_mono (ae_mono h')⟩

theorem _root_.AEMeasurable.mono_measure {f : α → β} (h : AEMeasurable f μ) (h' : ν ≤ μ) :
    AEMeasurable f ν := by
  obtain ⟨g, hg, hfg⟩ := h
  exact ⟨g, hg, hfg.filter_mono (ae_mono h')⟩

end

end MeasureTheory

end
