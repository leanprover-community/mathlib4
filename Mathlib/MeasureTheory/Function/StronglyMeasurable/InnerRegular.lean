/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.DiscreteFamily

import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Function.LusinContinuous
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.CardinalInter
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Topology.MetricSpace.Perfect

/-!
# Strong measurability for inner regular measures

This file proves that measurable maps into pseudometrizable Borel spaces have an almost everywhere
separable range under the uncountable disjoint-union property. This is the topological reduction in
the proof that almost everywhere measurability and almost everywhere strong measurability agree for
finite inner regular measures.
-/

@[expose] public section

open scoped Cardinal ENNReal Topology

open Filter Function Set TopologicalSpace

namespace MeasureTheory

universe u

variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [TopologicalSpace Y]
  [PseudoMetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y] {f : X → Y}

private noncomputable def Measure.inducedIndexMeasure {i : Type*} [MeasurableSpace i]
    (A : i → Set X) (hA : Pairwise (Disjoint on A))
    (hAmeas : ∀ s : Set i, MeasurableSet (⋃ j ∈ s, A j)) : Measure i := by
  refine Measure.ofMeasurable (fun s _ ↦ μ (⋃ j ∈ s, A j)) (by simp) ?_
  intro s _ hs
  rw [show (⋃ j ∈ ⋃ n, s n, A j) = ⋃ n, ⋃ j ∈ s n, A j by
    ext x
    simp only [mem_iUnion]
    aesop]
  apply measure_iUnion
  · intro m n hmn
    change Disjoint (⋃ j ∈ s m, A j) (⋃ j ∈ s n, A j)
    rw [Set.disjoint_left]
    rintro x hx hy
    simp only [mem_iUnion] at hx hy
    obtain ⟨j, hjm, hxj⟩ := hx
    obtain ⟨k, hkn, hxk⟩ := hy
    have hjk : j ≠ k := by
      rintro rfl
      exact Set.disjoint_left.1 (hs hmn) hjm hkn
    exact Set.disjoint_left.1 (hA hjk) hxj hxk
  · exact fun n ↦ hAmeas (s n)

@[simp]
private theorem Measure.inducedIndexMeasure_apply {i : Type*} [MeasurableSpace i]
    (hall : ∀ s : Set i, MeasurableSet s) (A : i → Set X) (hA : Pairwise (Disjoint on A))
    (hAmeas : ∀ s : Set i, MeasurableSet (⋃ j ∈ s, A j)) (s : Set i) :
    μ.inducedIndexMeasure A hA hAmeas s = μ (⋃ j ∈ s, A j) := by
  rw [Measure.inducedIndexMeasure, Measure.ofMeasurable_apply _ (hall s)]

private theorem Measure.exists_pos_measure_le_of_splits_aux {i : Type*} [MeasurableSpace i]
    (nu : Measure i) [IsFiniteMeasure nu] (hall : ∀ s : Set i, MeasurableSet s)
    (hsplit : ∀ s : Set i, 0 < nu s → ∃ t ⊆ s, 0 < nu t ∧ 0 < nu (s \ t))
    {s : Set i} (hs : 0 < nu s) {ε : ENNReal} (hε : 0 < ε) :
    ∃ t ⊆ s, 0 < nu t ∧ nu t ≤ ε := by
  classical
  choose next hnext hnext_pos hnext_diff_pos using
    fun t : {t : Set i // 0 < nu t} ↦ hsplit t t.2
  let next' : {t : Set i // 0 < nu t} → {t : Set i // 0 < nu t} :=
    fun t ↦ ⟨next t, hnext_pos t⟩
  let r : ℕ → {t : Set i // 0 < nu t} := fun n ↦ next'^[n] ⟨s, hs⟩
  have r_succ (n : ℕ) : r (n + 1) = next' (r n) := by
    simp only [r, Function.iterate_succ_apply']
  have hr : Antitone fun n ↦ (r n : Set i) := antitone_nat_of_succ_le fun n ↦ by
    rw [r_succ]
    exact hnext (r n)
  let p : ℕ → Set i := fun n ↦ (r n : Set i) \ r (n + 1)
  have hp_pos (n : ℕ) : 0 < nu (p n) := by
    change 0 < nu ((r n : Set i) \ r (n + 1))
    rw [r_succ]
    exact hnext_diff_pos (r n)
  have hp_disj_of_lt {m n : ℕ} (hmn : m < n) : Disjoint (p m) (p n) := by
    rw [Set.disjoint_left]
    rintro x hxm hxn
    exact hxm.2 (hr (Nat.succ_le_iff.2 hmn) hxn.1)
  have hp_disj : Pairwise (Disjoint on p) := fun m n hmn ↦
    (lt_or_gt_of_ne hmn).elim hp_disj_of_lt fun h ↦ disjoint_comm.2 (hp_disj_of_lt h)
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hε.ne' (measure_ne_top nu s)
  have hNpos : 0 < N := by
    by_contra! h
    have hNzero : N = 0 := Nat.eq_zero_of_le_zero h
    rw [hNzero] at hN
    simp at hN
  by_contra! h
  have hp_sub (n : ℕ) : p n ⊆ s := fun x hx ↦ by
    simpa only [r, Function.iterate_zero_apply] using hr (Nat.zero_le n) hx.1
  have hsum_lt : (N : ENNReal) * ε < ∑ n ∈ Finset.range N, nu (p n) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      ENNReal.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 hNpos⟩
        (fun n _ ↦ h (p n) (hp_sub n) (hp_pos n))
  have hsum_le : ∑ n ∈ Finset.range N, nu (p n) ≤ nu s := by
    rw [← measure_biUnion_finset (hp_disj.set_pairwise _) (fun n _ ↦ hall (p n))]
    exact measure_mono fun x hx ↦ by
      simp only [mem_iUnion] at hx
      obtain ⟨n, -, hxn⟩ := hx
      exact hp_sub n hxn
  exact not_le_of_gt (hN.trans hsum_lt) hsum_le

private theorem Measure.splits_or_exists_atom_aux {i : Type*} [MeasurableSpace i] (nu : Measure i) :
    (∀ s : Set i, 0 < nu s → ∃ t ⊆ s, 0 < nu t ∧ 0 < nu (s \ t)) ∨
      ∃ s : Set i, 0 < nu s ∧ ∀ t ⊆ s, nu t = 0 ∨ nu (s \ t) = 0 := by
  classical
  by_cases h : ∀ s : Set i, 0 < nu s → ∃ t ⊆ s, 0 < nu t ∧ 0 < nu (s \ t)
  · exact Or.inl h
  · push Not at h
    obtain ⟨s, hs, h⟩ := h
    refine Or.inr ⟨s, hs, fun t hts ↦ ?_⟩
    by_cases ht : nu t = 0
    · exact Or.inl ht
    · exact Or.inr (nonpos_iff_eq_zero.1 (h t hts (pos_iff_ne_zero.2 ht)))

private theorem exists_pairwiseDisjoint_iUnion_eq_aux {R α : Type*} (B : R → Set α) :
    ∃ M : R → Set α, Pairwise (Disjoint on M) ∧ (∀ r, M r ⊆ B r) ∧
      (⋃ r, M r) = ⋃ r, B r := by
  classical
  obtain ⟨order, wf, -⟩ := Cardinal.exists_ord_eq_type_lt R
  letI : LinearOrder R := order
  letI : WellFoundedLT R := wf
  let M : R → Set α := fun r ↦ B r \ ⋃ q : Iio r, B q.1
  have hMdisj : Pairwise (Disjoint on M) := by
    intro r t hrt
    rcases lt_or_gt_of_ne hrt with hrt | htr
    · change Disjoint (M r) (M t)
      rw [Set.disjoint_left]
      exact fun x hxr hxt ↦ hxt.2 (mem_iUnion.2 ⟨⟨r, hrt⟩, hxr.1⟩)
    · change Disjoint (M r) (M t)
      rw [disjoint_comm, Set.disjoint_left]
      exact fun x hxt hxr ↦ hxr.2 (mem_iUnion.2 ⟨⟨t, htr⟩, hxt.1⟩)
  refine ⟨M, hMdisj, fun _ ↦ sdiff_subset,
    Subset.antisymm (iUnion_mono fun _ ↦ sdiff_subset) ?_⟩
  intro x hx
  obtain ⟨r, hxr⟩ := mem_iUnion.1 hx
  let r₀ : R := wellFounded_lt.min {r : R | x ∈ B r} ⟨r, hxr⟩
  have hr₀ : x ∈ B r₀ := wellFounded_lt.min_mem {r : R | x ∈ B r} ⟨r, hxr⟩
  apply mem_iUnion.2
  refine ⟨r₀, hr₀, ?_⟩
  rintro hxprior
  obtain ⟨q, hxq⟩ := mem_iUnion.1 hxprior
  exact wellFounded_lt.not_lt_min {r : R | x ∈ B r} hxq q.2

private theorem Measure.exists_minimal_disjoint_null_cover_aux {i : Type u}
    [MeasurableSpace i] (nu : Measure i) (hpoint : ∀ x, nu {x} = 0)
    {s : Set i} (hs : 0 < nu s) :
    ∃ (R : Type u) (M : R → Set i), Pairwise (Disjoint on M) ∧
      (∀ r, M r ⊆ s) ∧ (∀ r, nu (M r) = 0) ∧ 0 < nu (⋃ r, M r) ∧
      ℵ₀ < Cardinal.mk R ∧ ∀ {J : Type u} (C : J → Set i),
        (∀ j, C j ⊆ s) → (∀ j, nu (C j) = 0) →
        Cardinal.mk J < Cardinal.mk R → nu (⋃ j, C j) = 0 := by
  classical
  let admissible : Set Cardinal.{u} := {c | ∃ (R : Type u) (B : R → Set i),
    Cardinal.mk R = c ∧ (∀ r, B r ⊆ s) ∧ (∀ r, nu (B r) = 0) ∧ 0 < nu (⋃ r, B r)}
  have hadmissible : admissible.Nonempty := by
    refine ⟨Cardinal.mk s, s, fun x ↦ {(x : i)}, rfl, fun x ↦ ?_, fun x ↦ hpoint x, ?_⟩
    · exact singleton_subset_iff.2 x.2
    · simpa using hs
  let κ := sInf admissible
  have hκ_mem : κ ∈ admissible := csInf_mem hadmissible
  obtain ⟨R, B, hR, hBs, hBnull, hBpos⟩ := hκ_mem
  have hsmall {J : Type u} (C : J → Set i) (hCs : ∀ j, C j ⊆ s)
      (hCnull : ∀ j, nu (C j) = 0) (hJ : Cardinal.mk J < Cardinal.mk R) :
      nu (⋃ j, C j) = 0 := by
    by_contra hC
    have hJ_mem : Cardinal.mk J ∈ admissible :=
      ⟨J, C, rfl, hCs, hCnull, pos_iff_ne_zero.2 hC⟩
    exact (not_le_of_gt hJ) (hR.le.trans (csInf_le' hJ_mem))
  obtain ⟨M, hMdisj, hMB, hM_union⟩ := exists_pairwiseDisjoint_iUnion_eq_aux B
  have hMsub (r : R) : M r ⊆ s := (hMB r).trans (hBs r)
  have hMnull (r : R) : nu (M r) = 0 := measure_mono_null (hMB r) (hBnull r)
  have hMpos : 0 < nu (⋃ r, M r) := hM_union.symm ▸ hBpos
  have hRuncount : ℵ₀ < Cardinal.mk R := by
    rw [← not_le, Cardinal.mk_le_aleph0_iff]
    intro hcount
    letI : Countable R := hcount
    exact hMpos.ne' (measure_iUnion_null hMnull)
  exact ⟨R, M, hMdisj, hMsub, hMnull, hMpos, hRuncount, hsmall⟩

private theorem Measure.iUnion_Ici_pos_of_minimal_null_cover_aux {i R : Type u}
    [MeasurableSpace i] (nu : Measure i) {s : Set i} (M : R → Set i)
    (hMsub : ∀ r, M r ⊆ s) (hMnull : ∀ r, nu (M r) = 0) (hMpos : 0 < nu (⋃ r, M r))
    (hsmall : ∀ {J : Type u} (C : J → Set i), (∀ j, C j ⊆ s) →
      (∀ j, nu (C j) = 0) → Cardinal.mk J < Cardinal.mk R → nu (⋃ j, C j) = 0)
    [LinearOrder R] [WellFoundedLT R]
    (hord : Cardinal.ord (Cardinal.mk R) = Ordinal.type ((· < ·) : R → R → Prop)) (r : R) :
    0 < nu (⋃ q ∈ Ici r, M q) := by
  let initial : Set i := ⋃ q : Iio r, M q.1
  have hinitial : nu initial = 0 := hsmall (fun q : Iio r ↦ M q.1) (fun q ↦ hMsub q.1)
    (fun q ↦ hMnull q.1) (Cardinal.mk_Iio_lt r hord)
  by_contra htail
  refine hMpos.ne' (measure_mono_null ?_ (measure_union_null hinitial <|
    nonpos_iff_eq_zero.1 (not_lt.1 htail)))
  intro x hx
  obtain ⟨q, hxq⟩ := mem_iUnion.1 hx
  rcases lt_or_ge q r with hqr | hrq
  · exact Or.inl (mem_iUnion.2 ⟨⟨q, hqr⟩, hxq⟩)
  · exact Or.inr (mem_iUnion₂.2 ⟨q, hrq, hxq⟩)

private theorem iUnion_compl_sInter_eq_aux {R α : Type*} (M : R → Set α)
    (S : Set (Set R)) :
    (⋃ r ∈ (⋂₀ S)ᶜ, M r) = ⋃ t : S, ⋃ r ∈ (t.1)ᶜ, M r := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.1 hx
    change r ∉ ⋂₀ S at hr
    rw [mem_sInter] at hr
    push Not at hr
    obtain ⟨t, htS, hrt⟩ := hr
    exact mem_iUnion.2 ⟨⟨t, htS⟩, mem_iUnion₂.2 ⟨r, hrt, hxr⟩⟩
  · intro hx
    obtain ⟨t, r, hrt, hxr⟩ := by simpa only [mem_iUnion] using hx
    apply mem_iUnion₂.2
    refine ⟨r, ?_, hxr⟩
    change r ∉ ⋂₀ S
    exact fun hr ↦ hrt (mem_sInter.1 hr t t.2)

private theorem measure_or_measure_compl_eq_zero_of_atom_aux {i R : Type*}
    [MeasurableSpace i] [MeasurableSpace R] (nu : Measure i) (rho : Measure R) {s : Set i}
    (hatom : ∀ t ⊆ s, nu t = 0 ∨ nu (s \ t) = 0) (M : R → Set i)
    (hMdisj : Pairwise (Disjoint on M)) (hMsub : ∀ r, M r ⊆ s)
    (hrho : ∀ t : Set R, rho t = nu (⋃ r ∈ t, M r)) (t : Set R) :
    rho t = 0 ∨ rho tᶜ = 0 := by
  have ht_sub : (⋃ r ∈ t, M r) ⊆ s := iUnion_subset fun r ↦ iUnion_subset fun _ ↦ hMsub r
  rcases hatom _ ht_sub with ht | ht
  · exact Or.inl ((hrho t).trans ht)
  · refine Or.inr ((hrho tᶜ).trans (measure_mono_null ?_ ht))
    intro x hx
    obtain ⟨r, hrt, hxr⟩ := mem_iUnion₂.1 hx
    refine ⟨hMsub r hxr, fun hx' ↦ ?_⟩
    obtain ⟨q, hqt, hxq⟩ := mem_iUnion₂.1 hx'
    have hrq : r ≠ q := fun h ↦ hrt (h ▸ hqt)
    exact Set.disjoint_left.1 (hMdisj hrq) hxr hxq

private theorem Measure.exists_cardinalInterUltrafilter_aux {i R : Type u}
    [MeasurableSpace i] (nu : Measure i) (hall : ∀ s : Set i, MeasurableSet s)
    {s : Set i} (hatom : ∀ t ⊆ s, nu t = 0 ∨ nu (s \ t) = 0)
    (M : R → Set i) (hMdisj : Pairwise (Disjoint on M)) (hMsub : ∀ r, M r ⊆ s)
    (hMnull : ∀ r, nu (M r) = 0) (hMpos : 0 < nu (⋃ r, M r))
    (hsmall : ∀ {J : Type u} (C : J → Set i), (∀ j, C j ⊆ s) →
      (∀ j, nu (C j) = 0) → Cardinal.mk J < Cardinal.mk R → nu (⋃ j, C j) = 0) :
    ∃ U : Ultrafilter R, (U : Filter R) ≤ Filter.cofinite ∧
      CardinalInterFilter (U : Filter R) (Cardinal.mk R) := by
  classical
  letI : MeasurableSpace R := ⊤
  let rho := nu.inducedIndexMeasure M hMdisj fun t ↦ hall _
  have hrho (t : Set R) : rho t = nu (⋃ r ∈ t, M r) :=
    Measure.inducedIndexMeasure_apply (fun _ ↦ MeasurableSet.of_discrete) M hMdisj _ t
  have hrho_pos : 0 < rho univ := by simpa [hrho] using hMpos
  have hrho_atom (t : Set R) : rho t = 0 ∨ rho tᶜ = 0 :=
    measure_or_measure_compl_eq_zero_of_atom_aux nu rho hatom M hMdisj hMsub hrho t
  let F : Filter R := Filter.comk (fun t ↦ rho t = 0) (by simp)
    (fun _ ht _ hut ↦ measure_mono_null hut ht) fun _ ht _ hu ↦ measure_union_null ht hu
  have hF_ultra (t : Set R) : tᶜ ∉ F ↔ t ∈ F := by
    change rho (tᶜ)ᶜ ≠ 0 ↔ rho tᶜ = 0
    rw [compl_compl]
    constructor
    · exact fun ht ↦ (hrho_atom t).resolve_left ht
    · intro ht htzero
      have : rho univ = 0 := by
        rw [← union_compl_self t]
        exact measure_union_null htzero ht
      exact hrho_pos.ne' this
  let U : Ultrafilter R := Ultrafilter.ofComplNotMemIff F hF_ultra
  have hUfree : (U : Filter R) ≤ Filter.cofinite := by
    intro t ht
    change rho tᶜ = 0
    rw [hrho]
    exact (measure_biUnion_null_iff (Filter.mem_cofinite.1 ht).countable).2 fun r _ ↦ hMnull r
  have hUinter : CardinalInterFilter (U : Filter R) (Cardinal.mk R) := by
    refine ⟨fun S hSc hS ↦ ?_⟩
    let C : S → Set i := fun t ↦ ⋃ r ∈ (t.1)ᶜ, M r
    have hCsub (t : S) : C t ⊆ s := iUnion_subset fun r ↦
      iUnion_subset fun _ ↦ hMsub r
    have hCnull (t : S) : nu (C t) = 0 := by
      rw [← hrho]
      exact hS t t.2
    change rho ((⋂₀ S)ᶜ) = 0
    rw [hrho]
    have hnull := hsmall C hCsub hCnull hSc
    rw [iUnion_compl_sInter_eq_aux]
    exact hnull
  exact ⟨U, hUfree, hUinter⟩

private theorem ultrafilter_exists_fiber_mem_of_card_lt {R C : Type u} {κ : Cardinal.{u}}
    (U : Ultrafilter R) [CardinalInterFilter (U : Filter R) κ]
    (hC : Cardinal.mk C < κ) (color : R → C) :
    ∃ c, color ⁻¹' {c} ∈ U := by
  classical
  by_contra h
  push Not at h
  have hcompl (c : C) : (color ⁻¹' {c})ᶜ ∈ U := U.compl_mem_iff_notMem.2 (h c)
  have hinter : (⋂ c, (color ⁻¹' {c})ᶜ) ∈ U :=
    (Filter.cardinal_iInter_mem hC).2 hcompl
  have hempty : (⋂ c, (color ⁻¹' {c})ᶜ) = ∅ := by
    ext x
    simp
  rw [hempty] at hinter
  exact U.empty_notMem hinter

private theorem ultrafilter_exists_largeColor {R C : Type u} {κ : Cardinal.{u}}
    [DecidableEq R] (U : Ultrafilter R) (hfree : (U : Filter R) ≤ cofinite)
    [CardinalInterFilter (U : Filter R) κ] (hC : Cardinal.mk C < κ)
    (color : Finset R → C) :
    ∃ largeColor : ℕ → Finset R → C, (∀ F, largeColor 0 F = color F) ∧
      ∀ n F, {x : R | x ∉ F ∧ largeColor n (insert x F) = largeColor (n + 1) F} ∈ U := by
  classical
  choose pick hpick using fun f : R → C ↦ ultrafilter_exists_fiber_mem_of_card_lt U hC f
  let largeColor : ℕ → Finset R → C := fun n ↦
    Nat.rec color (fun _ previous F ↦ pick fun x ↦ previous (insert x F)) n
  have largeColor_zero (F : Finset R) : largeColor 0 F = color F := rfl
  have largeColor_succ (n : ℕ) (F : Finset R) :
      largeColor (n + 1) F = pick (fun x ↦ largeColor n (insert x F)) := by
    simp [largeColor]
  refine ⟨largeColor, largeColor_zero, fun n F ↦ ?_⟩
  have hFcompl : (F : Set R)ᶜ ∈ U := hfree F.finite_toSet.compl_mem_cofinite
  have hpick' := hpick fun x ↦ largeColor n (insert x F)
  rw [← largeColor_succ n F] at hpick'
  filter_upwards [hFcompl, hpick'] with x hxF hxColor
  exact ⟨hxF, hxColor⟩

private theorem ultrafilter_compl_mem_of_mk_lt {R : Type u} {κ : Cardinal.{u}}
    (U : Ultrafilter R) (hfree : (U : Filter R) ≤ cofinite)
    [CardinalInterFilter (U : Filter R) κ] {s : Set R} (hs : Cardinal.mk s < κ) :
    sᶜ ∈ U := by
  have hinter : (⋂ x : s, ({(x : R)} : Set R)ᶜ) ∈ U :=
    (Filter.cardinal_iInter_mem hs).2 fun x ↦ hfree (finite_singleton (x : R)).compl_mem_cofinite
  convert hinter using 1
  ext x
  simp only [mem_compl_iff, mem_iInter, mem_singleton_iff, Subtype.forall]
  constructor
  · exact fun h i hi hxi ↦ h (hxi ▸ hi)
  · exact fun h hx ↦ h x hx rfl

private theorem ultrafilter_exists_homogeneous_next_aux {R C : Type u} {κ : Cardinal.{u}}
    [DecidableEq R] (U : Ultrafilter R) (hfree : (U : Filter R) ≤ cofinite)
    [CardinalInterFilter (U : Filter R) κ] (hκ : ℵ₀ < κ)
    (largeColor : ℕ → Finset R → C)
    (hlarge : ∀ n F, {x : R | x ∉ F ∧ largeColor n (insert x F) = largeColor (n + 1) F} ∈ U)
    (a : κ.ord.ToType) (previous : ∀ b, b < a → R) :
    ∃ x, x ∉ range (fun b : Iio a ↦ previous b.1 b.2) ∧
      ∀ (l : List (Iio a)) (n : ℕ),
        let F := (l.map fun b ↦ previous b.1 b.2).toFinset
        x ∉ F ∧ largeColor n (insert x F) = largeColor (n + 1) F := by
  let prior : Set R := range fun b : Iio a ↦ previous b.1 b.2
  let good : List (Iio a) × ℕ → Set R := fun p ↦
    let F := (p.1.map fun b ↦ previous b.1 b.2).toFinset
    {x | x ∉ F ∧ largeColor p.2 (insert x F) = largeColor (p.2 + 1) F}
  have hpred : Cardinal.mk (Iio a) < κ := by
    simpa only [Cardinal.mk_ord_toType] using Cardinal.mk_Iio_lt a (by simp)
  have hlist : Cardinal.mk (List (Iio a)) < κ :=
    (Cardinal.mk_list_le_max _).trans_lt (max_lt hκ hpred)
  have hindex : Cardinal.mk (List (Iio a) × ℕ) < κ := by
    rw [Cardinal.mk_prod, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact Cardinal.mul_lt_of_lt hκ.le (by simpa using hlist) hκ
  have hinter : (⋂ p, good p) ∈ U :=
    (Filter.cardinal_iInter_mem hindex).2 fun p ↦ hlarge p.2 _
  have hprior : Cardinal.mk prior < κ := Cardinal.mk_range_le.trans_lt hpred
  obtain ⟨x, hxprior, hxgood⟩ := U.nonempty_of_mem <| inter_mem
    (ultrafilter_compl_mem_of_mk_lt U hfree hprior) hinter
  exact ⟨x, hxprior, fun l n ↦ mem_iInter.1 hxgood (l, n)⟩

private theorem largeColor_image_eq_empty_aux {O R C : Type*} [LinearOrder O]
    [WellFoundedLT O] [DecidableEq R] (largeColor : ℕ → Finset R → C) (selected : O → R)
    (hselected : ∀ (a : O) (l : List (Iio a)) (n : ℕ),
      let F := (l.map fun b ↦ selected b.1).toFinset
      selected a ∉ F ∧ largeColor n (insert (selected a) F) = largeColor (n + 1) F)
    (G : Finset O) (m : ℕ) (hm : G.card ≤ m) :
    largeColor (m - G.card) (G.image selected) = largeColor m ∅ := by
  induction G using Finset.induction_on_max with
  | empty => simp
  | insert a G hmax ih =>
    have haG : a ∉ G := fun haG ↦ (hmax a haG).false
    let l : List (Iio a) := G.attach.toList.map fun b ↦ ⟨b.1, hmax b.1 b.2⟩
    have hl : (l.map fun b ↦ selected b.1).toFinset = G.image selected := by
      ext x
      simp [l]
    have hstep := hselected a l (m - (insert a G).card)
    rw [hl] at hstep
    have hsub_succ : m - (insert a G).card + 1 = m - G.card := by
      have : (insert a G).card = G.card + 1 := by simp [haG]
      omega
    calc
      largeColor (m - (insert a G).card) ((insert a G).image selected) =
          largeColor (m - (insert a G).card) (insert (selected a) (G.image selected)) := by
            rw [Finset.image_insert]
      _ = largeColor (m - (insert a G).card + 1) (G.image selected) := hstep.2
      _ = largeColor (m - G.card) (G.image selected) := by rw [hsub_succ]
      _ = largeColor m ∅ := ih (by omega)

private theorem ultrafilter_exists_cardinal_homogeneous_set {R C : Type u} {κ : Cardinal.{u}}
    (U : Ultrafilter R) (hfree : (U : Filter R) ≤ cofinite)
    [CardinalInterFilter (U : Filter R) κ] (hκ : ℵ₀ < κ) (hC : Cardinal.mk C < κ)
    (color : Finset R → C) :
    ∃ Q : Set R, Cardinal.mk Q = κ ∧
      ∀ m, ∃ c, ∀ F : Finset R, (F : Set R) ⊆ Q → F.card = m → color F = c := by
  classical
  letI : DecidableEq R := Classical.decEq R
  obtain ⟨largeColor, largeColor_zero, hlarge⟩ :=
    ultrafilter_exists_largeColor U hfree hC color
  let O := κ.ord.ToType
  choose next hnext_prior hnext_good using fun a : O ↦
    ultrafilter_exists_homogeneous_next_aux U hfree hκ largeColor hlarge a
  let selected : O → R := wellFounded_lt.fix fun a previous ↦ next a previous
  have selected_eq (a : O) : selected a = next a fun b _ ↦ selected b :=
    WellFounded.fix_eq wellFounded_lt (fun a previous ↦ next a previous) a
  have selected_good (a : O) (l : List (Iio a)) (n : ℕ) :
      let F := (l.map fun b ↦ selected b.1).toFinset
      selected a ∉ F ∧ largeColor n (insert (selected a) F) = largeColor (n + 1) F := by
    rw [selected_eq]
    exact hnext_good a (fun b _ ↦ selected b) l n
  have selected_ne_of_lt {a b : O} (hab : a < b) : selected b ≠ selected a := by
    rw [selected_eq]
    exact fun h ↦ hnext_prior b (fun c _ ↦ selected c) ⟨⟨a, hab⟩, h.symm⟩
  have selected_inj : Function.Injective selected := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact selected_ne_of_lt h hab.symm
    · exact selected_ne_of_lt h hab
  let Q : Set R := range selected
  have hQcard : Cardinal.mk Q = κ := by
    change Cardinal.mk (range selected) = κ
    rw [Cardinal.mk_range_eq selected selected_inj, Cardinal.mk_ord_toType]
  refine ⟨Q, hQcard, fun m ↦ ⟨largeColor m ∅, fun F hFQ hFm ↦ ?_⟩⟩
  choose pre hpre using fun x : F ↦ hFQ x.2
  let G : Finset O := Finset.univ.image pre
  have pre_inj : Function.Injective pre := fun x y h ↦ Subtype.ext <| by
    rw [← hpre x, ← hpre y, h]
  have hGcard : G.card = F.card := by
    change (Finset.univ.image pre).card = F.card
    rw [Finset.card_image_of_injective _ pre_inj]
    exact Fintype.card_coe F
  have hGimage : G.image selected = F := by
    change (Finset.univ.image pre).image selected = F
    rw [Finset.image_image]
    have hcomp : selected ∘ pre = fun x : F ↦ (x : R) := funext hpre
    rw [hcomp]
    ext x
    simp
  have h := largeColor_image_eq_empty_aux largeColor selected selected_good G m (by omega)
  rw [hGcard, hFm, Nat.sub_self, hGimage, largeColor_zero] at h
  exact h

private theorem Measure.exists_extension_approx_aux {i : Type*} [MeasurableSpace i]
    (nu : Measure i) [IsFiniteMeasure nu] {s u : Set i} {a : ENNReal} (hus : u ⊆ s)
    (hua : nu u ≤ a) (ha : a ≠ ⊤) (n : ℕ) :
    ∃ t, u ⊆ t ∧ t ⊆ s ∧ nu t ≤ a ∧
      ∀ w, u ⊆ w → w ⊆ s → nu w ≤ a → nu.real w ≤ nu.real t + 1 / (n + 1) := by
  let E : Set ℝ := nu.real '' {t : Set i | u ⊆ t ∧ t ⊆ s ∧ nu t ≤ a}
  have hE : E.Nonempty := ⟨nu.real u, u, ⟨subset_rfl, hus, hua⟩, rfl⟩
  have hE_bdd : BddAbove E := by
    refine ⟨a.toReal, ?_⟩
    rintro r ⟨t, ⟨-, -, hta⟩, rfl⟩
    exact ENNReal.toReal_mono ha hta
  by_cases hsup : sSup E ≤ nu.real u + 1 / (n + 1)
  · refine ⟨u, subset_rfl, hus, hua, fun w huw hws hwa ↦ ?_⟩
    exact (le_csSup hE_bdd ⟨w, ⟨huw, hws, hwa⟩, rfl⟩).trans hsup
  · have hε : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hsub : sSup E - 1 / (n + 1) < sSup E := sub_lt_self _ hε
    obtain ⟨r, ⟨t, ht, rfl⟩, htr⟩ := exists_lt_of_lt_csSup hE hsub
    refine ⟨t, ht.1, ht.2.1, ht.2.2, fun w huw hws hwa ↦ ?_⟩
    have hw : nu.real w ≤ sSup E :=
      le_csSup hE_bdd ⟨w, ⟨huw, hws, hwa⟩, rfl⟩
    linarith

private theorem Measure.measure_iUnion_eq_of_extension_approx_aux {i : Type*}
    [MeasurableSpace i] (nu : Measure i) [IsFiniteMeasure nu]
    (hall : ∀ s : Set i, MeasurableSet s)
    (hsplit : ∀ s : Set i, 0 < nu s → ∃ t ⊆ s, 0 < nu t ∧ 0 < nu (s \ t))
    {s : Set i} {a : ENNReal} (ha : a ≤ nu s) (u : ℕ → Set i) (hu_mono : Monotone u)
    (hus : ∀ n, u n ⊆ s) (hua : ∀ n, nu (u n) ≤ a)
    (happrox : ∀ n w, u n ⊆ w → w ⊆ s → nu w ≤ a →
      nu.real w ≤ nu.real (u (n + 1)) + 1 / (n + 1)) :
    nu (⋃ n, u n) = a := by
  let U : Set i := ⋃ n, u n
  have hUs : U ⊆ s := iUnion_subset hus
  have hU_le : nu U ≤ a := by
    change nu (⋃ n, u n) ≤ a
    rw [hu_mono.measure_iUnion]
    exact iSup_le hua
  apply le_antisymm hU_le
  by_contra hnot
  have hU_lt : nu U < a := lt_of_not_ge hnot
  have hres_pos : 0 < nu (s \ U) := by
    rw [measure_sdiff hUs (hall U).nullMeasurableSet (measure_ne_top nu U)]
    exact tsub_pos_iff_lt.2 (hU_lt.trans_le ha)
  have hgap_pos : 0 < a - nu U := tsub_pos_iff_lt.2 hU_lt
  obtain ⟨t, htres, htpos, htgap⟩ :=
    nu.exists_pos_measure_le_of_splits_aux hall hsplit hres_pos hgap_pos
  have htU : Disjoint U t := Set.disjoint_left.2 fun x hxU hxt ↦ htres hxt |>.2 hxU
  let w := U ∪ t
  have hw_measure : nu w = nu U + nu t := measure_union htU (hall t)
  have hw_le : nu w ≤ a := by
    rw [hw_measure]
    exact (ENNReal.le_sub_iff_add_le_left (measure_ne_top nu U) hU_le).1 htgap
  have hw_s : w ⊆ s := union_subset hUs (htres.trans sdiff_subset)
  have hw_real : nu.real w = nu.real U + nu.real t := measureReal_union htU (hall t)
  have ht_real_pos : 0 < nu.real t :=
    ENNReal.toReal_pos htpos.ne' (measure_ne_top nu t)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht_real_pos
  have huU : u n ⊆ U := subset_iUnion u n
  have happ := happrox n w (huU.trans subset_union_left) hw_s hw_le
  have hunU : nu.real (u (n + 1)) ≤ nu.real U :=
    measureReal_mono (subset_iUnion u (n + 1))
  rw [hw_real] at happ
  have : nu.real t ≤ 1 / (n + 1) := by
    linarith
  exact ((not_le_of_gt hn) this).elim

private theorem Measure.exists_subset_measure_eq_of_splits_aux {i : Type*} [MeasurableSpace i]
    (nu : Measure i) [IsFiniteMeasure nu] (hall : ∀ s : Set i, MeasurableSet s)
    (hsplit : ∀ s : Set i, 0 < nu s → ∃ t ⊆ s, 0 < nu t ∧ 0 < nu (s \ t))
    {s : Set i} {a : ENNReal} (ha : a ≤ nu s) : ∃ t ⊆ s, nu t = a := by
  classical
  have ha_top : a ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top nu s) ha
  let V := {t : Set i // t ⊆ s ∧ nu t ≤ a}
  let u0 : V := ⟨∅, empty_subset _, by simp⟩
  choose next hnext_sub hnext_s hnext_a hnext_approx using fun (n : ℕ) (u : V) ↦
    nu.exists_extension_approx_aux u.2.1 u.2.2 ha_top n
  let next' : ℕ → V → V := fun n u ↦ ⟨next n u, hnext_s n u, hnext_a n u⟩
  let u : ℕ → V := fun n ↦ Nat.rec u0 (fun n u ↦ next' n u) n
  have u_succ (n : ℕ) : u (n + 1) = next' n (u n) := by simp [u]
  have hu_mono : Monotone (fun n : ℕ ↦ (u n).1) := monotone_nat_of_le_succ fun n ↦ by
    rw [u_succ]
    exact hnext_sub n (u n)
  have happrox (n : ℕ) (w : Set i) (hunw : (u n).1 ⊆ w) (hws : w ⊆ s)
      (hwa : nu w ≤ a) :
      nu.real w ≤ nu.real (u (n + 1)).1 + 1 / (n + 1) := by
    rw [u_succ]
    exact hnext_approx n (u n) w hunw hws hwa
  let U : Set i := ⋃ n, (u n).1
  refine ⟨U, iUnion_subset fun n ↦ (u n).2.1, ?_⟩
  exact nu.measure_iUnion_eq_of_extension_approx_aux hall hsplit ha _ hu_mono
    (fun n ↦ (u n).2.1) (fun n ↦ (u n).2.2) happrox

private theorem Measure.measure_binarySplitNode_aux {i : Type*} [MeasurableSpace i]
    (nu : Measure i) [IsFiniteMeasure nu] (hall : ∀ t : Set i, MeasurableSet t)
    (half : Set i → Set i)
    (hhalf_sub : ∀ t, half t ⊆ t) (hhalf_measure : ∀ t, nu (half t) = nu t / 2)
    (s : Set i) (l : List Bool) :
    nu (l.foldr (fun b parent ↦ match b with
      | false => half parent
      | true => parent \ half parent) s) =
      nu s * (2⁻¹ : ENNReal) ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    cases b
    · change nu (half (l.foldr _ s)) = _
      rw [hhalf_measure, ih, div_eq_mul_inv]
      simp [pow_succ, mul_assoc]
    · change nu (l.foldr _ s \ half (l.foldr _ s)) = _
      rw [measure_sdiff (hhalf_sub _) (hall _).nullMeasurableSet (measure_ne_top nu _),
        hhalf_measure, ENNReal.sub_half (measure_ne_top nu _), ih, div_eq_mul_inv]
      simp [pow_succ, mul_assoc]

private theorem Measure.exists_nullFiber_map_of_splits_aux {i : Type*} [MeasurableSpace i]
    (nu : Measure i) [IsFiniteMeasure nu] (hall : ∀ s : Set i, MeasurableSet s)
    (hsplit : ∀ s : Set i, 0 < nu s → ∃ t ⊆ s, 0 < nu t ∧ 0 < nu (s \ t))
    (s : Set i) : ∃ code : i → ℕ → Bool, ∀ b, nu (s ∩ code ⁻¹' {b}) = 0 := by
  classical
  choose half hhalf_sub hhalf_measure using fun t : Set i ↦
    nu.exists_subset_measure_eq_of_splits_aux hall hsplit (s := t) (a := nu t / 2)
      ENNReal.half_le_self
  let node : List Bool → Set i := fun l ↦ l.foldr
    (fun b parent ↦ match b with | false => half parent | true => parent \ half parent) s
  have hnode_measure (l : List Bool) :
      nu (node l) = nu s * (2⁻¹ : ENNReal) ^ l.length :=
    nu.measure_binarySplitNode_aux hall half hhalf_sub hhalf_measure s l
  let path (x : i) : ℕ → List Bool := fun n ↦ Nat.rec []
    (fun _ l ↦ (if x ∈ half (node l) then false else true) :: l) n
  let code : i → ℕ → Bool := fun x n ↦ if x ∈ half (node (path x n)) then false else true
  have path_succ (x : i) (n : ℕ) : path x (n + 1) = code x n :: path x n := by
    simp [path, code]
  have hxnode {x : i} (hxs : x ∈ s) : ∀ n, x ∈ node (path x n) := by
    intro n
    induction n with
    | zero => simpa [node, path]
    | succ n ih =>
      rw [path_succ]
      simp only [node, List.foldr_cons, code]
      split_ifs with hx
      · exact hx
      · refine ⟨?_, hx⟩
        simpa only [node] using ih
  let pref (b : ℕ → Bool) : ℕ → List Bool := fun n ↦ Nat.rec [] (fun n l ↦ b n :: l) n
  have pref_succ (b : ℕ → Bool) (n : ℕ) : pref b (n + 1) = b n :: pref b n := by
    simp [pref]
  have pref_length (b : ℕ → Bool) (n : ℕ) : (pref b n).length = n := by
    induction n <;> simp_all [pref]
  have path_eq_pref (x : i) (n : ℕ) : path x n = pref (code x) n := by
    induction n with
    | zero => simp [path, pref]
    | succ n ih => rw [path_succ, pref_succ, ih]
  have hlim (b : ℕ → Bool) :
      Tendsto (fun n ↦ nu (node (pref b n))) atTop (𝓝 0) := by
    simp_rw [hnode_measure, pref_length]
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2⁻¹ : ENNReal) < 1))
      (Or.inr (measure_ne_top nu s))
  have hfiber (b : ℕ → Bool) (n : ℕ) : s ∩ code ⁻¹' {b} ⊆ node (pref b n) := by
    intro x hx
    have hxb : code x = b := by
      simpa only [mem_preimage, mem_singleton_iff] using hx.2
    rw [← hxb]
    rw [← path_eq_pref x n]
    exact hxnode hx.1 n
  exact ⟨code, fun b ↦
    bot_unique (ge_of_tendsto' (hlim b) fun n ↦ measure_mono (hfiber b n))⟩

private def UncountableCompactUnitInterval :=
  {K : Set ℝ // IsCompact K ∧ K ⊆ Icc 0 1 ∧ ¬K.Countable}

private theorem mk_uncountableCompactUnitInterval :
    Cardinal.mk UncountableCompactUnitInterval = 𝔠 := by
  let code : UncountableCompactUnitInterval → Set (countableBasis ℝ) := fun K ↦
    {b | (b : Set ℝ) ⊆ K.1ᶜ}
  have code_inj : Function.Injective code := by
    intro K L hKL
    apply Subtype.ext
    apply compl_injective
    apply Subset.antisymm
    · intro x hx
      obtain ⟨b, hb, hxb, hbK⟩ :=
        (isBasis_countableBasis ℝ).exists_subset_of_mem_open hx K.2.1.isClosed.isOpen_compl
      have hbcode : (⟨b, hb⟩ : countableBasis ℝ) ∈ code K := hbK
      rw [hKL] at hbcode
      exact hbcode hxb
    · intro x hx
      obtain ⟨b, hb, hxb, hbL⟩ :=
        (isBasis_countableBasis ℝ).exists_subset_of_mem_open hx L.2.1.isClosed.isOpen_compl
      have hbcode : (⟨b, hb⟩ : countableBasis ℝ) ∈ code L := hbL
      rw [← hKL] at hbcode
      exact hbcode hxb
  let natCode : UncountableCompactUnitInterval → Set ℕ := fun K ↦ Encodable.encode '' code K
  have natCode_inj : Function.Injective natCode :=
    (Set.image_injective.2 Encodable.encode_injective).comp code_inj
  have hupper : Cardinal.mk UncountableCompactUnitInterval ≤ 𝔠 := by
    rw [← Cardinal.mk_set_nat]
    exact Cardinal.mk_le_of_injective natCode_inj
  let interval : Icc (1 / 2 : ℝ) 1 → UncountableCompactUnitInterval := fun x ↦
    ⟨Icc 0 x, isCompact_Icc, fun y hy ↦ ⟨hy.1, hy.2.trans x.2.2⟩, by
      rw [Cardinal.Real.Icc_countable_iff]
      exact not_le_of_gt ((by norm_num : (0 : ℝ) < 1 / 2).trans_le x.2.1)⟩
  have interval_inj : Function.Injective interval := by
    intro x y hxy
    have hsets : Icc 0 (x : ℝ) = Icc 0 (y : ℝ) := congr_arg Subtype.val hxy
    apply Subtype.ext
    apply le_antisymm
    · have hxmem : (x : ℝ) ∈ Icc 0 (y : ℝ) := by
        rw [← hsets]
        exact ⟨(by linarith [x.2.1]), le_rfl⟩
      exact hxmem.2
    · have hymem : (y : ℝ) ∈ Icc 0 (x : ℝ) := by
        rw [hsets]
        exact ⟨(by linarith [y.2.1]), le_rfl⟩
      exact hymem.2
  apply le_antisymm hupper
  rw [← Cardinal.mk_Icc_real (by norm_num : (1 / 2 : ℝ) < 1)]
  exact Cardinal.mk_le_of_injective interval_inj

private theorem UncountableCompactUnitInterval.mk_carrier
    (K : UncountableCompactUnitInterval) : Cardinal.mk K.1 = 𝔠 := by
  refine le_antisymm ((Cardinal.mk_subtype_le _).trans_eq Cardinal.mk_real) ?_
  obtain ⟨g, hg, -, hg_inj⟩ := K.2.1.isClosed.exists_nat_bool_injection_of_not_countable K.2.2.2
  let g' : (ℕ → Bool) → K.1 := fun b ↦ ⟨g b, hg (mem_range_self b)⟩
  rw [← show Cardinal.mk (ℕ → Bool) = 𝔠 by
    rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]]
  exact Cardinal.mk_le_of_injective (f := g') fun _ _ h ↦ hg_inj (by
    simpa [g'] using congr_arg Subtype.val h)

private theorem exists_pair_avoiding_prior [LinearOrder UncountableCompactUnitInterval]
    [WellFoundedLT UncountableCompactUnitInterval]
    (hord : Cardinal.ord (Cardinal.mk UncountableCompactUnitInterval) =
      Ordinal.type ((· < ·) : UncountableCompactUnitInterval →
        UncountableCompactUnitInterval → Prop))
    (K : UncountableCompactUnitInterval)
    (previous : ∀ J, J < K → ℝ × ℝ) :
    ∃ r s, r ∈ Icc (0 : ℝ) 1 ∧ s ∈ K.1 ∧ r ≠ s ∧
      ∀ J (hJ : J < K), r ≠ (previous J hJ).1 ∧ r ≠ (previous J hJ).2 ∧
        s ≠ (previous J hJ).1 ∧ s ≠ (previous J hJ).2 := by
  let prior : Iio K × Bool → ℝ := fun p ↦
    if p.2 then (previous p.1 p.1.2).1 else (previous p.1 p.1.2).2
  let bad : Set ℝ := range prior
  have hpred : Cardinal.mk (Iio K) < 𝔠 := by
    rw [← mk_uncountableCompactUnitInterval]
    exact Cardinal.mk_Iio_lt K hord
  have hprior : Cardinal.mk (Iio K × Bool) < 𝔠 := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_bool]
    exact Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum hpred
      (by simpa using Cardinal.nat_lt_continuum 2)
  have hbad : Cardinal.mk bad < 𝔠 := Cardinal.mk_range_le.trans_lt hprior
  have hs_nonempty : (K.1 \ bad).Nonempty := by
    apply Cardinal.sdiff_nonempty_of_mk_lt_mk
    rwa [K.mk_carrier]
  obtain ⟨s, hsK, hsbad⟩ := hs_nonempty
  let bad' := bad ∪ {s}
  have hbad' : Cardinal.mk bad' < 𝔠 := by
    refine (Cardinal.mk_union_le bad {s}).trans_lt ?_
    rw [Cardinal.mk_singleton]
    exact Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum hbad
      (Cardinal.nat_lt_continuum 1)
  have hr_nonempty : (Icc (0 : ℝ) 1 \ bad').Nonempty := by
    apply Cardinal.sdiff_nonempty_of_mk_lt_mk
    rwa [Cardinal.mk_Icc_real zero_lt_one]
  obtain ⟨r, hrIcc, hrbad⟩ := hr_nonempty
  refine ⟨r, s, hrIcc, hsK, fun hrs ↦ hrbad (Or.inr hrs), fun J hJ ↦ ?_⟩
  have hfst : (previous J hJ).1 ∈ bad := by
    refine ⟨(⟨J, hJ⟩, true), ?_⟩
    simp [prior]
  have hsnd : (previous J hJ).2 ∈ bad := by
    refine ⟨(⟨J, hJ⟩, false), ?_⟩
    simp [prior]
  refine ⟨fun h ↦ hrbad (Or.inl (h ▸ hfst)), fun h ↦ hrbad (Or.inl (h ▸ hsnd)), ?_, ?_⟩
  · intro h
    exact hsbad (h ▸ hfst)
  · intro h
    exact hsbad (h ▸ hsnd)

private theorem exists_bernstein_unitInterval :
    ∃ B : Set ℝ, B ⊆ Icc 0 1 ∧ Cardinal.mk B = 𝔠 ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Icc 0 1 → ¬K.Countable → ¬K ⊆ B := by
  classical
  obtain ⟨order, wf, hord⟩ :=
    Cardinal.exists_ord_eq_type_lt UncountableCompactUnitInterval
  letI : LinearOrder UncountableCompactUnitInterval := order
  letI : WellFoundedLT UncountableCompactUnitInterval := wf
  choose r s hrIcc hsK hrs hprior using fun K
      (previous : ∀ J, J < K → ℝ × ℝ) ↦ exists_pair_avoiding_prior hord K previous
  let step (K : UncountableCompactUnitInterval)
      (previous : ∀ J, J < K → ℝ × ℝ) : ℝ × ℝ := (r K previous, s K previous)
  let chosen : UncountableCompactUnitInterval → ℝ × ℝ := wellFounded_lt.fix step
  have chosen_eq (K : UncountableCompactUnitInterval) :
      chosen K = step K fun J _ ↦ chosen J := WellFounded.fix_eq wellFounded_lt step K
  let R : UncountableCompactUnitInterval → ℝ := fun K ↦ (chosen K).1
  let S : UncountableCompactUnitInterval → ℝ := fun K ↦ (chosen K).2
  have hR_mem (K : UncountableCompactUnitInterval) : R K ∈ Icc (0 : ℝ) 1 := by
    change (chosen K).1 ∈ Icc (0 : ℝ) 1
    rw [chosen_eq K]
    exact hrIcc K _
  have hS_mem (K : UncountableCompactUnitInterval) : S K ∈ K.1 := by
    change (chosen K).2 ∈ K.1
    rw [chosen_eq K]
    exact hsK K _
  have hRS_self (K : UncountableCompactUnitInterval) : R K ≠ S K := by
    change (chosen K).1 ≠ (chosen K).2
    rw [chosen_eq K]
    exact hrs K _
  have hprior_chosen {J K : UncountableCompactUnitInterval} (hJK : J < K) :
      R K ≠ R J ∧ R K ≠ S J ∧ S K ≠ R J ∧ S K ≠ S J := by
    change (chosen K).1 ≠ (chosen J).1 ∧ (chosen K).1 ≠ (chosen J).2 ∧
      (chosen K).2 ≠ (chosen J).1 ∧ (chosen K).2 ≠ (chosen J).2
    rw [chosen_eq K]
    simpa only [step] using hprior K (fun J _ ↦ chosen J) J hJK
  have hR_inj : Function.Injective R := Function.Injective.of_lt_imp_ne fun J K hJK ↦
    (hprior_chosen hJK).1.symm
  have hSR (J K : UncountableCompactUnitInterval) : S J ≠ R K := by
    rcases lt_trichotomy J K with h | rfl | h
    · exact (hprior_chosen h).2.1.symm
    · exact (hRS_self J).symm
    · exact (hprior_chosen h).2.2.1
  let B : Set ℝ := range R
  have hBsub : B ⊆ Icc (0 : ℝ) 1 := by
    rintro x ⟨K, rfl⟩
    exact hR_mem K
  have hBcard : Cardinal.mk B = 𝔠 := by
    simpa only [B, mk_uncountableCompactUnitInterval] using Cardinal.mk_range_eq R hR_inj
  refine ⟨B, hBsub, hBcard, fun K hK hKI hKunc hKB ↦ ?_⟩
  let K' : UncountableCompactUnitInterval := ⟨K, hK, hKI, hKunc⟩
  obtain ⟨J, hJ⟩ := hKB (hS_mem K')
  exact hSR K' J hJ.symm

private theorem exists_measurable_eqOn_pairwiseDisjoint {i : Type*} (A : i → Set X)
    (hA : Pairwise (Disjoint on A)) (hAmeas : ∀ s : Set i, MeasurableSet (⋃ j ∈ s, A j))
    (label : i → ℝ) :
    ∃ g : X → ℝ, Measurable g ∧ ∀ j, Set.EqOn g (fun _ ↦ label j) (A j) := by
  classical
  let U : Set X := ⋃ j, A j
  let g : X → ℝ := fun x ↦ if hx : ∃ j, x ∈ A j then label (Classical.choose hx) else 0
  have hindex {x : X} {j k : i} (hxj : x ∈ A j) (hxk : x ∈ A k) : j = k := by
    by_contra hjk
    exact Set.disjoint_left.1 (hA hjk) hxj hxk
  have hgA (j : i) : Set.EqOn g (fun _ ↦ label j) (A j) := by
    intro x hx
    have hex : ∃ k, x ∈ A k := ⟨j, hx⟩
    simp only [g, dif_pos hex]
    exact congr_arg label (hindex (Classical.choose_spec hex) hx)
  refine ⟨g, ?_, hgA⟩
  intro t ht
  have hpreimage : g ⁻¹' t =
      (if (0 : ℝ) ∈ t then Uᶜ else ∅) ∪ ⋃ j ∈ {j | label j ∈ t}, A j := by
    ext x
    by_cases hx : ∃ j, x ∈ A j
    · obtain ⟨j, hxj⟩ := hx
      have hxU : x ∈ U := mem_iUnion.2 ⟨j, hxj⟩
      have hg : g x = label j := hgA j hxj
      simp only [mem_preimage, mem_union, mem_iUnion, mem_setOf_eq]
      rw [hg]
      constructor
      · exact fun h ↦ Or.inr ⟨j, h, hxj⟩
      · rintro (h | ⟨k, hkt, hxk⟩)
        · split at h <;> simp_all
        · simpa [hindex hxk hxj] using hkt
    · have hxU : x ∉ U := by
        intro hx'
        exact hx (by simpa only [U, mem_iUnion] using hx')
      have hnoA (j : i) : x ∉ A j := fun hxj ↦ hx ⟨j, hxj⟩
      simp [g, hxU, hnoA]
  rw [hpreimage]
  apply MeasurableSet.union
  · have hUmeas : MeasurableSet U := by
      convert hAmeas univ using 1
      simp [U]
    split <;> simp_all
  · exact hAmeas {j | label j ∈ t}

private theorem measure_setOf_embedding_eq_zero_aux {i : Type*} [MeasurableSpace i]
    (nu : Measure i) (code : i → ℕ → Bool) (hcode : ∀ b, nu (code ⁻¹' {b}) = 0)
    {B : Set ℝ} (e : (ℕ → Bool) ↪ B) (r : ℝ) : nu {j | (e (code j) : ℝ) = r} = 0 := by
  by_cases hr : ∃ j, (e (code j) : ℝ) = r
  · obtain ⟨j, hj⟩ := hr
    apply measure_mono_null (t := code ⁻¹' {code j}) _ (hcode (code j))
    intro k hk
    exact e.injective (Subtype.ext (hk.trans hj.symm))
  · rw [show {j | (e (code j) : ℝ) = r} = ∅ by
      ext j
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun h ↦ hr ⟨j, h⟩]
    simp

private theorem measure_preimage_singleton_inter_iUnion_eq_zero_aux {i : Type*}
    (A : i → Set X) (label : i → ℝ) (g : X → ℝ)
    (hgA : ∀ j, Set.EqOn g (fun _ ↦ label j) (A j))
    (hlabel : ∀ r, μ (⋃ j ∈ {j | label j = r}, A j) = 0) (r : ℝ) :
    μ (g ⁻¹' {r} ∩ ⋃ j, A j) = 0 := by
  rw [show g ⁻¹' {r} ∩ ⋃ j, A j = ⋃ j ∈ {j | label j = r}, A j by
    ext x
    constructor
    · rintro ⟨hgxr, hxU⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.1 hxU
      exact mem_iUnion₂.2 ⟨j, (hgA j hxj).symm.trans hgxr, hxj⟩
    · intro hx
      obtain ⟨j, hjr, hxj⟩ := mem_iUnion₂.1 hx
      exact ⟨(hgA j hxj).trans hjr, mem_iUnion.2 ⟨j, hxj⟩⟩]
  exact hlabel r

private theorem measure_eq_zero_of_countable_image_aux (g : X → ℝ) {U K : Set X}
    (hKU : K ⊆ U) (hcount : (g '' K).Countable)
    (hfiber : ∀ r, μ (g ⁻¹' {r} ∩ U) = 0) : μ K = 0 := by
  letI : Countable (g '' K) := hcount.to_subtype
  rw [show K = ⋃ r : g '' K, K ∩ g ⁻¹' {(r : ℝ)} by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun hx ↦ ⟨⟨g x, mem_image_of_mem g hx⟩, hx, rfl⟩,
      fun ⟨_, hx, _⟩ ↦ hx⟩]
  apply measure_iUnion_null
  intro r
  have hsub : K ∩ g ⁻¹' {(r : ℝ)} ⊆ g ⁻¹' {(r : ℝ)} ∩ U := fun _ hx ↦
    ⟨hx.2, hKU hx.1⟩
  exact measure_mono_null hsub (hfiber r)

private theorem Measure.measure_iUnion_eq_zero_of_pairwiseDisjoint_of_splits_aux
    [TopologicalSpace X] [IsFiniteMeasure μ] {i : Type*} (A : i → Set X)
    (hA : Pairwise (Disjoint on A))
    (hAmeas : ∀ s : Set i, MeasurableSet (⋃ j ∈ s, A j))
    (hLusin : ∀ (g : X → ℝ), Measurable g → ∀ U : Set X, MeasurableSet U → 0 < μ U →
      ∃ K ⊆ U, IsCompact K ∧ ContinuousOn g K ∧ 0 < μ K)
    (hsplit : letI : MeasurableSpace i := ⊤
      let nu := μ.inducedIndexMeasure A hA hAmeas
      ∀ s : Set i, 0 < nu s → ∃ t ⊆ s, 0 < nu t ∧ 0 < nu (s \ t)) :
    μ (⋃ j, A j) = 0 := by
  classical
  letI : MeasurableSpace i := ⊤
  have hall (s : Set i) : MeasurableSet s := MeasurableSet.of_discrete
  let nu := μ.inducedIndexMeasure A hA hAmeas
  letI : IsFiniteMeasure nu := IsFiniteMeasure.mk <| by
    change μ.inducedIndexMeasure A hA hAmeas univ < ∞
    rw [Measure.inducedIndexMeasure_apply hall]
    exact (measure_mono (subset_univ _)).trans_lt (measure_lt_top μ univ)
  have hsplit' : ∀ s : Set i, 0 < nu s → ∃ t ⊆ s, 0 < nu t ∧ 0 < nu (s \ t) := hsplit
  obtain ⟨code, hcode⟩ := nu.exists_nullFiber_map_of_splits_aux hall hsplit' univ
  have hcode_zero (b : ℕ → Bool) : nu (code ⁻¹' {b}) = 0 := by simpa using hcode b
  obtain ⟨B, hBI, hBcard, hBernstein⟩ := exists_bernstein_unitInterval
  have hbranch : Cardinal.mk (ℕ → Bool) = 𝔠 := by
    rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
  have hbranchB : Cardinal.mk (ℕ → Bool) ≤ Cardinal.mk B := by rw [hbranch, hBcard]
  obtain ⟨e⟩ : Nonempty ((ℕ → Bool) ↪ B) :=
    Cardinal.lift_mk_le'.1 (by simpa using hbranchB)
  let label : i → ℝ := fun j ↦ e (code j)
  obtain ⟨g, hg, hgA⟩ := exists_measurable_eqOn_pairwiseDisjoint A hA hAmeas label
  let U : Set X := ⋃ j, A j
  have hUmeas : MeasurableSet U := by
    convert hAmeas univ using 1
    simp [U]
  by_contra hUzero
  obtain ⟨K, hKU, hKcompact, hgK, hKpos⟩ :=
    hLusin g hg U hUmeas (pos_iff_ne_zero.2 hUzero)
  have hlabel_zero (r : ℝ) : nu {j | label j = r} = 0 :=
    measure_setOf_embedding_eq_zero_aux nu code hcode_zero e r
  have hlabel_source (r : ℝ) : μ (⋃ j ∈ {j | label j = r}, A j) = 0 := by
    rw [← Measure.inducedIndexMeasure_apply hall]
    exact hlabel_zero r
  have hfiber_zero (r : ℝ) : μ (g ⁻¹' {r} ∩ U) = 0 :=
    measure_preimage_singleton_inter_iUnion_eq_zero_aux A label g hgA hlabel_source r
  have hKB : g '' K ⊆ B := by
    rintro r ⟨x, hxK, rfl⟩
    obtain ⟨j, hxj⟩ : ∃ j, x ∈ A j := by simpa only [U, mem_iUnion] using hKU hxK
    rw [hgA j hxj]
    exact (e (code j)).2
  have hKimage_count : (g '' K).Countable := by
    by_contra h
    exact hBernstein (g '' K) (hKcompact.image_of_continuousOn hgK) (hKB.trans hBI) h hKB
  exact hKpos.ne' (measure_eq_zero_of_countable_image_aux g hKU hKimage_count hfiber_zero)

/-- The full disjoint-union identity follows once it is known that the union of the null members
of the family is null. -/
theorem Measure.measure_iUnion_eq_tsum_of_pairwiseDisjoint_of_null [SFinite μ]
    {ι : Type*} (s : ι → Set X) (hdisj : Pairwise (Disjoint on s))
    (hmeas : ∀ I : Set ι, MeasurableSet (⋃ i ∈ I, s i))
    (hnull : μ (⋃ i : {i | μ (s i) = 0}, s i) = 0) :
    μ (⋃ i, s i) = ∑' i, μ (s i) := by
  classical
  have hs_meas (i : ι) : MeasurableSet (s i) := by
    simpa using hmeas {i}
  let p : Set ι := {i | 0 < μ (s i)}
  have hp_count : p.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion hs_meas hdisj
  letI : Countable p := hp_count.to_subtype
  have hpos : μ (⋃ i : p, s i) = ∑' i : p, μ (s i) :=
    measure_iUnion
      (fun i j hij ↦ hdisj fun h ↦ hij (Subtype.ext h))
      (fun i ↦ hs_meas i)
  have hsplit : (⋃ i, s i) =
      (⋃ i : p, s i) ∪ ⋃ i : {i | μ (s i) = 0}, s i := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hxi⟩
      rcases eq_or_ne (μ (s i)) 0 with hi | hi
      · exact Or.inr ⟨⟨i, hi⟩, hxi⟩
      · exact Or.inl ⟨⟨i, pos_iff_ne_zero.2 hi⟩, hxi⟩
    · rintro (⟨i, hxi⟩ | ⟨i, hxi⟩) <;> exact ⟨i, hxi⟩
  rw [hsplit, measure_congr (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 hnull)), hpos]
  exact tsum_subtype_eq_of_support_subset fun i hi ↦ pos_iff_ne_zero.2 hi

/-- In a finite measure space, an uncountable family of positive measurable sets contains, for
every positive `m`, `m` distinct members with nonempty intersection. -/
theorem Measure.exists_finset_iInter_nonempty_of_uncountable [IsFiniteMeasure μ]
    {ι : Type*} [Uncountable ι] (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hpos : ∀ i, 0 < μ (s i)) {m : ℕ} (hm : 0 < m) :
    ∃ F : Finset ι, F.card = m ∧ (⋂ i ∈ F, s i).Nonempty := by
  classical
  obtain ⟨n, hn⟩ :
      ∃ n : ℕ, ¬ ({i | (2⁻¹ : ENNReal) ^ n ≤ μ (s i)} : Set ι).Countable := by
    by_contra! h
    refine Set.not_countable_univ ((countable_iUnion h).mono fun i _ ↦ ?_)
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (hpos i).ne'
    exact mem_iUnion.2 ⟨n, hn.le⟩
  let ε : ENNReal := (2⁻¹ : ENNReal) ^ n
  have hε : ε ≠ 0 := by simp [ε]
  have hbound_ne_top : (m - 1 : ℕ) * μ (univ : Set X) ≠ ⊤ := by finiteness
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hε hbound_ne_top
  have hlevel_inf : Set.Infinite {i | ε ≤ μ (s i)} := by
    intro hfin
    exact hn hfin.countable
  obtain ⟨F, hFsub, hFcard⟩ := hlevel_inf.exists_subset_card_eq N
  by_contra! H
  have hcard (x : X) : (F.filter fun i ↦ x ∈ s i).card ≤ m - 1 := by
    by_contra h
    have hmle : m ≤ (F.filter fun i ↦ x ∈ s i).card := by omega
    obtain ⟨G, hGsub, hGcard⟩ := Finset.exists_subset_card_eq hmle
    have hx : x ∈ ⋂ i ∈ G, s i := mem_iInter₂.2 fun i hi ↦
      (Finset.mem_filter.1 (hGsub hi)).2
    simp [H G hGcard] at hx
  have hpoint (x : X) :
      (∑ i ∈ F, (s i).indicator (1 : X → ENNReal) x) ≤ (m - 1 : ℕ) := by
    simpa only [Finset.sum_apply, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_le]
      using hcard x
  have hint :
      (∫⁻ x, ∑ i ∈ F, (s i).indicator (1 : X → ENNReal) x ∂μ) =
        ∑ i ∈ F, μ (s i) := by
    rw [lintegral_finsetSum F]
    · simp_rw [lintegral_indicator_one (hs _)]
    · exact fun i _ ↦ measurable_const.indicator (hs i)
  have hsum_lower : (N : ENNReal) * ε ≤ ∑ i ∈ F, μ (s i) := by
    rw [← hFcard, ← nsmul_eq_mul]
    exact F.card_nsmul_le_sum _ _ fun i hi ↦ hFsub hi
  have hsum_upper : ∑ i ∈ F, μ (s i) ≤ (m - 1 : ℕ) * μ (univ : Set X) := by
    rw [← hint, ← lintegral_const]
    exact lintegral_mono hpoint
  exact not_le_of_gt (hN.trans_le hsum_lower) hsum_upper

private noncomputable def compactIntersectionColor {R : Type u} (K : R → Set X)
    (F : Finset R) : ULift.{u} Bool := by
  classical
  exact ULift.up (if (⋂ r ∈ F, K r).Nonempty then true else false)

private theorem finset_iInter_nonempty_of_homogeneous_aux [IsFiniteMeasure μ]
    {R : Type u} {Q : Set R} [Uncountable Q] (K : R → Set X)
    (hKmeas : ∀ r, MeasurableSet (K r)) (hKpos : ∀ r, 0 < μ (K r))
    (hhom : ∀ m, ∃ c, ∀ F : Finset R, (F : Set R) ⊆ Q → F.card = m →
      compactIntersectionColor K F = c)
    {F : Finset R} (hFQ : (F : Set R) ⊆ Q) (hFpos : 0 < F.card) :
    (⋂ r ∈ F, K r).Nonempty := by
  classical
  obtain ⟨c, hc⟩ := hhom F.card
  obtain ⟨G, hGcard, hGnonempty⟩ := Measure.exists_finset_iInter_nonempty_of_uncountable
    (fun q : Q ↦ K q.1) (fun q ↦ hKmeas q.1) (fun q ↦ hKpos q.1) hFpos
  let G' : Finset R := G.image ((↑) : Q → R)
  have hG'card : G'.card = F.card := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hGcard]
  have hG'Q : (G' : Set R) ⊆ Q := by
    rintro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    exact q.2
  have hG'nonempty : (⋂ r ∈ G', K r).Nonempty := by
    obtain ⟨x, hx⟩ := hGnonempty
    refine ⟨x, mem_iInter₂.2 fun r hr ↦ ?_⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hr
    exact mem_iInter₂.1 hx q hq
  by_contra hF
  have hfalse : compactIntersectionColor K F = ULift.up false := by
    simp only [compactIntersectionColor, if_neg hF]
  have htrue : compactIntersectionColor K G' = ULift.up true := by
    simp only [compactIntersectionColor, if_pos hG'nonempty]
  exact Bool.false_ne_true (congrArg ULift.down <| hfalse.symm.trans <|
    (hc F hFQ rfl).trans ((hc G' hG'Q hG'card).symm.trans htrue))

private theorem exists_large_compact_fip_aux [IsFiniteMeasure μ] {R : Type u}
    (U : Ultrafilter R) (hfree : (U : Filter R) ≤ Filter.cofinite)
    [CardinalInterFilter (U : Filter R) (Cardinal.mk R)] (hR : ℵ₀ < Cardinal.mk R)
    (K : R → Set X) (hKmeas : ∀ r, MeasurableSet (K r)) (hKpos : ∀ r, 0 < μ (K r)) :
    ∃ Q : Set R, Cardinal.mk Q = Cardinal.mk R ∧
      ∀ F : Finset Q, (⋂ q ∈ F, K q.1).Nonempty := by
  classical
  have hBool : Cardinal.mk (ULift.{u} Bool) < Cardinal.mk R :=
    (by simp : Cardinal.mk (ULift.{u} Bool) < ℵ₀).trans hR
  obtain ⟨Q, hQcard, hhom⟩ :=
    ultrafilter_exists_cardinal_homogeneous_set U hfree hR hBool
      (compactIntersectionColor K)
  have hQuncount : Uncountable Q := Cardinal.aleph0_lt_mk_iff.1 (by simpa [hQcard] using hR)
  letI : Uncountable Q := hQuncount
  refine ⟨Q, hQcard, fun F ↦ ?_⟩
  by_cases hF : F = ∅
  · let q : Q := Classical.choice (inferInstance : Nonempty Q)
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (hKpos q).ne'
    exact ⟨x, by simp [hF]⟩
  · let F' : Finset R := F.image ((↑) : Q → R)
    have hF'Q : (F' : Set R) ⊆ Q := by
      rintro r hr
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
      exact q.2
    have hF'pos : 0 < F'.card := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact F.card_pos.mpr (Finset.nonempty_iff_ne_empty.2 hF)
    obtain ⟨x, hx⟩ :=
      finset_iInter_nonempty_of_homogeneous_aux K hKmeas hKpos hhom hF'Q hF'pos
    refine ⟨x, mem_iInter₂.2 fun q hq ↦ ?_⟩
    exact mem_iInter₂.1 hx q.1 (Finset.mem_image.2 ⟨q, hq, rfl⟩)

omit [MeasurableSpace X] in
private theorem iInter_nonempty_of_compact_fip_aux [TopologicalSpace X] [T2Space X] {R : Type*}
    {Q : Set R} (hQ : Q.Nonempty) (K : R → Set X) (hKcompact : ∀ r, IsCompact (K r))
    (hfinite : ∀ F : Finset Q, (⋂ q ∈ F, K q.1).Nonempty) :
    (⋂ q : Q, K q.1).Nonempty := by
  classical
  obtain ⟨q₀, hq₀⟩ := hQ
  obtain ⟨x, -, hx⟩ := (hKcompact q₀).inter_iInter_nonempty (fun q : Q ↦ K q.1)
    (fun q ↦ (hKcompact q.1).isClosed) fun F ↦ by
      obtain ⟨x, hx⟩ := hfinite (insert ⟨q₀, hq₀⟩ F)
      refine ⟨x, mem_iInter₂.1 hx _ (Finset.mem_insert_self _ _),
        mem_iInter₂.2 fun q hq ↦ ?_⟩
      exact mem_iInter₂.1 hx q (Finset.mem_insert_of_mem hq)
  exact ⟨x, hx⟩

private theorem exists_lt_mem_of_cardinalMk_eq_aux {R : Type u} [LinearOrder R]
    [WellFoundedLT R] (hord : Cardinal.ord (Cardinal.mk R) =
      Ordinal.type ((· < ·) : R → R → Prop)) (hR : ℵ₀ ≤ Cardinal.mk R)
    {Q : Set R} (hQcard : Cardinal.mk Q = Cardinal.mk R) (r : R) : ∃ q : Q, r < q.1 := by
  by_contra h
  push Not at h
  have hle := Cardinal.mk_le_mk_of_subset (show Q ⊆ Iic r from fun q hq ↦ h ⟨q, hq⟩)
  rw [hQcard] at hle
  exact (not_le_of_gt (Cardinal.mk_Iic_lt r hord hR)) hle

omit [MeasurableSpace X] in
private theorem not_mem_iInter_tailSource_aux {i R : Type u} [LinearOrder R]
    [WellFoundedLT R] (hord : Cardinal.ord (Cardinal.mk R) =
      Ordinal.type ((· < ·) : R → R → Prop)) (hR : ℵ₀ ≤ Cardinal.mk R)
    (A : i → Set X) (hA : Pairwise (Disjoint on A)) (M : R → Set i)
    (hMdisj : Pairwise (Disjoint on M)) {Q : Set R} [Nonempty Q]
    (hQcard : Cardinal.mk Q = Cardinal.mk R) (K : R → Set X)
    (hKsub : ∀ r, K r ⊆ ⋃ j ∈ (⋃ q ∈ Ici r, M q), A j) {x : X}
    (hxall : x ∈ ⋂ q : Q, K q.1) : False := by
  let q₀ : Q := Classical.choice (inferInstance : Nonempty Q)
  have hx₀ := hKsub q₀ (mem_iInter.1 hxall q₀)
  obtain ⟨i₀, hi₀tail, hxi₀⟩ := mem_iUnion₂.1 hx₀
  obtain ⟨r, -, hi₀r⟩ := mem_iUnion₂.1 hi₀tail
  obtain ⟨q, hrq⟩ := exists_lt_mem_of_cardinalMk_eq_aux hord hR hQcard r
  have hxq := hKsub q.1 (mem_iInter.1 hxall q)
  obtain ⟨j, hjtail, hxj⟩ := mem_iUnion₂.1 hxq
  obtain ⟨t, hqt, hjt⟩ := mem_iUnion₂.1 hjtail
  have hij : i₀ = j := by
    by_contra hij
    exact Set.disjoint_left.1 (hA hij) hxi₀ hxj
  subst j
  have hrt : r = t := by
    by_contra hrt
    exact Set.disjoint_left.1 (hMdisj hrt) hi₀r hjt
  exact (not_lt_of_ge (hrt ▸ hqt)) hrq

private theorem Measure.measure_iUnion_eq_zero_of_pairwiseDisjoint_of_atom_aux
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] {i : Type u} (A : i → Set X)
    (hA : Pairwise (Disjoint on A)) (hnull : ∀ j, μ (A j) = 0)
    (hAmeas : ∀ s : Set i, MeasurableSet (⋃ j ∈ s, A j))
    (hatom : letI : MeasurableSpace i := ⊤
      let nu := μ.inducedIndexMeasure A hA hAmeas
      ∃ s : Set i, 0 < nu s ∧ ∀ t ⊆ s, nu t = 0 ∨ nu (s \ t) = 0) :
    μ (⋃ j, A j) = 0 := by
  classical
  letI : MeasurableSpace i := ⊤
  have hall (s : Set i) : MeasurableSet s := MeasurableSet.of_discrete
  let nu := μ.inducedIndexMeasure A hA hAmeas
  letI : IsFiniteMeasure nu := IsFiniteMeasure.mk <| by
    change μ.inducedIndexMeasure A hA hAmeas univ < ∞
    rw [Measure.inducedIndexMeasure_apply hall]
    exact (measure_mono (subset_univ _)).trans_lt (measure_lt_top μ univ)
  obtain ⟨s, hs, hs_atom⟩ := hatom
  have hpoint (j : i) : nu {j} = 0 := by
    rw [Measure.inducedIndexMeasure_apply hall]
    simpa using hnull j
  obtain ⟨R, M, hMdisj, hMsub, hMnull, hMpos, hR, hsmall⟩ :=
    nu.exists_minimal_disjoint_null_cover_aux hpoint hs
  obtain ⟨U, hUfree, hUinter⟩ :=
    nu.exists_cardinalInterUltrafilter_aux hall hs_atom M hMdisj hMsub hMnull hMpos hsmall
  letI : CardinalInterFilter (U : Filter R) (Cardinal.mk R) := hUinter
  obtain ⟨order, wf, hord⟩ := Cardinal.exists_ord_eq_type_lt R
  letI : LinearOrder R := order
  letI : WellFoundedLT R := wf
  let tail : R → Set i := fun r ↦ ⋃ q ∈ Ici r, M q
  have htail_pos (r : R) : 0 < nu (tail r) :=
    nu.iUnion_Ici_pos_of_minimal_null_cover_aux M hMsub hMnull hMpos hsmall hord r
  let sourceTail : R → Set X := fun r ↦ ⋃ j ∈ tail r, A j
  have hsourceTail_meas (r : R) : MeasurableSet (sourceTail r) := hAmeas _
  have hsourceTail_pos (r : R) : 0 < μ (sourceTail r) := by
    rw [← Measure.inducedIndexMeasure_apply hall]
    exact htail_pos r
  choose K hKsub hKcompact hKpos using fun r : R ↦
    (hsourceTail_meas r).exists_lt_isCompact_of_ne_top (measure_ne_top μ _) (hsourceTail_pos r)
  have hKmeas (r : R) : MeasurableSet (K r) := (hKcompact r).isClosed.measurableSet
  obtain ⟨Q, hQcard, hfinite_inter⟩ :=
    exists_large_compact_fip_aux U hUfree hR K hKmeas hKpos
  have hQuncount : Uncountable Q := Cardinal.aleph0_lt_mk_iff.1 (by simpa [hQcard] using hR)
  letI : Uncountable Q := hQuncount
  have hQ_nonempty : Q.Nonempty := by
    let q : Q := Classical.choice (inferInstance : Nonempty Q)
    exact ⟨q, q.2⟩
  obtain ⟨x, hxall⟩ := iInter_nonempty_of_compact_fip_aux hQ_nonempty K hKcompact hfinite_inter
  have hKsub' (r : R) : K r ⊆ ⋃ j ∈ (⋃ q ∈ Ici r, M q), A j := by
    simpa only [sourceTail, tail] using hKsub r
  exact (not_mem_iInter_tailSource_aux hord hR.le A hA M hMdisj hQcard K hKsub' hxall).elim

private theorem Measure.measure_iUnion_eq_zero_of_pairwiseDisjoint_of_lusin_aux
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] {i : Type u} (A : i → Set X)
    (hA : Pairwise (Disjoint on A)) (hnull : ∀ j, μ (A j) = 0)
    (hAmeas : ∀ s : Set i, MeasurableSet (⋃ j ∈ s, A j))
    (hLusin : ∀ (g : X → ℝ), Measurable g → ∀ U : Set X, MeasurableSet U → 0 < μ U →
      ∃ K ⊆ U, IsCompact K ∧ ContinuousOn g K ∧ 0 < μ K) :
    μ (⋃ j, A j) = 0 := by
  letI : MeasurableSpace i := ⊤
  let nu := μ.inducedIndexMeasure A hA hAmeas
  rcases nu.splits_or_exists_atom_aux with hsplit | hatom
  · exact μ.measure_iUnion_eq_zero_of_pairwiseDisjoint_of_splits_aux A hA hAmeas hLusin hsplit
  · exact μ.measure_iUnion_eq_zero_of_pairwiseDisjoint_of_atom_aux A hA hnull hAmeas hatom

/-- An arbitrary union of a pairwise disjoint family of null sets is null if every subunion is
measurable and the finite measure is compact-inner-regular. -/
theorem Measure.measure_iUnion_eq_zero_of_pairwiseDisjoint
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] {i : Type u} (A : i → Set X)
    (hA : Pairwise (Disjoint on A)) (hnull : ∀ j, μ (A j) = 0)
    (hAmeas : ∀ s : Set i, MeasurableSet (⋃ j ∈ s, A j)) :
    μ (⋃ j, A j) = 0 := by
  apply μ.measure_iUnion_eq_zero_of_pairwiseDisjoint_of_lusin_aux A hA hnull hAmeas
  intro g hg U hUmeas hUpos
  obtain ⟨K, hKU, hKcompact, hgK, hUK⟩ :=
    Measurable.exists_isCompact_continuousOn μ hg hUmeas (measure_ne_top μ U) hUpos
  refine ⟨K, hKU, hKcompact, hgK, ?_⟩
  rw [pos_iff_ne_zero]
  intro hKzero
  rw [measure_sdiff_null hKzero] at hUK
  exact hUK.false

/-- The measure of an arbitrary measurable union of pairwise disjoint sets is the sum of their
measures for a finite compact-inner-regular measure. -/
theorem Measure.measure_iUnion_eq_tsum_of_pairwiseDisjoint
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] {i : Type u} (s : i → Set X)
    (hdisj : Pairwise (Disjoint on s))
    (hmeas : ∀ I : Set i, MeasurableSet (⋃ j ∈ I, s j)) :
    μ (⋃ j, s j) = ∑' j, μ (s j) := by
  refine μ.measure_iUnion_eq_tsum_of_pairwiseDisjoint_of_null s hdisj hmeas ?_
  let i₀ := {j | μ (s j) = 0}
  refine μ.measure_iUnion_eq_zero_of_pairwiseDisjoint (fun j : i₀ ↦ s j)
    (fun j k hjk ↦ hdisj fun hjk' ↦ hjk (Subtype.ext hjk')) (fun j ↦ j.2) ?_
  intro I
  convert hmeas ((↑) '' I) using 1
  ext x
  simp only [mem_iUnion, mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  aesop

omit [PseudoMetrizableSpace Y] in
private theorem measure_preimage_iUnion_null_of_discreteFamily_aux [SFinite μ]
    (hf : Measurable f) {b : Set (Set Y)} (hb_open : ∀ U ∈ b, IsOpen U)
    (hb_discrete : DiscreteFamily ((↑) : b → Set Y))
    (hnull : ∀ (s : Set Y → Set X), Pairwise (Disjoint on s) →
      (∀ i, μ (s i) = 0) → (∀ I : Set (Set Y), MeasurableSet (⋃ i ∈ I, s i)) →
      μ (⋃ i, s i) = 0) :
    μ (f ⁻¹' ⋃ U : {U : b | μ (f ⁻¹' (U : Set Y)) = 0}, (U : Set Y)) = 0 := by
  classical
  let q : Set (Set Y) := {U | U ∈ b ∧ μ (f ⁻¹' U) = 0}
  let A : Set Y → Set X := fun U ↦ if U ∈ q then f ⁻¹' U else ∅
  have hA_disj : Pairwise (Disjoint on A) := by
    intro U V hUV
    change Disjoint (A U) (A V)
    by_cases hU : U ∈ q
    · by_cases hV : V ∈ q
      · rw [show A U = f ⁻¹' U by simp [A, hU], show A V = f ⁻¹' V by simp [A, hV]]
        apply Disjoint.preimage f
        have hne : (⟨U, hU.1⟩ : b) ≠ ⟨V, hV.1⟩ := by
          intro h
          exact hUV (congrArg Subtype.val h)
        exact hb_discrete.pairwiseDisjoint hne
      · simp [A, hV]
    · simp [A, hU]
  have hA_null (U : Set Y) : μ (A U) = 0 := by
    by_cases hU : U ∈ q
    · simpa [A, hU] using hU.2
    · simp [A, hU]
  have hA_union (I : Set (Set Y)) : MeasurableSet (⋃ U ∈ I, A U) := by
    have hopen (U : Set Y) : IsOpen (if U ∈ q then U else ∅) := by
      by_cases hU : U ∈ q
      · simpa [hU] using hb_open U hU.1
      · simp [hU]
    rw [show (⋃ U ∈ I, A U) = f ⁻¹' ⋃ U ∈ I, if U ∈ q then U else ∅ by
      ext x
      simp [A]]
    exact hf (isOpen_iUnion fun U ↦ isOpen_iUnion fun _ ↦ hopen U).measurableSet
  rw [show f ⁻¹' ⋃ U : {U : b | μ (f ⁻¹' (U : Set Y)) = 0}, (U : Set Y) =
      ⋃ U, A U by
    ext x
    constructor
    · intro hx
      change f x ∈ ⋃ U : {U : b | μ (f ⁻¹' (U : Set Y)) = 0}, (U : Set Y) at hx
      obtain ⟨U, hxU⟩ := mem_iUnion.1 hx
      apply mem_iUnion.2
      refine ⟨(U : Set Y), ?_⟩
      have hUq : (U : Set Y) ∈ q := ⟨U.1.2, U.2⟩
      simpa [A, hUq] using hxU
    · intro hx
      obtain ⟨U, hxU⟩ := mem_iUnion.1 hx
      by_cases hU : U ∈ q
      · change f x ∈ ⋃ U : {U : b | μ (f ⁻¹' (U : Set Y)) = 0}, (U : Set Y)
        exact mem_iUnion_of_mem ⟨⟨U, hU.1⟩, hU.2⟩ (by simpa [A, hU] using hxU)
      · exfalso
        simp [A, hU] at hxU]
  exact hnull A hA_disj hA_null hA_union

omit [PseudoMetrizableSpace Y] in
private theorem countable_setOf_pos_preimage_of_sigmaDiscreteFamily_aux [SFinite μ]
    (hf : Measurable f) (b : ℕ → Set (Set Y))
    (hb_open : ∀ {n : ℕ} (U : b n), IsOpen (U : Set Y))
    (hb_discrete : ∀ n, DiscreteFamily ((↑) : b n → Set Y)) :
    {U | ∃ n, U ∈ b n ∧ 0 < μ (f ⁻¹' U)}.Countable := by
  have hn_count (n : ℕ) : Set.Countable {U : b n | 0 < μ (f ⁻¹' (U : Set Y))} :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun U ↦ hf (hb_open U).measurableSet)
      (fun U V hUV ↦ Disjoint.preimage f ((hb_discrete n).pairwiseDisjoint hUV))
  rw [show {U | ∃ n, U ∈ b n ∧ 0 < μ (f ⁻¹' U)} =
      ⋃ n, ((↑) : b n → Set Y) '' {U | 0 < μ (f ⁻¹' (U : Set Y))} by
    ext U
    simp only [mem_setOf_eq, mem_iUnion, mem_image, Subtype.exists, exists_and_left]
    aesop]
  exact countable_iUnion fun n ↦ (hn_count n).image _

omit [TopologicalSpace Y] [PseudoMetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
private theorem countable_induced_basis_compl_aux (b : ℕ → Set (Set Y)) (N : Set Y)
    (hp_count : {U | ∃ n, U ∈ b n ∧ 0 < μ (f ⁻¹' U)}.Countable)
    (hnull_sub : ∀ n U, U ∈ b n → μ (f ⁻¹' U) = 0 → U ⊆ N) :
    (((preimage ((↑) : ↑(Nᶜ) → Y)) '' (⋃ n, b n)) : Set (Set ↑(Nᶜ))).Countable := by
  refine ((hp_count.image (preimage ((↑) : ↑(Nᶜ) → Y))).union
    (countable_singleton (∅ : Set ↑(Nᶜ)))).mono ?_
  rintro V ⟨U, hUb, rfl⟩
  obtain ⟨n, hUn⟩ := mem_iUnion.1 hUb
  by_cases hU_pos : 0 < μ (f ⁻¹' U)
  · exact Or.inl ⟨U, ⟨n, hUn, hU_pos⟩, rfl⟩
  · right
    rw [mem_singleton_iff]
    ext y
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    exact fun hyU ↦ y.2 (hnull_sub n U hUn (nonpos_iff_eq_zero.1 (not_lt.1 hU_pos)) hyU)

/-- A measurable map into a pseudometrizable Borel space has an almost everywhere closed separable
range, provided that arbitrary measurable unions of a disjoint family of null sets are null.

This isolates the topological part of the Kupka--Prikry theorem from its measure-theoretic core. -/
theorem Measurable.exists_isClosed_isSeparable_ae_mem_of_iUnion_null [SFinite μ]
    (hf : Measurable f)
    (hnull : ∀ (s : Set Y → Set X), Pairwise (Disjoint on s) →
      (∀ i, μ (s i) = 0) → (∀ I : Set (Set Y), MeasurableSet (⋃ i ∈ I, s i)) →
      μ (⋃ i, s i) = 0) :
    ∃ s : Set Y, IsClosed s ∧ IsSeparable s ∧ ∀ᵐ x ∂μ, f x ∈ s := by
  classical
  obtain ⟨b, hb, hdisc⟩ := exists_isTopologicalBasis_sigmaDiscrete (X := Y)
  let z : ℕ → Set Y := fun n ↦
    ⋃ U : {U : b n | μ (f ⁻¹' (U : Set Y)) = 0}, (U : Set Y)
  have hb_open {n : ℕ} (U : b n) : IsOpen (U : Set Y) :=
    hb.isOpen (mem_iUnion.2 ⟨n, U.2⟩)
  have hz_open (n : ℕ) : IsOpen (z n) := isOpen_iUnion fun U ↦ hb_open U.1
  have hz_null (n : ℕ) : μ (f ⁻¹' z n) = 0 := by
    simpa only [z] using measure_preimage_iUnion_null_of_discreteFamily_aux hf
      (fun U hU ↦ hb_open ⟨U, hU⟩) (hdisc n) hnull
  let N : Set Y := ⋃ n, z n
  have hN_open : IsOpen N := isOpen_iUnion hz_open
  have hN_null : μ (f ⁻¹' N) = 0 := by
    simpa only [N, preimage_iUnion] using measure_iUnion_null hz_null
  let p : Set (Set Y) :=
    {U | ∃ n, U ∈ b n ∧ 0 < μ (f ⁻¹' U)}
  have hp_count : p.Countable := by
    simpa only [p] using
      countable_setOf_pos_preimage_of_sigmaDiscreteFamily_aux hf b hb_open hdisc
  let Z : Set Y := Nᶜ
  have hZ_closed : IsClosed Z := hN_open.isClosed_compl
  have hZ_ae : ∀ᵐ x ∂μ, f x ∈ Z := by
    apply ae_iff.2
    change μ (f ⁻¹' Zᶜ) = 0
    simpa only [Z, compl_compl] using hN_null
  have hZ_basis : IsTopologicalBasis
      ((preimage ((↑) : Z → Y)) '' (⋃ n, b n)) := hb.induced _
  have hnull_sub (n : ℕ) (U : Set Y) (hUn : U ∈ b n) (hUnull : μ (f ⁻¹' U) = 0) :
      U ⊆ N := fun y hyU ↦ by
    apply mem_iUnion.2
    refine ⟨n, mem_iUnion.2 ?_⟩
    exact ⟨⟨⟨U, hUn⟩, hUnull⟩, hyU⟩
  have hZ_basis_count :
      (((preimage ((↑) : Z → Y)) '' (⋃ n, b n)) : Set (Set Z)).Countable :=
    countable_induced_basis_compl_aux b N hp_count hnull_sub
  letI : SecondCountableTopology Z := hZ_basis.secondCountableTopology hZ_basis_count
  exact ⟨Z, hZ_closed, IsSeparable.of_subtype Z, hZ_ae⟩

/-- An almost everywhere measurable map into a pseudometrizable Borel space has an almost
everywhere closed separable range, provided that arbitrary measurable unions of a disjoint family
of null sets are null. -/
theorem AEMeasurable.exists_isClosed_isSeparable_ae_mem_of_iUnion_null [SFinite μ]
    (hf : AEMeasurable f μ)
    (hnull : ∀ (s : Set Y → Set X), Pairwise (Disjoint on s) →
      (∀ i, μ (s i) = 0) → (∀ I : Set (Set Y), MeasurableSet (⋃ i ∈ I, s i)) →
      μ (⋃ i, s i) = 0) :
    ∃ s : Set Y, IsClosed s ∧ IsSeparable s ∧ ∀ᵐ x ∂μ, f x ∈ s := by
  obtain ⟨s, hs_closed, hs_sep, hs⟩ :=
    Measurable.exists_isClosed_isSeparable_ae_mem_of_iUnion_null hf.measurable_mk hnull
  refine ⟨s, hs_closed, hs_sep, ?_⟩
  filter_upwards [hf.ae_eq_mk, hs] with x hfx hx
  rwa [hfx]

/-- Under the uncountable null-union property, almost everywhere measurable maps into a
pseudometrizable Borel space are almost everywhere strongly measurable. -/
theorem AEMeasurable.aestronglyMeasurable_of_iUnion_null [SFinite μ]
    (hf : AEMeasurable f μ)
    (hnull : ∀ (s : Set Y → Set X), Pairwise (Disjoint on s) →
      (∀ i, μ (s i) = 0) → (∀ I : Set (Set Y), MeasurableSet (⋃ i ∈ I, s i)) →
      μ (⋃ i, s i) = 0) :
    AEStronglyMeasurable f μ := by
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨hf, ?_⟩
  obtain ⟨s, -, hs, hfs⟩ :=
    AEMeasurable.exists_isClosed_isSeparable_ae_mem_of_iUnion_null hf hnull
  exact ⟨s, hs, hfs⟩

/-- Under the uncountable null-union property, almost everywhere strong measurability is
equivalent to almost everywhere measurability for maps into pseudometrizable Borel spaces. -/
theorem aestronglyMeasurable_iff_aemeasurable_of_iUnion_null [SFinite μ]
    (hnull : ∀ (s : Set Y → Set X), Pairwise (Disjoint on s) →
      (∀ i, μ (s i) = 0) → (∀ I : Set (Set Y), MeasurableSet (⋃ i ∈ I, s i)) →
      μ (⋃ i, s i) = 0) :
    AEStronglyMeasurable f μ ↔ AEMeasurable f μ :=
  ⟨AEStronglyMeasurable.aemeasurable,
    fun hf ↦ AEMeasurable.aestronglyMeasurable_of_iUnion_null hf hnull⟩

/-- A measurable map into a pseudometrizable Borel space has an almost everywhere closed separable
range with respect to a finite compact-inner-regular measure. -/
theorem Measurable.exists_isClosed_isSeparable_ae_mem
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] (hf : Measurable f) :
    ∃ s : Set Y, IsClosed s ∧ IsSeparable s ∧ ∀ᵐ x ∂μ, f x ∈ s :=
  Measurable.exists_isClosed_isSeparable_ae_mem_of_iUnion_null hf fun s hdisj hnull hmeas ↦
    μ.measure_iUnion_eq_zero_of_pairwiseDisjoint s hdisj hnull hmeas

/-- An almost everywhere measurable map into a pseudometrizable Borel space has an almost
everywhere closed separable range with respect to a finite compact-inner-regular measure. -/
theorem AEMeasurable.exists_isClosed_isSeparable_ae_mem
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] (hf : AEMeasurable f μ) :
    ∃ s : Set Y, IsClosed s ∧ IsSeparable s ∧ ∀ᵐ x ∂μ, f x ∈ s :=
  AEMeasurable.exists_isClosed_isSeparable_ae_mem_of_iUnion_null hf fun s hdisj hnull hmeas ↦
    μ.measure_iUnion_eq_zero_of_pairwiseDisjoint s hdisj hnull hmeas

/-- Almost everywhere measurable maps into pseudometrizable Borel spaces are almost everywhere
strongly measurable with respect to finite compact-inner-regular measures. -/
theorem AEMeasurable.aestronglyMeasurable_of_innerRegular
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] (hf : AEMeasurable f μ) :
    AEStronglyMeasurable f μ := by
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨hf, ?_⟩
  obtain ⟨s, -, hs, hfs⟩ := AEMeasurable.exists_isClosed_isSeparable_ae_mem hf
  exact ⟨s, hs, hfs⟩

/-- Almost everywhere strong measurability and almost everywhere measurability agree for maps into
pseudometrizable Borel spaces with respect to finite compact-inner-regular measures. -/
theorem aestronglyMeasurable_iff_aemeasurable_of_innerRegular
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] :
    AEStronglyMeasurable f μ ↔ AEMeasurable f μ :=
  ⟨AEStronglyMeasurable.aemeasurable,
    AEMeasurable.aestronglyMeasurable_of_innerRegular⟩

end MeasureTheory
