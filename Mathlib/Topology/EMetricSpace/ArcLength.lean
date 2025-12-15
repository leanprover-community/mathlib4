/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Success Moses
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Data.Set.Operations

/-!
# Arc length

This file is devoted to the definition of the `arcLength` of a function `f` between
`a` and `b` and the continuity of the single variable function `arcLength a` or
`(arcLength · b)`.

## Tags

Topology, Metric space, Continuity
-/

@[expose] public section

open ENNReal

variable {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E] (f : α → E) {a b c : α}

/-- The length of the arc of the curve `f : α → E` between two points `a` and `b` is defined
as the variation of `f` on the closed interval `[a, b]`. Equals zero when `b ≤ a`. -/
noncomputable def arcLength (a b : α) : ℝ≥0∞ :=
  eVariationOn f (Set.Icc a b)

theorem arcLength_eq : arcLength f a b = eVariationOn f (Set.Icc a b) := rfl

theorem arcLength_ne_iff : (arcLength f a b ≠ ∞) ↔ BoundedVariationOn f (Set.Icc a b) := .rfl

/-- `arcLength f a b` is the supremum of finite sums of `edist (f <| u i) (f <| u <| i+1)` for `u`
satisfying the same conditions as for `eVariationOn` with the addition of:
* `u 0` is `a`.
* `u 1` is **not** `a`. -/
theorem arcLength_eq_iSup (hab : a ≤ b) : arcLength f a b =
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ (∀ i, u i ∈ Set.Icc a b) ∧ u 0 = a ∧ a < u 1},
    ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, hu, huab⟩
    by_cases h : ∀ m ≤ n, u m = a
    · have : ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        simp only [Finset.mem_range] at hi
        rw [h i (by linarith), h (i + 1) (by linarith), edist_self]
      rw [this]; apply zero_le
    push_neg at h
    obtain ⟨m, ⟨hmn, hma⟩, hmin⟩ := WellFounded.has_min wellFounded_lt {m | m ≤ n ∧ u m ≠ a} h
    push_neg at hmin
    cases m with
    | zero =>
      refine le_iSup_of_le ⟨n + 1, Nat.rec a (fun k _ ↦ u k),
        fun k ↦ ?_, fun k ↦ ?_, rfl, (huab 0).1.lt_of_ne' hma⟩ ?_
      · apply monotone_nat_of_le_succ
        intro n; cases n;
        · exact (huab 0).1
        · exact hu (Nat.le_succ _)
      · cases k
        · exact Set.left_mem_Icc.mpr hab
        · exact huab _
      · rw [Finset.sum_range_succ']; exact self_le_add_right _ _
    | succ m =>
      have : ∀ k ≤ m, u k = a := by
        intro k hk; contrapose! hmin
        exact ⟨_, ⟨hk.trans (m.le_succ.trans hmn), hmin⟩, hk.trans_lt m.lt_succ_self⟩
      refine le_iSup_of_le ?_ ?_
      · refine ⟨n - m, ⟨fun k ↦ u (m + k), ⟨?_, ?_⟩⟩⟩
        · exact Monotone.comp hu (fun {k₁ k₂} hk ↦ Nat.add_le_add_left hk m)
        · exact ⟨fun k ↦ huab _, this m le_rfl, (huab _).1.lt_of_ne' hma⟩
      · dsimp only [Subtype.coe_mk]
        conv =>
          lhs; rw [← Nat.sub_add_cancel (m.le_succ.trans hmn), add_comm, Finset.sum_range_add]
        simp_rw [add_assoc]
        have : ∑ x ∈ Finset.range m, edist (f (u (x + 1))) (f (u x)) = 0 := by
          apply Finset.sum_eq_zero; intro i hi
          simp only [Finset.mem_range] at hi
          rw [this i (by linarith), this (i+1) (by linarith), edist_self]
        rw [this, zero_add]
  · apply iSup_le
    intro p; rw [arcLength]
    let p' : ℕ × { u // Monotone u ∧ ∀ i, u i ∈ Set.Icc a b } :=
      ⟨p.1, ⟨p.2.val, ⟨p.2.property.1, p.2.property.2.1⟩⟩⟩
    exact le_iSup (fun p ↦ ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))) p'

theorem edist_le_arcLength (hab : a ≤ b) : edist (f a) (f b) ≤ arcLength f a b := by
  refine eVariationOn.edist_le f ?_ ?_ <;> simp [hab]

/-- The length of a function over a singleton is zero. -/
theorem arcLength_eq_zero (hab : b ≤ a) : arcLength f a b = 0 :=
  eVariationOn.subsingleton f <| by simp [hab]

theorem arcLength_self (a : α) : arcLength f a a = 0 := arcLength_eq_zero _ le_rfl

theorem arcLength_anti (c : α) : Antitone (arcLength f · c) :=
  fun _a _b hab ↦ eVariationOn.mono _ fun _x ⟨hbx, hxc⟩ ↦ ⟨hab.trans hbx, hxc⟩

theorem arcLength_mono (a : α) : Monotone (arcLength f a) :=
  fun _x _y hxy ↦ eVariationOn.mono _ fun _z ⟨haz, hzx⟩ ↦ ⟨haz, hzx.trans hxy⟩

theorem arcLength_add (hab : a ≤ b) (hbc : b ≤ c) :
    arcLength f a b + arcLength f b c = arcLength f a c := by
  simp_rw [arcLength]
  convert eVariationOn.Icc_add_Icc f (s := Set.univ) hab hbc (by simp) <;> simp

theorem arcLength_sum {n : ℕ} {u : ℕ → α} (hu : Monotone u) :
    ∑ i ∈ Finset.range n, arcLength f (u i) (u (i + 1)) = arcLength f (u 0) (u n) := by
  induction n with
  | zero => rw [arcLength_self, Finset.sum_range_zero]
  | succ k ih => rw [Finset.sum_range_succ, ih, arcLength_add f (hu <| zero_le k) (hu k.le_succ)]

theorem arcLength_sub₀ (hba : b ≤ a) : arcLength f a b = arcLength f a c - arcLength f b c := by
  rw [arcLength_eq_zero f hba, eq_comm]
  exact tsub_eq_zero_of_le (arcLength_anti f c hba)

theorem arcLength_sub' (hbc : b ≤ c) (hac : arcLength f b c ≠ ∞) :
    arcLength f a b = arcLength f a c - arcLength f b c := by
  rcases le_total a b with (hab | hba)
  · exact ENNReal.eq_sub_of_add_eq hac (arcLength_add f hab hbc)
  · exact arcLength_sub₀ f hba

theorem arcLength_sub (hbc : b ≤ c) (hac : arcLength f a c ≠ ∞) :
    arcLength f a b = arcLength f a c - arcLength f b c := by
  rcases le_total a b with (hab | hba)
  · exact arcLength_sub' f hbc <| ne_top_of_le_ne_top hac <| arcLength_anti f c hab
  · exact arcLength_sub₀ f hba

open OrderDual

@[simp]
theorem arcLength_comp_ofDual :
    arcLength (f ∘ ofDual) (toDual b) (toDual a) = arcLength f a b := by
  have : Set.Icc (toDual b) (toDual a) = ofDual ⁻¹' (Set.Icc a b) := by simp
  simp_rw [arcLength, this, eVariationOn.comp_ofDual]

theorem arcLength_left_eq :
    (arcLength f · b) = arcLength (f ∘ ofDual) (toDual b) ∘ toDual := by
  ext; simp

theorem arcLength_right_eq :
    arcLength f a = (arcLength (f ∘ ofDual) · (toDual a)) ∘ toDual := by
  ext; simp

theorem arcLength_Icc_extend (h : a ≤ b) (f : Set.Icc a b → E) :
    arcLength (Set.IccExtend h f) a b = eVariationOn f Set.univ :=
  (eVariationOn.comp_eq_of_monotoneOn _ _ ((Set.monotone_projIcc h).monotoneOn _)).trans <| by
    rw [(Set.projIcc_surjOn h).image_eq_of_mapsTo (Set.mapsTo_univ ..)]

section

/-! ### Continuity (in various forms) "around" a point -/

variable [TopologicalSpace α]

theorem continuousOn_Iic_arcLength_of_ge (h : b ≤ a) :
    ContinuousOn (arcLength f a) (Set.Iic b) :=
  continuousOn_const.congr fun _x hx ↦ arcLength_eq_zero _ (trans hx h)

theorem continuousOn_Ici_arcLength_of_ge (h : b ≤ a) :
    ContinuousOn (arcLength f · b) (Set.Ici a) :=
  continuousOn_const.congr fun _x hx ↦ arcLength_eq_zero _ (trans h hx)

variable [OrderTopology α]

theorem continuousAt_arcLength_right (h : b < a) : ContinuousAt (arcLength f a) b :=
  continuousAt_const.congr <| Filter.eventuallyEq_of_mem (Iio_mem_nhds h)
    fun x hx ↦ (arcLength_eq_zero _ (le_of_lt <| by simpa)).symm

theorem continuousAt_arcLength_left (h : b < a) : ContinuousAt (arcLength f · b) a :=
  continuousAt_const.congr <| Filter.eventuallyEq_of_mem (Ioi_mem_nhds h)
    fun x hx ↦ (arcLength_eq_zero _ (le_of_lt <| by simpa)).symm

variable (hab : a < b) (hrect : BoundedVariationOn f (Set.Icc a b)) /- f is rectifiable on [a,b] -/
include hab hrect

theorem continuous_right_self_arcLength
    (cont : ContinuousWithinAt f (Set.Ico a b) a) /- f is right continuous at a -/ :
    ContinuousWithinAt (arcLength f a) (Set.Ici a) a := by
  replace cont : ContinuousWithinAt f (Set.Ici a) a :=
    cont.mono_of_mem_nhdsWithin (mem_nhdsWithin.mpr ⟨_, isOpen_Iio, hab, fun _ ↦ .symm⟩)
  rw [ContinuousWithinAt, arcLength_self, ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hlab : arcLength f a b = 0
  · rw [eventually_nhdsWithin_iff]
    refine Filter.eventually_of_mem (Iio_mem_nhds hab) (fun x hb ha ↦ ?_)
    exact ((arcLength_mono f a hb.le).trans_eq hlab).trans (zero_le ε)
  · have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    rw [← arcLength_ne_iff, arcLength_eq_iSup] at hrect <;> try exact hab.le
    rw [arcLength_eq_iSup] at hlab <;> try exact hab.le
    obtain ⟨⟨n, u, hu, hmem, hea, hal⟩, hl⟩ :=
      lt_iSup_iff.1 (ENNReal.sub_lt_self hrect hlab hε2.ne')
    simp_rw [← arcLength_eq_iSup f hab.le, edist_comm] at hl
    obtain ⟨c, hc, hcb⟩ := (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hab).1
      ((EMetric.nhds_basis_eball.tendsto_right_iff).1 cont _ hε2)
    apply (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hab).2
    by_cases h : ∀ x, ¬ x ∈ Set.Ioo a c
    · refine ⟨c, hc, fun x hx ↦ ?_⟩
      obtain rfl | hxa := eq_or_ne a x
      exacts [(arcLength_self f a).trans_le (zero_le ε), (h x ⟨hx.1.lt_of_ne hxa, hx.2⟩).elim]
    push_neg at h; obtain ⟨d, hd⟩ := h
    let e := min (u 1) d
    have hae : a < e := lt_min hal hd.1
    have hec : e < c := (min_le_right _ d).trans_lt hd.2
    refine ⟨e, ⟨hae, hec.le.trans hc.2⟩, fun x hx ↦ (arcLength_mono f a hx.2.le).trans ?_⟩
    obtain rfl | hε := eq_or_ne ε ∞
    · exact le_top
    have : ε / 2 ≠ ∞ := fun h ↦ (ENNReal.div_eq_top.1 h).elim (two_ne_zero ·.2) (hε ·.1)
    by_contra hac
    apply (Eq.refl <| arcLength f a b).not_lt
    calc arcLength f a b
      _ ≤ arcLength f a b - ε/2 + ε/2 := by apply tsub_le_iff_right.mp; exact le_rfl
      _ < ∑ i ∈ Finset.range (n+1), edist (f <| u i) (f <| u (i+1)) + ε/2 := by
        rw [ENNReal.add_lt_add_iff_right this, Finset.sum_range_succ]
        calc arcLength f a b - ε/2
          _ < ∑ x ∈ Finset.range n, edist (f (u x)) (f (u (x + 1))) := by exact hl
          _ ≤ _ := by refine le_add_of_nonneg_right (by simp)
      _ ≤ ∑ i ∈ Finset.range n, edist (f <| u (i+1)) (f <| u (i+1+1)) +
          (edist (f e) (f a) + edist (f e) (f <| u 1)) + ε/2  := by
        refine add_le_add_left ?_ (ε/2)
        rw [Finset.sum_range_succ', hea]
        apply add_le_add_right (edist_triangle_left ..) _
      _ ≤ ∑ i ∈ Finset.range n, arcLength f (u <| i+1) (u <| i+1+1) +
        (ε/2 + arcLength f e (u 1)) + ε/2 := by
          apply add_le_add_left
          apply add_le_add
          · apply Finset.sum_le_sum fun i hi ↦ edist_le_arcLength f <| hu (i+1).le_succ
          apply add_le_add (hcb ⟨hae.le, hec⟩).le (edist_le_arcLength f <| min_le_left _ d)
      _ = _ + (ε + arcLength f e (u 1)) := by rw [add_assoc, add_right_comm, ENNReal.add_halves]
      _ ≤ _ + arcLength f (u 0) (u 1) := by
        rw [hea, ← arcLength_add f hae.le <| min_le_left _ d, add_comm ε]
        rw [← add_comm (arcLength ..), ← add_assoc _ _ ε, ← add_assoc _ (arcLength ..)]
        refine add_le_add_right ?_ _
        push_neg at hac; exact hac.le
      _ = ∑ i ∈ Finset.range (n+1), arcLength f (u i) (u <| i+1) := by rw [Finset.sum_range_succ']
      _ = arcLength f (u 0) (u <| n+1) := arcLength_sum f hu
      _ ≤ arcLength f a b := hea ▸ arcLength_mono f a (hmem _).2

theorem continuous_right_arcLength_right
    (cont : ContinuousWithinAt f (Set.Ico a b) a) /- f is right continuous at a -/ :
    ContinuousWithinAt (arcLength f c) (Set.Ici a) a := by
  by_cases hca : c ≤ a
  · refine ((continuous_add_left _).continuousAt.comp_continuousWithinAt <|
      continuous_right_self_arcLength f hab hrect cont).congr
        (fun x hx ↦ (arcLength_add f hca hx).symm) (arcLength_add f hca le_rfl).symm
  apply ContinuousAt.continuousWithinAt
  exact ContinuousAt.congr_of_eventuallyEq (continuous_const.continuousAt) <|
    Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds (lt_of_not_ge hca))
      fun x hx ↦ arcLength_eq_zero f hx.le

theorem continuous_left_arcLength_left
    (cont : ContinuousWithinAt f (Set.Ioc a b) b) /- f is left continuous at b -/ :
    ContinuousWithinAt (arcLength f · c) (Set.Iic b) b := by
  rw [← arcLength_ne_iff, ← arcLength_comp_ofDual] at hrect; rw [arcLength_left_eq]
  refine ContinuousWithinAt.comp (t := Set.Ici (toDual b)) ?_ ?_ fun x hx ↦ ?_
  · exact continuous_right_arcLength_right (f ∘ ofDual) (by simpa) hrect (by simpa)
  · exact continuous_toDual.continuousWithinAt
  · simpa only [toDual_lt_toDual, Set.mem_Iic] using hx

omit hab

theorem continuous_left_arcLength_right
    (cont : ContinuousWithinAt f (Set.Ioc a b) b) /- f is left continuous at b -/ :
    ContinuousWithinAt (arcLength f a) (Set.Iic b) b := by
  obtain hba | hab := le_or_gt b a
  · apply (Continuous.continuousWithinAt continuous_const).congr (fun x hx ↦ _)
    · exact arcLength_eq_zero f hba
    · intro x hx; exact arcLength_eq_zero f <| trans hx hba
  · refine (((ENNReal.continuousOn_sub_left _).continuousAt ?_).comp_continuousWithinAt <|
      continuous_left_arcLength_left f hab hrect cont).congr (fun x hx ↦ arcLength_sub f hx hrect)
        (arcLength_sub f le_rfl hrect)
    rw [arcLength_self]; exact isOpen_ne.mem_nhds ENNReal.top_ne_zero.symm

theorem continuous_right_arcLength_left
    (cont : ContinuousWithinAt f (Set.Ico a b) a) /- f is right continuous at a -/ :
    ContinuousWithinAt (arcLength f · b) (Set.Ici a) a := by
  rw [←arcLength_ne_iff, ← arcLength_comp_ofDual] at hrect; rw [arcLength_left_eq]
  exact (continuous_left_arcLength_right (f ∘ ofDual) hrect <| by simpa).comp
    continuous_toDual.continuousWithinAt fun x ↦ id

theorem continuousOn_Iic_arcLength_right (cont : ContinuousOn f (Set.Icc a b)) :
    ContinuousOn (arcLength f a) (Set.Iic b) := by
  intro x hx; obtain hba | hab := le_or_gt b a
  · exact continuousOn_Iic_arcLength_of_ge _ hba _ hx
  obtain rfl | hxb := eq_or_lt_of_le hx
  · exact continuous_left_arcLength_right f hrect
      ((cont x ⟨hab.le, hx⟩).mono fun y h ↦ ⟨h.1.le, h.2⟩)
  refine (lt_or_ge x a).elim (fun hxa ↦ ((continuousOn_Iic_arcLength_of_ge f le_rfl).continuousAt
    <| Iic_mem_nhds hxa).continuousWithinAt)
    fun hax ↦ (continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩).continuousWithinAt
  · apply continuous_left_arcLength_right f (ne_top_of_le_ne_top hrect <| arcLength_mono f a hx)
    exact (cont x ⟨hax, hx⟩).mono fun y hy ↦ ⟨hy.1.le, hy.2.trans hx⟩
  · apply continuous_right_arcLength_right f hxb
      (ne_top_of_le_ne_top hrect <| arcLength_anti f b hax)
    exact (cont x ⟨hax, hx⟩).mono fun y hy ↦ ⟨hax.trans hy.1, hy.2.le⟩

theorem continuousOn_Ici_arcLength_left (cont : ContinuousOn f (Set.Icc a b)) :
    ContinuousOn (arcLength f · b) (Set.Ici a) := by
  rw [← arcLength_ne_iff, ← arcLength_comp_ofDual] at hrect; rw [arcLength_left_eq]
  exact (continuousOn_Iic_arcLength_right _ hrect <| by simpa).comp
    continuous_toDual.continuousOn fun x ↦ id

end

section

/-! ### Continuity lemmas with respect to a given order-connected set. -/

variable {s : Set α} (hconn : s.OrdConnected)
include hconn

theorem locallyBoundedVariationOn_iff_arcLength_ne_top :
    LocallyBoundedVariationOn f s ↔ ∀ ⦃a b⦄, a ∈ s → b ∈ s → arcLength f a b ≠ ∞ :=
  forall₄_congr <| fun a b ha hb ↦ by rw [Set.inter_eq_right.mpr (hconn.out ha hb)]; rfl

alias ⟨LocallyBoundedVariationOn.arcLength_ne_top, _⟩ :=
  locallyBoundedVariationOn_iff_arcLength_ne_top

variable [TopologicalSpace α] [OrderTopology α] (bdd : LocallyBoundedVariationOn f s)
         (cont : ContinuousOn f s)

include bdd cont

theorem continuousOn_arcLength_of_mem (ha : a ∈ s) : ContinuousOn (arcLength f a) s := by
  by_cases h : ∃ x ∈ s, ∀ y ∈ s, y ≤ x
  · obtain ⟨x, hxs, hx⟩ := h
    exact (continuousOn_Iic_arcLength_right f
      (bdd.arcLength_ne_top f hconn ha hxs) <| cont.mono <| hconn.out ha hxs).mono hx
  push_neg at h
  intro x hx; obtain ⟨y, hy, hxy⟩ := h x hx
  exact ((continuousOn_Iic_arcLength_right f (bdd.arcLength_ne_top f hconn ha hy) <|
    cont.mono <| hconn.out ha hy).continuousAt <| Iic_mem_nhds hxy).continuousWithinAt

variable (a b)

theorem continuousOn_arcLength_right : ContinuousOn (arcLength f a) s := by
  intro x hxs; obtain hxa | hax := lt_or_ge x a
  · exact (continuousAt_arcLength_right f hxa).continuousWithinAt
  by_cases h : ∀ y ∈ s, x ≤ y
  · exact ((continuous_add_left _).comp_continuousOn <| continuousOn_arcLength_of_mem
      f hconn bdd cont hxs).congr (fun y hy ↦ (arcLength_add f hax <| h y hy).symm) x hxs
  push_neg at h; obtain ⟨y, hys, hyx⟩ := h
  obtain hay | hya := le_total a y
  · apply ((continuous_add_left _).continuousAt.comp_continuousWithinAt <|
      continuousOn_arcLength_of_mem f hconn bdd cont hys x hxs).congr_of_eventuallyEq
      (Set.EqOn.eventuallyEq_of_mem _ <| inter_mem_nhdsWithin s <| Ici_mem_nhds hyx)
    exacts [(arcLength_add f hay hyx.le).symm, fun z hz ↦ (arcLength_add f hay hz.2).symm]
  exact continuousOn_arcLength_of_mem f hconn bdd cont (hconn.out hys hxs ⟨hya, hax⟩) x hxs

theorem continuousOn_arcLength_left : ContinuousOn (arcLength f · b) s := by
  rw [arcLength_left_eq]
  apply continuousOn_arcLength_right _ _ hconn.dual _ cont
  exact bdd.comp_ofDual

end

section

/-! ### Continuity -/

variable [TopologicalSpace α] [OrderTopology α] (a b) (bdd : LocallyBoundedVariationOn f Set.univ)
         (cont : Continuous f)
include bdd cont

theorem continuous_arcLength_left : Continuous (arcLength f · b) := by
  rw [← continuousOn_univ] at *
  exact continuousOn_arcLength_left f _ Set.ordConnected_univ bdd cont

theorem continuous_arcLength_right : Continuous (arcLength f a) := by
  rw [← continuousOn_univ] at *
  exact continuousOn_arcLength_right f _ Set.ordConnected_univ bdd cont

end
