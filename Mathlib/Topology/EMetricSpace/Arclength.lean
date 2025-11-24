/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Data.Set.Operations

/-!
# Arc length

This file is file is devoted to the definition of the `arclength` of a function `f` between
`a` and `b`.

## Main results

## Tags

Topology, Metric space, Continuity
-/

open ENNReal

variable {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E] (f : α → E) {a b c : α}

/--
The length of the arc  of the curve `f : α → E` between two points `a` and `b`, is defined
as the variation of `f` on the closed interval `[a, b]`. Equals zero when `b ≤ a`.
-/
noncomputable def arclength (a b : α) : ℝ≥0∞ :=
  eVariationOn f (Set.Icc a b)

theorem wf : WellFounded ((· < ·) : ℕ → ℕ → Prop) := sorry

-- Fixme
section
theorem mem_nhdsWithin_Ici_iff_exists_Ico_subset {α : Type*}
  [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
  {a u' : α} {s : Set α} (hu' : a < u') :
  s ∈ nhdsWithin a (Set.Ici a) ↔ ∃ (u : α) (H : u ∈ Set.Ioc a u'), Set.Ico a u ⊆ s := by sorry

end

/--
`arclength f a b` is the supremum of finite sums of `edist (f $ u i) (f $ u $ i+1)` for `u`
satisfying the same conditions as for `evariation_on` with the addition of:
* `u 0` is `a`.
* `u 1` is **not** `a`.
-/
theorem arclength_eq_supr (hab : a ≤ b) : arclength f a b =
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ (∀ i, u i ∈ Set.Icc a b) ∧ u 0 = a ∧ a < u 1},
    ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, hu, huab⟩
    by_cases h : ∀ m ≤ n, u m = a
    · have : ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        simp only [Finset.mem_range] at hi
        rw [h i (by linarith), h (i+1) (by linarith), edist_self]
      rw [this]; apply zero_le
    push_neg at h
    obtain ⟨m, ⟨hmn, hma⟩, hmin⟩ := WellFounded.has_min wf {m | m ≤ n ∧ u m ≠ a} h
    push_neg at hmin
    cases m with
    | zero =>
      refine le_iSup_of_le ⟨n + 1, Nat.rec a (fun k _ => u k), ⟨fun k => ?_,
        ⟨fun k => ?_, ⟨rfl, (huab 0).1.lt_of_ne' hma⟩⟩⟩⟩ ?_
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
      · refine ⟨n - m, ⟨fun k => u (m + k), ⟨?_, ?_⟩⟩⟩
        · exact hu.comp (fun _ _ h => add_le_add_left h _)
        · exact ⟨fun k => huab _, this m le_rfl, (huab _).1.lt_of_ne' hma⟩
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
    intro p; rw [arclength_eq_supr₂]
    let p' : ℕ × { u // Monotone u ∧ ∀ i, u i ∈ Set.Icc a b } :=
      ⟨p.1, ⟨p.2.val, ⟨p.2.property.1, p.2.property.2.1⟩⟩⟩
    exact le_iSup (fun p => ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))) p'

theorem edist_le_arclength (hab : a ≤ b) : edist (f a) (f b) ≤ arclength f a b := by
  refine eVariationOn.edist_le f ?_ ?_ <;> simp [hab]

/-- The length of a function over a singleton is zero. -/
theorem arclength_eq_zero (hab : b ≤ a) : arclength f a b = 0 := by
  refine eVariationOn.subsingleton f ?_; simp [hab]

theorem arclength_self (a : α) : arclength f a a = 0 := arclength_eq_zero _ (le_rfl)

theorem arclength_anti (c : α) : Antitone (fun x => arclength f x c) := by
  refine fun a b hab => eVariationOn.mono _ ?_
  rintro x ⟨hbx, hxc⟩
  exact ⟨hab.trans hbx, hxc⟩

theorem arclength_mono (a : α) : Monotone (arclength f a) := by
  refine fun x y hxy => eVariationOn.mono _ ?_
  rintro z ⟨haz, hzx⟩
  exact ⟨haz, hzx.trans hxy⟩

theorem arclength_add (hab : a ≤ b) (hbc : b ≤ c) :
    arclength f a b + arclength f b c  = arclength f a c := by
  simp_rw [arclength]
  convert eVariationOn.Icc_add_Icc f (s := Set.univ) hab hbc (by simp) <;> simp

theorem arclength_sum {n : ℕ} {u : ℕ → α} (hu : Monotone u) :
    ∑ i ∈ Finset.range n, arclength f (u i) (u (i + 1)) = arclength f (u 0) (u n) := by
  induction n with
  | zero => rw [arclength_self, Finset.sum_range_zero]
  | succ k ih => rw [Finset.sum_range_succ, ih, arclength_add f (hu <| zero_le k) (hu k.le_succ)]

theorem arclength_sub₀ (hba : b ≤ a) : arclength f a b = arclength f a c - arclength f b c := by
  rw [arclength_eq_zero f hba, eq_comm]
  exact tsub_eq_zero_of_le (arclength_anti f c hba)

theorem arclength_sub' (hbc : b ≤ c) (hac : arclength f b c ≠ ∞) :
    arclength f a b =  arclength f a c - arclength f b c := by
  rcases le_total a b with (hab | hba)
  · exact ENNReal.eq_sub_of_add_eq hac (arclength_add f hab hbc)
  · exact arclength_sub₀ f hba

theorem arclength_sub (hbc : b ≤ c) (hac : arclength f a c ≠ ∞) :
    arclength f a b = arclength f a c - arclength f b c := by
  rcases le_total a b with (hab | hba)
  · exact arclength_sub' f hbc <| ne_top_of_le_ne_top hac <| arclength_anti f c hab
  · exact arclength_sub₀ f hba

open OrderDual

@[simp]
theorem arclength_comp_of_dual :
    arclength (f ∘ ofDual) (toDual b) (toDual a) = arclength f a b := by
  unfold arclength
  have : Set.Icc (toDual b) (toDual a) = ofDual ⁻¹' (Set.Icc a b) := by simp
  rw [this, eVariationOn.comp_ofDual]

theorem arclength'_eq (b : α) :
    (fun x => arclength f x b) = arclength (f ∘ ofDual) (toDual b) ∘ toDual := by
  ext x; simp

-- set_option trace.Meta.Tactic.simp true
theorem arclength_Icc_extend (h : a ≤ b) (f : Set.Icc a b → E) :
    arclength (Set.IccExtend h f) a b = eVariationOn f Set.univ := by
  have : Set.projIcc a b h '' (Set.Icc a b) = Set.univ := by
    ext x; constructor
    · aesop
    revert x; exact Set.projIcc_surjOn h
  rw [←this]
  exact eVariationOn.comp_eq_of_monotoneOn _ _ (Monotone.monotoneOn (Set.monotone_projIcc h) _)


section

variable [TopologicalSpace α]

theorem continous_on_Iic_arclength_of_ge (h : b ≤ a) :
    ContinuousOn (arclength f a) (Set.Iic b) := by
  exact continuousOn_const.congr (fun x hx => arclength_eq_zero _ (trans hx h))

theorem continuous_on_Ici_arclength'_of_ge (h : b ≤ a) :
    ContinuousOn (fun x => arclength f x b) (Set.Ici a) := by
  exact continuousOn_const.congr (fun x hx => arclength_eq_zero _ (trans h hx))

variable [OrderTopology α]

theorem continuous_at_arclength_of_gt (h : b < a) : ContinuousAt (arclength f a) b :=
  continuousAt_const.congr <|
    Filter.eventuallyEq_of_mem (Iio_mem_nhds h) <|
      fun x hx => (arclength_eq_zero _ (by simp at hx; exact hx.le)).symm

theorem continuous_at_arclength'_of_gt (h : b < a) : ContinuousAt (fun x => arclength f x b) a :=
  continuousAt_const.congr <|
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds h) <|
      fun x hx => (arclength_eq_zero _ (by simp at hx; exact hx.le)).symm

variable (hab : a < b) (hrect : arclength f a b ≠ ∞) /- f is rectifiable on [a,b] -/
include hab hrect

theorem continuous_right_self_arclength
  (hcont : ContinuousWithinAt f (Set.Ico a b) a) /- f is right continuous at a -/ :
    ContinuousWithinAt (arclength f a) (Set.Ici a) a := by
  replace hcont : ContinuousWithinAt f (Set.Ici a) a := by
    refine hcont.mono_of_mem_nhdsWithin ?_
    refine (mem_nhdsWithin.mpr ⟨_, isOpen_Iio, hab, ?_⟩)
    rintro _ ⟨h₁, h₂⟩; exact ⟨h₂, h₁⟩
  rw [ContinuousWithinAt, arclength_self, ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hlab : arclength f a b = 0
  · rw [eventually_nhdsWithin_iff]
    refine Filter.eventually_of_mem (Iio_mem_nhds hab) (fun x hb ha => ?_)
    exact ((arclength_mono f a <| le_of_lt hb).trans_eq hlab).trans (zero_le ε)
  · have hε2 : 0 < ε / 2 := ENNReal.half_pos (ne_of_gt hε)
    rw [arclength_eq_supr f hab.le] at hrect hlab
    obtain ⟨⟨n, u, hu, hmem, hea, hal⟩, hl⟩ :=
      lt_iSup_iff.1 (ENNReal.sub_lt_self hrect hlab hε2.ne')
    simp_rw [← arclength_eq_supr f hab.le, edist_comm] at hl
    obtain ⟨c, hc, hcb⟩ : ∃ (c : α) (_ : _), _ := by
      rw [← mem_nhdsWithin_Ici_iff_exists_Ico_subset hab, ←Filter.Eventually]
      exact Iff.mp (EMetric.nhds_basis_eball.tendsto_right_iff) hcont _ hε2
    by_cases h : ∀ x, ¬ x ∈ Set.Ioo a c
    · unfold Filter.Eventually
      rw [mem_nhdsWithin_Ici_iff_exists_Ico_subset hab]
      refine ⟨c, hc, fun x hx => ?_⟩
      obtain rfl | hxa := eq_or_ne a x
      exacts [(arclength_self f a).trans_le (zero_le ε), (h x ⟨hx.1.lt_of_ne hxa, hx.2⟩).elim]
    · push_neg at h; obtain ⟨d, hd⟩ := h
      let e := min (u 1) d
      have hae : a < e := lt_min hal hd.1
      have hec : e < c := (min_le_right _ d).trans_lt hd.2
      unfold Filter.Eventually
      rw [mem_nhdsWithin_Ici_iff_exists_Ico_subset hab]
      refine ⟨e, ⟨hae, hec.le.trans hc.2⟩, fun x hx => (arclength_mono f a hx.2.le).trans ?_⟩
      obtain rfl | hε := eq_or_ne ε ⊤
      · exact le_top
      have : ε / 2 ≠ ⊤ :=
        fun h => (ENNReal.div_eq_top.1 h).elim (fun h => two_ne_zero h.2) (fun h => hε h.1)
      by_contra hac
      apply (Eq.refl <| arclength f a b).not_lt
      calc arclength f a b
        _ ≤ arclength f a b - ε/2 + ε/2 := by apply tsub_le_iff_right.mp; exact le_rfl
        _ < ∑ i ∈ Finset.range (n+1), edist (f <| u i) (f <| u (i+1)) + ε/2 := by
          rw [ENNReal.add_lt_add_iff_right this, Finset.sum_range_succ]
          calc arclength f a b - ε / 2
            _ < ∑ x ∈ Finset.range n, edist (f (u x)) (f (u (x + 1))) := by exact hl
            _ ≤ _ := by refine le_add_of_nonneg_right (by simp)
        _ ≤ ∑ i ∈ Finset.range n, edist (f <| u (i+1)) (f <| u (i+1+1)) +
            (edist (f e) (f a) + edist (f e) (f <| u 1)) + ε/2  := by
          refine add_le_add_right ?_ _
          rw [Finset.sum_range_succ', hea]
          apply add_le_add_left (edist_triangle_left _ _ _)
        _ ≤ ∑ i ∈ Finset.range n, arclength f (u <| i+1) (u <| i+1+1) +
          (ε/2 + arclength f e (u 1)) + ε/2 := by
          refine add_le_add_right ?_ (ε/2)
          refine add_le_add (Finset.sum_le_sum <| fun i _ =>
            edist_le_arclength f <| hu (i+1).le_succ) ?_
          refine add_le_add (le_of_lt <| hcb ⟨hae.le, hec⟩) <|
            edist_le_arclength f <| min_le_left _ d
        _ = _ + (ε + arclength f e (u 1)) := by rw [add_assoc, add_right_comm, ENNReal.add_halves]
        _ ≤ _ + arclength f (u 0) (u 1) := by
          rw [hea, ← arclength_add f hae.le <| min_le_left _ d, add_comm ε]
          rw [←add_comm (arclength _ _ _),  ←add_assoc _ _ ε, ←add_assoc _ (arclength _ _ _)]
          refine add_le_add_left (?_) _
          push_neg at hac; exact hac.le
        _ = ∑ i ∈ Finset.range (n+1), arclength f (u i) (u <| i+1) := by rw [Finset.sum_range_succ']
        _ = arclength f (u 0) (u <| n+1) := arclength_sum f hu
        _ ≤ arclength f a b := by rw [hea]; exact arclength_mono f a (hmem _).2

theorem continuous_right_arclength
  (hcont : ContinuousWithinAt f (Set.Ico a b) a) :
    ContinuousWithinAt (arclength f c) (Set.Ici a) a := by
  by_cases h : c ≤ a
  · sorry
  sorry

theorem continuous_left_arclength'
  (hcont : ContinuousWithinAt f (Set.Ioc a b) b) /- f is left continuous at b -/ :
    ContinuousWithinAt (arclength f a) (Set.Iic b) b := by
  -- rw [← arclength_comp_of_dual, ←arclength'_eq] at hrect
  sorry


omit hab

theorem continuous_left_arclength
  (hcont : ContinuousWithinAt f (Set.Ioc a b) b) /-f is left continuous at b-/ :
  ContinuousWithinAt (arclength f a) (Set.Iic b) b := by sorry

theorem continuous_right_arclength'
  (hcont : ContinuousWithinAt f (Set.Ico a b) a) /-f is right continuous at a-/ :
  ContinuousWithinAt (fun x => arclength f x b) (Set.Ici a) a := by sorry

theorem continuous_on_Iic_arclength (hcont : ContinuousOn f (Set.Icc a b)) :
  ContinuousOn (arclength f a) (Set.Iic b) := by sorry

theorem continuous_on_Ici_arclength' (hcont : ContinuousOn f (Set.Icc a b)) :
  ContinuousOn (fun x => arclength f x b) (Set.Ici a) := by sorry

end

section

variable {s : Set α} (hconn : s.OrdConnected)
include hconn

theorem has_locally_bounded_variation_on_iff_arclength_ne_top :
  LocallyBoundedVariationOn f s ↔ ∀ ⦃a b⦄, a ∈ s → b ∈ s → arclength f a b ≠ ∞ := by sorry

-- alias has_locally_bounded_variation_on_iff_arclength_ne_top :=
--   LocallyBoundedVariationOn.arclength_ne_top _

variable [TopologicalSpace α] [OrderTopology α] (hbdd : LocallyBoundedVariationOn f s)
         (hcont : ContinuousOn f s)

include hbdd hcont

theorem continuous_on_arclength_of_mem (ha : a ∈ s) : ContinuousOn (arclength f a) s := by sorry

variable (a b)

theorem continuous_on_arclength : ContinuousOn (arclength f a) s := by sorry

theorem continuous_on_arclength' : ContinuousOn (fun x => arclength f x b) s := by sorry

end

section

variable [TopologicalSpace α] [OrderTopology α] (a b) (hbdd : LocallyBoundedVariationOn f Set.univ)
         (hcont : Continuous f)
include hbdd hcont

theorem continuous_arlclength : Continuous (arclength f a) := by sorry

theorem continuous_arclenght' : Continuous (fun x => arclength f x b) := by sorry

end
