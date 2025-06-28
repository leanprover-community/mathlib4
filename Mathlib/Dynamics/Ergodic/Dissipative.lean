/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Dynamics.Ergodic.Conservative

/-!
# Dissipative systems and Hopf decomposition
-/

open Function Set Filter MeasureTheory Measure
open scoped Topology ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {s t : Set α}

/-- A set is called *dissipative* for a self-map `f` and a measure `μ`,
if its preimages under iterations of `f` are a.e. disjoint with the original set.

Usually, this notion is used for a quasi measure preserving map `f` and a null measurable set `s`,
when it is equivalent to either of the following:

- the preimages of the set under the iterations of `f` are pairwise a.e. disjoint;
- there exists a measurable set `t ⊆ s` that is a.e. equal to `s`
  such that the preimages of `t` under the iterations of `f` are pairwise disjoint.

The choice of a specific definition
in the case of a non quasi measure preserving map or a non null measurable set
should be considered an implementation detail and can change in the future.
-/
structure IsDissipativeSet (f : α → α) (μ : Measure α) (s : Set α) : Prop where
  aedisjoint_iterate ⦃n : ℕ⦄ : 0 < n → AEDisjoint μ (f^[n] ⁻¹' s) s

namespace IsDissipativeSet

/-- A set of measure zero is a dissipative for any map. -/
theorem of_null (h : μ s = 0) : IsDissipativeSet f μ s :=
  ⟨fun _ _ ↦ measure_mono_null inter_subset_right h⟩

@[simp]
protected theorem empty : IsDissipativeSet f μ ∅ := of_null measure_empty

/-- If `s` is a null measurable dissipative set for a quasi measure preserving map `f`,
then there exists there exists a measurable set `t ⊆ s` that is a.e. equal to `s`
such that the preimages of `t` under the iterations of `f` are pairwise disjoint. -/
theorem exists_measurableSet (h : IsDissipativeSet f μ s) (hf : QuasiMeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) :
    ∃ t ⊆ s, MeasurableSet t ∧ t =ᵐ[μ] s ∧ Pairwise (Disjoint on (f^[·] ⁻¹' t)) := by
  have : NullMeasurableSet (s \ ⋃ n > 0, f^[n] ⁻¹' s) μ :=
    hs.diff <| .iUnion fun n ↦ .iUnion fun _ ↦ hs.preimage <| hf.iterate _
  rcases this.exists_measurable_subset_ae_eq with ⟨t, htsub, htm, hteq⟩
  refine ⟨t, htsub.trans diff_subset, htm, hteq.trans ?ae_eq, ?disj⟩
  case ae_eq =>
    rw [diff_ae_eq_self, ← AEDisjoint]
    simpa only [AEDisjoint.iUnion_right_iff, AEDisjoint.comm] using h.1
  case disj =>
    rw [pairwise_disjoint_on]
    intro m n hlt
    rcases exists_pos_add_of_lt hlt with ⟨k, hk, rfl⟩
    rw [add_comm m, iterate_add, preimage_comp]
    refine disjoint_sdiff_left.mono_right ?_ |>.mono htsub (preimage_mono htsub) |>.preimage _
    exact (preimage_mono diff_subset).trans <| subset_iUnion₂ (s := fun n _ ↦ f^[n] ⁻¹' s) k hk

theorem rightInverse' {g : α → α} (h : IsDissipativeSet f μ s) (hgf : RightInverse g f)
    (hg : QuasiMeasurePreserving g μ μ) :
    IsDissipativeSet g μ s where
  aedisjoint_iterate n hn := by
    refine measure_mono_null ?_ ((hg.iterate n).preimage_null <| h.aedisjoint_iterate hn)
    refine fun x ⟨hgx, hx⟩ ↦ ⟨?_, hgx⟩
    rwa [mem_preimage, hgf.iterate n]

/-- If `s` is a dissipative set of a quasi measure preserving map `f`,
then its preimages under the iterates of `f` are pairwise a.e. disjoint. -/
theorem aedisjoint_iterate_iterate (h : IsDissipativeSet f μ s)
    (hf : QuasiMeasurePreserving f μ μ) : Pairwise (AEDisjoint μ on (f^[·] ⁻¹' s)) := by
  rw [AEDisjoint.symmetric.pairwise_on]
  intro m n hlt
  rw [← Nat.sub_add_cancel hlt.le, iterate_add, preimage_comp]
  refine ((h.aedisjoint_iterate ?_).preimage (hf.iterate _)).symm
  rwa [Nat.sub_pos_iff_lt]

theorem disjointed_iUnion {e : α ≃ α} {s : ℕ → Set α} (hs : ∀ i, IsDissipativeSet e μ (s i)) :
    IsDissipativeSet e μ (⋃ i, s i \ ⋃ j < i, ⋃ n ≠ (0 : ℤ), (e^n : α ≃ α) ⁻¹' s j) where
 aedisjoint_iterate n hn := by
   simp_rw [preimage_iUnion, preimage_diff, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff]
   intro i j
   rcases lt_trichotomy i j with hlt | rfl | hlt
   · refine aedisjoint_compl_right.mono diff_subset ?_
     refine fun x ⟨_, hx⟩ hxi ↦ hx <| mem_iUnion₂_of_mem hlt ?_
     exact mem_iUnion₂.2 ⟨n, mod_cast hn.ne', hxi⟩
   · exact ((hs i).aedisjoint_iterate hn).mono diff_subset diff_subset
   · refine aedisjoint_compl_left.mono ?_ diff_subset
     refine fun x ⟨_, hx⟩ hxi ↦ hx <| mem_iUnion₂_of_mem hlt ?_
     exact mem_iUnion₂.2 ⟨(-n : ℤ), by simpa using hn.ne', by simpa⟩

theorem exists_saturation_eq_iUnion {ι : Type*} [Countable ι] {s : ι → Set α} {e : α ≃ α}
    (hs : ∀ i, IsDissipativeSet e μ (s i)) (hsm : ∀ i, MeasurableSet (s i))
    (hem : Measurable e) (hem' : Measurable e.symm) :
    ∃ t, IsDissipativeSet e μ t ∧ MeasurableSet t ∧
      ⋃ n : ℤ, (e^n) ⁻¹' t = ⋃ n : ℤ, (e^n) ⁻¹' ⋃ i, s i := by
  cases isEmpty_or_nonempty ι
  · use ∅
    simp
  · rcases exists_surjective_nat ι with ⟨f, hf⟩
    refine ⟨_, disjointed_iUnion fun n ↦ hs (f n), ?_, ?_⟩
    · measurability
    · ext x
      simp only [mem_iUnion, mem_diff, mem_preimage, not_exists, hf.exists]
      refine ⟨fun ⟨i, j, h, _⟩ ↦ ⟨i, j, h⟩, fun h ↦ ?_⟩
      classical rcases Nat.findX (exists_comm.1 h) with ⟨n, ⟨i, hi⟩, hn⟩
      refine ⟨i, n, hi, fun m hm k _ hmem ↦ hn m hm ⟨k + i, ?_⟩⟩
      rwa [zpow_add, Equiv.Perm.mul_apply]

theorem exists_saturation_eq_union {e : α ≃ α}
    (hsd : IsDissipativeSet e μ s) (hsm : MeasurableSet s)
    (htd : IsDissipativeSet e μ t) (htm : MeasurableSet t)
    (hem : Measurable e) (hem' : Measurable e.symm) :
    ∃ u, IsDissipativeSet e μ u ∧ MeasurableSet u ∧
      ⋃ n : ℤ, (e^n) ⁻¹' u = ⋃ n : ℤ, (e^n) ⁻¹' (s ∪ t) := by
  rw [union_eq_iUnion]
  apply exists_saturation_eq_iUnion <;> simp [*]

variable (μ) in
/-- There exists a measurable dissipative set
with the maximal possible value of the measure of the saturation. -/
theorem exists_max_measure {e : α ≃ α} (hem : Measurable e) (hem' : Measurable e.symm) :
    ∃ s : Set α, IsDissipativeSet e μ s ∧ MeasurableSet s ∧
      ∀ t, IsDissipativeSet e μ t → MeasurableSet t →
        μ (⋃ n : ℤ, (e^n) ⁻¹' t) ≤ μ (⋃ n : ℤ, (e^n) ⁻¹' s) := by
  set M := ⨆ (s : Set α) (_ : IsDissipativeSet e μ s) (_ : MeasurableSet s),
    μ (⋃ n : ℤ, (e^n) ⁻¹' s)
  cases eq_zero_or_neZero M with
  | inl hM => exact ⟨∅, .empty, by simpa [M] using hM⟩
  | inr _ =>
    rcases exists_seq_forall_of_frequently (frequently_lt_nhds M) with ⟨m, hm, hlt⟩
    simp only [M, lt_iSup_iff] at hlt
    choose s hsd hsm hsμ using hlt
    rcases exists_saturation_eq_iUnion hsd hsm hem hem' with ⟨S, hSd, hSm, hSeq⟩
    refine ⟨S, hSd, hSm, fun t htd htm ↦ ?_⟩
    calc
      μ (⋃ n : ℤ, (e^n) ⁻¹' t) ≤ M := le_iSup₂_of_le t htd (le_iSup (fun _ ↦ μ _) htm)
      _ ≤ μ (⋃ n : ℤ, (e^n) ⁻¹' ⋃ i,    s i) :=
        le_of_tendsto' hm fun i ↦ calc
          m i ≤ μ (⋃ n : ℤ, (e^n) ⁻¹' s i) := (hsμ _).le
          _ ≤ μ (⋃ n : ℤ, (e^n) ⁻¹' ⋃ i, s i) := by gcongr; apply subset_iUnion
      _ = μ (⋃ n : ℤ, (e^n) ⁻¹' S) := by rw [hSeq]

theorem ae_le_of_max_measure {e : α ≃ α} (hem : Measurable e) (hem' : Measurable e.symm)
    (hsd : IsDissipativeSet e μ s) (hsm : MeasurableSet s)
    (hmax : ∀ t, IsDissipativeSet e μ t → MeasurableSet t →
      μ (⋃ n : ℤ, (e^n) ⁻¹' t) ≤ μ (⋃ n : ℤ, (e^n) ⁻¹' s))
    (hfin : μ (⋃ n : ℤ, (e^n) ⁻¹' s) ≠ ∞)
    (htd : IsDissipativeSet e μ t) (htm : MeasurableSet t) :
    (⋃ n : ℤ, (e^n) ⁻¹' t) ≤ᵐ[μ] (⋃ n : ℤ, (e^n) ⁻¹' s) := by
  rcases exists_saturation_eq_union hsd hsm htd htm hem hem' with ⟨u, hud, hum, hust⟩
  simp_rw [← union_ae_eq_left_iff_ae_subset, ← iUnion_union_distrib, ← preimage_union]
  have : μ (⋃ n : ℤ, (e ^ n) ⁻¹' (s ∪ t)) ≤ μ (⋃ n : ℤ, (e ^ n) ⁻¹' s) := hust ▸ hmax _ hud hum
  refine .symm <| ae_eq_of_subset_of_measure_ge ?_ this ?_ ?_
  · gcongr; apply subset_union_left
  · measurability
  · exact ne_top_of_le_ne_top hfin this

theorem conservative_compl_saturation {e : α ≃ α} (hem : QuasiMeasurePreserving e μ μ)
    (hmax : ∀ t, IsDissipativeSet e μ t → MeasurableSet t →
      (⋃ n : ℤ, (e^n) ⁻¹' t) ≤ᵐ[μ] (⋃ n : ℤ, (e^n) ⁻¹' s)) :
    Conservative e (μ.restrict (⋃ n : ℤ, (e^n) ⁻¹' s)ᶜ) where
  toQuasiMeasurePreserving := hem.restrict <| by
    -- TODO: move to a lemma
    simp only [compl_iUnion, mapsTo_iInter]
    refine fun n ↦ (mapsTo_preimage _ _).mono_left ?_
    convert iInter_subset _ (n + 1) using 1
    rw [zpow_add_one, Equiv.Perm.coe_mul, preimage_comp, preimage_compl]
  exists_mem_iterate_mem' t htm ht₀ := by
    rw [μ.restrict_apply htm, ← diff_eq, ne_eq, ← ae_le_set] at ht₀
    contrapose! ht₀
    refine .trans (subset_iUnion (fun n : ℤ ↦ (e^n) ⁻¹' t) 0).eventuallyLE (hmax t ?_ htm)
    · exact ⟨fun n hn ↦ (disjoint_right.2 fun x hx ↦ ht₀ x hx n hn.ne').aedisjoint⟩

end IsDissipativeSet

theorem exists_hopf_decomposition [SFinite μ] {e : α ≃ α}
    (hem : QuasiMeasurePreserving e μ μ) (hem' : Measurable e.symm) :
    ∃ s : Set α, MeasurableSet s ∧ IsDissipativeSet e μ s ∧
      Conservative e (μ.restrict (⋃ n : ℤ, (e^n) ⁻¹' s)ᶜ) := by
  have := hem.measurable
  wlog hμ : IsFiniteMeasure μ generalizing μ
  · rcases exists_isFiniteMeasure_absolutelyContinuous μ with ⟨ν, hfin, hμν, hνμ⟩
    rcases this (hem.mono hνμ hμν) hfin with ⟨s, hsm, hsd, hsc⟩
    refine ⟨s, hsm, ?_, hsc.congr_ae ?_⟩
    -- TODO: move to a lemma
    · exact ⟨fun n hn ↦ hμν <| hsd.1 hn⟩
    -- TODO: move to a lemma
    · ext t
      have H₁ : MeasurableSet (⋃ n : ℤ, (e^n) ⁻¹' s)ᶜ := .compl <| by measurability
      have H₂ {u : Set α} : μ u = 0 ↔ ν u = 0 := ⟨fun h ↦ hνμ h, fun h ↦ hμν h⟩
      simp only [mem_ae_iff, Measure.restrict_apply' H₁, H₂]
  rcases IsDissipativeSet.exists_max_measure μ hem.measurable hem' with ⟨s, hsd, hsm, hs⟩
  refine ⟨s, hsm, hsd, IsDissipativeSet.conservative_compl_saturation hem ?_⟩
  intro t htd htm
  exact hsd.ae_le_of_max_measure this hem' hsm hs (measure_ne_top _ _) htd htm

end MeasureTheory
