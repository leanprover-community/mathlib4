/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# The Lyapunov's convexity theorem
-/

public section

namespace MeasureTheory.Measure

open Function

variable {α : Type*} [MeasurableSpace α]

@[expose]
def IsAtom (s : Set α) (μ : Measure α) :=
  MeasurableSet s ∧ 0 < μ s ∧ ∀ t ⊆ s, MeasurableSet t → μ t = 0 ∨ μ t = μ s

class NoAtoms (μ : Measure α) : Prop where
  no_atoms : ∀ s, ¬ IsAtom s μ

/-- For a symmetric relation `r`, the family `Fin.cons a f` is pairwise related if and only if
`a` is related to every `f j` and `f` is pairwise related. -/
theorem _root_.Fin.pairwise_cons_iff {β : Type*} {r : β → β → Prop} [Std.Symm r] {m : ℕ}
    {a : β} {f : Fin m → β} :
    Pairwise (r on (Fin.cons a f : Fin (m + 1) → β)) ↔ (∀ j, r a (f j)) ∧ Pairwise (r on f) := by
  simp [Pairwise, Fin.forall_fin_succ, onFun, eq_comm (a := (0 : Fin _)), forall_and]
  grind [Std.Symm]

namespace NoAtoms

variable {μ : Measure α} [NoAtoms μ]

/-- A measurable set of nonzero measure for a measure without atoms contains a measurable subset
whose measure is neither zero nor the measure of the whole set. -/
theorem exists_measurableSet_subset {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ 0) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ t ≠ 0 ∧ μ t ≠ μ s := by
  simpa [IsAtom, hs, pos_iff_ne_zero, hμs] using NoAtoms.no_atoms (μ := μ) s

variable [IsFiniteMeasure μ]

/-- A measurable set of nonzero measure for a finite measure without atoms splits into two
measurable pieces of positive measure. -/
theorem exists_measurableSet_subset_pos_sdiff_pos {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ 0) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ 0 < μ (s \ t) := by
  obtain ⟨t, hts, ht, h0, hne⟩ := exists_measurableSet_subset hs hμs
  refine ⟨t, hts, ht, pos_iff_ne_zero.2 h0, ?_⟩
  rw [measure_sdiff hts ht.nullMeasurableSet (measure_ne_top μ t), tsub_pos_iff_lt]
  exact (measure_mono hts).lt_of_ne hne

/-- A measurable set of nonzero measure for a finite measure without atoms contains `m` pairwise
disjoint measurable subsets of nonzero measure. -/
theorem exists_pairwise_disjoint_fin (m : ℕ) {A : Set α} (hA : MeasurableSet A) (hμA : μ A ≠ 0) :
    ∃ f : Fin m → Set α, (∀ j, MeasurableSet (f j) ∧ f j ⊆ A ∧ μ (f j) ≠ 0) ∧
      Pairwise (Disjoint on f) := by
  induction m generalizing A with
  | zero => simp
  | succ m ih =>
    obtain ⟨B, hBA, hB, hB0, hAB0⟩ := exists_measurableSet_subset_pos_sdiff_pos hA hμA
    obtain ⟨g, hg, hgd⟩ := ih (hA.diff hB) hAB0.ne'
    use Fin.cons B g, ?_, ?_
    · rw [Fin.forall_fin_succ]
      use ⟨hB, hBA, hB0.ne'⟩, fun i ↦ ?_
      obtain ⟨hgi, hgiA, hgi0⟩ := hg i
      exact ⟨hgi, hgiA.trans Set.sdiff_subset, hgi0⟩
    · rw [Fin.pairwise_cons_iff]
      use fun j ↦ Set.disjoint_sdiff_right.mono_right (hg j).right.left

end NoAtoms

namespace IsAtom

/-- An atom of a finite measure `ν` is null for every measure without atoms that is absolutely
continuous with respect to `ν`. -/
theorem measure_eq_zero_of_absolutelyContinuous {μ ν : Measure α} [NoAtoms μ]
    [IsFiniteMeasure ν] {s : Set α} (hs : IsAtom s ν) (hμν : μ ≪ ν) : μ s = 0 := by
  obtain ⟨hs, -, hatom⟩ := hs
  by_contra hμs
  obtain ⟨t, hts, ht, h0, hne⟩ := NoAtoms.exists_measurableSet_subset hs hμs
  have hνt : ν t = ν s := (hatom t hts ht).resolve_left fun h ↦ h0 (hμν h)
  have : ν (s \ t) = 0 := by
    rw [measure_sdiff hts ht.nullMeasurableSet (measure_ne_top ν t), hνt, tsub_self]
  exact hne (measure_eq_measure_of_null_sdiff hts (hμν this))

end IsAtom

/-- A finite sum of finite measures without atoms has no atoms. -/
instance noAtoms_finsetSum {ι : Type*} (s : Finset ι) (m : ι → Measure α)
    [∀ i, IsFiniteMeasure (m i)] [∀ i, NoAtoms (m i)] : NoAtoms (∑ i ∈ s, m i) where
  no_atoms A hA := by
    obtain ⟨i, hi, hne⟩ : ∃ i ∈ s, m i A ≠ 0 := by
      obtain ⟨-, hpos, -⟩ := hA
      simpa using hpos.ne'
    exact hne (hA.measure_eq_zero_of_absolutelyContinuous
      (absolutelyContinuous_finsetSum_right hi .rfl))

section LyapunovConvexity

variable {ι : Type*} [Fintype ι] (μ : ι → SignedMeasure α)

/-- The sum of the total variations of a finite family of signed measures. -/
noncomputable def sumTotalVariation : Measure α :=
  ∑ i, (μ i).totalVariation

theorem totalVariation_le_sumTotalVariation (i : ι) :
    (μ i).totalVariation ≤ sumTotalVariation μ :=
  Finset.single_le_sum (fun j _ ↦ (μ j).totalVariation.zero_le) (Finset.mem_univ i)

instance : IsFiniteMeasure (sumTotalVariation μ) :=
  inferInstanceAs (IsFiniteMeasure (∑ i, (μ i).totalVariation))

variable [∀ i, NoAtoms (μ i).totalVariation]

instance : NoAtoms (sumTotalVariation μ) :=
  inferInstanceAs (NoAtoms (∑ i, (μ i).totalVariation))

end LyapunovConvexity

end MeasureTheory.Measure
