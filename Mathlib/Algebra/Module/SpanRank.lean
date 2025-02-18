/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Xuchun Li, Jingting Wang, Andrew Yang
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Minimum Cardinality of generating set of a submodule

In this file, we define the minimum cardinality of a generating set for a submodule, which is
implemented as `spanFinrank` and `spanRank`.
The difference between these two definitions is only that when no finite generating set exists,
`spanFinrank` takes value `0` but `spanRank` takes value `⊤`.

## Main Definitions

* `spanFinrank`: The minimum cardinality of a generating set of a submodule as a natural
  number. If no finite generating set exists, it is defined to be `0`.
* `spanRank`: The minimum cardinality of a generating set of a submodule, possibly infinite, with
  type `ℕ∞`. If no finite generating set exists, it is defined to be `⊤`.
* `FG.generators`: For a finitely generated submodule, get a set of minimum generating elements
  indexed by `Fin (p.spanFinrank)`

## Main Results

* `FG.exists_fun_spanFinrank_span_range_eq` : Any finitely generated submodule has a generating
  family of cardinality equal to `spanFinrank`.

## Tags
submodule, generating subset, span rank
-/

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

namespace Submodule

/-- The minimum cardinality of a generating set of a submodule, possibly infinite, with type
  `ℕ∞`. If no finite generating set exists, the span rank is defined to be `⊤`. -/
noncomputable def spanRank (p : Submodule R M) : ℕ∞ := ⨅ (s : Set M) (_ : span R s = p), s.encard

/-- The minimum cardinality of a generating set of a submodule as a natural number. If no finite
  generating set exists, the span rank is defined to be `0`. -/
noncomputable def spanFinrank (p : Submodule R M) : ℕ := (spanRank p).toNat

lemma spanRank_eq_iInf (p : Submodule R M) :
    p.spanRank = ⨅ (s : {s : Set M // s.Finite ∧ span R s = p}), (s.2.1.toFinset.card : ℕ∞) := by
  rw [spanRank]
  rcases (eq_or_ne (⨅ (s : Set M) (_ : span R s = p), s.encard) ⊤) with (h1 | h2)
  · rw [h1, eq_comm]; simp_rw [iInf_eq_top] at h1 ⊢
    exact fun s ↦ False.elim (((Set.encard_ne_top_iff (s := s.1)).mpr s.2.1) (h1 s.1 s.2.2))
  · apply le_antisymm
    · refine le_iInf (fun s ↦ (le_trans (iInf₂_le s.1 s.2.2) ?_))
      rw [s.2.1.encard_eq_coe_toFinset_card]
    · refine le_iInf (fun s ↦ (le_iInf (fun h ↦ ?_)))
      by_cases hs : s.Finite
      · apply @le_trans _ _ _ (hs.toFinset.card : ℕ∞) _
        · apply iInf_le (fun (s : {s : Set M // s.Finite ∧ span R s = p})
            ↦ (s.2.1.toFinset.card : ℕ∞)) ⟨s, ⟨hs, h⟩⟩
        · rw [hs.encard_eq_coe_toFinset_card]
      · rw [Set.Infinite.encard_eq hs]
        exact OrderTop.le_top _

lemma spanFinrank_eq_iInf (p : Submodule R M) :
    p.spanFinrank = ⨅ (s : {s : Set M // s.Finite ∧ span R s = p}), s.2.1.toFinset.card := by
  rw [spanFinrank, spanRank_eq_iInf, ENat.iInf_toNat]

/-- A submodule's `spanRank` is not top if and only if it is finitely generated. -/
@[simp]
lemma spanRank_ne_top_iff_fg {p : Submodule R M} : p.spanRank ≠ ⊤ ↔ p.FG := by
  simp [spanRank, Submodule.fg_def, and_comm]

/-- A submodule is finitely generated if and only if its `spanRank` is equal to its `spanFinrank`.-/
lemma fg_iff_spanRank_eq_spanFinrank {p : Submodule R M} : p.spanRank = p.spanFinrank ↔ p.FG := by
  rw [spanFinrank, ← spanRank_ne_top_iff_fg, ← ENat.coe_toNat_eq_self, eq_comm]

lemma spanRank_span_le_encard (s : Set M) : (Submodule.span R s).spanRank ≤ s.encard :=
  biInf_le _ (by constructor)

lemma spanFinrank_span_le_ncard_of_finite {s : Set M} (hs : s.Finite) :
    (span R s).spanFinrank ≤ s.ncard := by
  rw [← ENat.coe_le_coe]
  convert spanRank_span_le_encard (R := R) s
  · simpa [spanFinrank] using (⟨hs.toFinset, by simp⟩ : (span R s).FG)
  · exact hs.cast_ncard_eq

/-- Constructs a generating set with cardinality equal to the `spanFinrank` of the submodule when
  the submodule is finitely generated. -/
theorem FG.exists_span_set_encard_eq_spanFinrank {p : Submodule R M} (h : p.FG) :
    ∃ s : Set M, s.encard = p.spanFinrank ∧ span R s = p := by
  haveI : Nonempty { s // s.Finite ∧ span R s = p } := by
    rcases h with ⟨s, hs⟩
    exact ⟨s, ⟨Finset.finite_toSet s, hs⟩⟩
  obtain ⟨⟨s, h₁, h₂⟩, h₃ : h₁.toFinset.card = _⟩ :
    p.spanFinrank ∈ _ := by rw [spanFinrank_eq_iInf]; exact Nat.sInf_mem (Set.range_nonempty _)
  exact ⟨s, ⟨h₃.symm ▸ (Set.Finite.encard_eq_coe_toFinset_card h₁), h₂⟩⟩

theorem exists_span_set_encard_eq_spanRank (p : Submodule R M) :
    ∃ s : Set M, s.encard = p.spanRank ∧ span R s = p := by
  by_cases h : p.FG
  · rw [fg_iff_spanRank_eq_spanFinrank.mpr h]; exact FG.exists_span_set_encard_eq_spanFinrank h
  · have hp : span R p = p := by simp
    refine ⟨p, ⟨?_, hp⟩⟩
    rw [← spanRank_ne_top_iff_fg, ne_eq, Decidable.not_not] at h
    nth_rw 1 1 1 1 [h, eq_top_iff, ← h, ← hp]
    exact spanRank_span_le_encard (p : Set M)

/-- For a finitely generated submodule, its spanRank is less than or equal to `n`
  if and only if there is a generating subset with cardinality less than or equal to `n`. -/
lemma FG.spanRank_le_enat_iff_exists_span_set_encard_le (p : Submodule R M) {n : ℕ∞} :
    p.spanRank ≤ n ↔ ∃ s : Set M, s.encard ≤ n ∧ span R s = p := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_encard_eq_spanRank p
    exact ⟨s, ⟨hs₁ ▸ h, hs₂⟩⟩
  · exact (fun ⟨s, ⟨hs₁, hs₂⟩⟩ ↦ hs₂.symm ▸ (le_trans (spanRank_span_le_encard s) hs₁))

@[simp]
lemma spanRank_eq_zero_iff_eq_bot {I : Submodule R M} : I.spanRank = 0 ↔ I = ⊥ := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ :=
      (FG.spanRank_le_enat_iff_exists_span_set_encard_le I (n := 0)).mp (by rw [h])
    simp_all
  · rintro rfl
    rw [← nonpos_iff_eq_zero, ← ENat.coe_zero, FG.spanRank_le_enat_iff_exists_span_set_encard_le]
    refine ⟨∅, by simp⟩

@[simp]
lemma spanRank_bot : (⊥ : Ideal R).spanRank = 0 := Submodule.spanRank_eq_zero_iff_eq_bot.mpr rfl

/-- Generating elements for the submodule of minimum cardinality. -/
noncomputable def generators (p : Submodule R M) : Set M :=
  Classical.choose (exists_span_set_encard_eq_spanRank p)

lemma generators_encard (p : Submodule R M) : (generators p).encard = spanRank p :=
  (Classical.choose_spec (exists_span_set_encard_eq_spanRank p)).1

lemma FG.generators_ncard {p : Submodule R M} (h : p.FG) :
    (generators p).ncard = spanFinrank p := by
  rw [← ENat.coe_inj, ← fg_iff_spanRank_eq_spanFinrank.mpr h, Set.ncard, generators_encard,
      ← spanFinrank]
  exact (fg_iff_spanRank_eq_spanFinrank.mpr h).symm

/-- The span of the generators equals the submodule. -/
lemma span_generators (p : Submodule R M) : span R (generators p) = p :=
  (Classical.choose_spec (exists_span_set_encard_eq_spanRank p)).2

/-- The elements of the generators are in the submodule. -/
lemma FG.generators_mem (p : Submodule R M) : generators p ⊆ p := by
  nth_rw 2 [← span_generators p]
  exact subset_span (s := generators p)

lemma spanRank_sup_le_sum_spanRank {p q : Submodule R M} :
    (p ⊔ q).spanRank ≤ p.spanRank + q.spanRank := by
  apply (FG.spanRank_le_enat_iff_exists_span_set_encard_le (p ⊔ q)).mpr
  obtain ⟨sp, ⟨hp₁, rfl⟩⟩ := exists_span_set_encard_eq_spanRank p
  obtain ⟨sq, ⟨hq₁, rfl⟩⟩ := exists_span_set_encard_eq_spanRank q
  exact ⟨sp ∪ sq, ⟨hp₁ ▸ hq₁ ▸ (Set.encard_union_le sp sq), span_union sp sq⟩⟩

end Submodule
