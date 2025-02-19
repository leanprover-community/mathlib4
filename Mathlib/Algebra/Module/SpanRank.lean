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
`spanFinrank` takes value in `ℕ` and equals `0` when no finite generating set exists.
`spanRank` takes value as a cardinal.

## Main Definitions

* `spanFinrank`: The minimum cardinality of a generating set of a submodule as a natural
  number. If no finite generating set exists, it is defined to be `0`.
* `spanRank`: The minimum cardinality of a generating set of a submodule as a cardinal.
* `FG.generators`: For a finitely generated submodule, get a set of generating elements with minimal
  cardinality.

## Main Results

* `FG.exists_span_set_card_eq_spanFinrank` : Any submodule has a generating set of cardinality equal
  to `spanRank`.

## Tags
submodule, generating subset, span rank

## TODO
* Add lemmas that link these notions to `Module.rank`.
-/

universe u

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

namespace Submodule

open Cardinal

/-- The minimum cardinality of a generating set of a submodule as a cardinal. -/
noncomputable def spanRank (p : Submodule R M) : Cardinal := ⨅ (s : {s : Set M // span R s = p}), #s

/-- The minimum cardinality of a generating set of a submodule as a natural number. If no finite
  generating set exists, the span rank is defined to be `0`. -/
noncomputable def spanFinrank (p : Submodule R M) : ℕ := (spanRank p).toNat

lemma spanRank_toENat_eq_iInf_encard (p : Submodule R M) : p.spanRank.toENat =
    (⨅ (s : Set M) (_ : span R s = p), s.encard) := by
  rw [spanRank]
  apply le_antisymm
  · refine le_iInf₂ (fun s hs ↦ ?_)
    rw [Set.encard, ENat.card]
    exact toENat.monotone' (ciInf_le' _ (⟨s, hs⟩ : {s : Set M // span R s = p}))
  · have := congrFun toENat_comp_ofENat.{u}.symm (⨅ (s : Set M) (_ : span R s = p), s.encard)
    rw [id_eq] at this; rw [this]
    haveI : Nonempty {s : Set M // span R s = p} := ⟨⟨p, by simp⟩⟩
    refine toENat.monotone' (le_ciInf fun s ↦ ?_)
    have : ofENat.{u} (⨅ (s' : Set M), ⨅ (_ : span R s' = p), s'.encard) ≤ ofENat s.1.encard :=
      ofENatHom.monotone' (le_trans (ciInf_le' _ s.1) (ciInf_le' _ s.2))
    apply le_trans this
    rw [Set.encard, ENat.card]
    exact Cardinal.ofENat_toENat_le _

lemma spanRank_toENat_eq_iInf_finset_card (p : Submodule R M) :
    p.spanRank.toENat =
      ⨅ (s : {s : Set M // s.Finite ∧ span R s = p}), (s.2.1.toFinset.card : ℕ∞) := by
  rw [spanRank_toENat_eq_iInf_encard]
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
  simp [spanFinrank, Cardinal.toNat, spanRank_toENat_eq_iInf_finset_card, ENat.iInf_toNat]

/-- A submodule's `spanRank` is finite if and only if it is finitely generated. -/
@[simp]
lemma spanRank_finite_iff_fg {p : Submodule R M} : p.spanRank < aleph0 ↔ p.FG := by
  rw [spanRank, Submodule.fg_def]
  constructor
  · rintro h
    obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s ∈
      Set.range (fun (s : {s : Set M // span R s = p}) ↦ #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
    refine ⟨s.1, ⟨?_, s.2⟩⟩
    simpa [← hs] using h
  · rintro ⟨s, ⟨hs₁, hs₂⟩⟩
    refine lt_of_le_of_lt (ciInf_le' _ ⟨s, hs₂⟩) ?_
    simpa

/-- A submodule is finitely generated if and only if its `spanRank` is equal to its `spanFinrank`.-/
lemma fg_iff_spanRank_eq_spanFinrank {p : Submodule R M} : p.spanRank = p.spanFinrank ↔ p.FG := by
  rw [spanFinrank, ← spanRank_finite_iff_fg, eq_comm]
  exact cast_toNat_eq_iff_lt_aleph0

lemma spanRank_span_le_card (s : Set M) : (Submodule.span R s).spanRank ≤ #s := by
  rw [spanRank]
  let s' : {s1 : Set M // span R s1 = span R s} := ⟨s, rfl⟩
  exact ciInf_le' _ s'

lemma spanFinrank_span_le_ncard_of_finite {s : Set M} (hs : s.Finite) :
    (span R s).spanFinrank ≤ s.ncard := by
  rw [← Nat.cast_le (α := Cardinal)]
  convert spanRank_span_le_card (R := R) s
  · rw [spanFinrank]
    refine Cardinal.cast_toNat_of_lt_aleph0 (lt_of_le_of_lt (spanRank_span_le_card s) ?_)
    simpa
  · exact Set.cast_ncard hs

/-- Constructs a generating set with cardinality equal to the `spanRank` of the submodule -/
theorem exists_span_set_card_eq_spanRank (p : Submodule R M) :
    ∃ s : Set M, #s = p.spanRank ∧ span R s = p := by
  rw [spanRank]
  obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s ∈
    Set.range (fun (s : {s : Set M // span R s = p}) ↦ #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
  exact ⟨s.1, ⟨hs, s.2⟩⟩

/-- Constructs a generating set with cardinality equal to the `spanFinrank` of the submodule when
  the submodule is finitely generated. -/
theorem FG.exists_span_set_encard_eq_spanFinrank {p : Submodule R M} (h : p.FG) :
    ∃ s : Set M, s.encard = p.spanFinrank ∧ span R s = p := by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
  refine ⟨s, ⟨?_, hs₂⟩⟩
  have := fg_iff_spanRank_eq_spanFinrank.mpr h
  rw [Set.encard, ENat.card, spanFinrank, hs₁, this]
  simp

/-- For a finitely generated submodule, its spanRank is less than or equal to a cardinal `a`
  if and only if there is a generating subset with cardinality less than or equal to `a`. -/
lemma FG.spanRank_le_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal} :
    p.spanRank ≤ a ↔ ∃ s : Set M, #s ≤ a ∧ span R s = p := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
    exact ⟨s, ⟨hs₁ ▸ h, hs₂⟩⟩
  · exact (fun ⟨s, ⟨hs₁, hs₂⟩⟩ ↦ hs₂.symm ▸ (le_trans (spanRank_span_le_card s) hs₁))

@[simp]
lemma spanRank_eq_zero_iff_eq_bot {I : Submodule R M} : I.spanRank = 0 ↔ I = ⊥ := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ :=
      (FG.spanRank_le_iff_exists_span_set_card_le I (a := 0)).mp (by rw [h])
    simp only [nonpos_iff_eq_zero, mk_eq_zero_iff, Set.isEmpty_coe_sort] at hs₁
    simp_all
  · rintro rfl; rw [spanRank]
    exact Cardinal.iInf_eq_zero_iff.mpr (Or.inr ⟨⟨∅, by simp⟩, by simp⟩)

@[simp]
lemma spanRank_bot : (⊥ : Ideal R).spanRank = 0 := Submodule.spanRank_eq_zero_iff_eq_bot.mpr rfl

/-- Generating elements for the submodule of minimum cardinality. -/
noncomputable def generators (p : Submodule R M) : Set M :=
  Classical.choose (exists_span_set_card_eq_spanRank p)

lemma generators_card (p : Submodule R M) : #(generators p) = spanRank p :=
  (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).1

lemma FG.generators_ncard {p : Submodule R M} (h : p.FG) :
    (generators p).ncard = spanFinrank p := by
  rw [← Nat.cast_inj (R := Cardinal), ← fg_iff_spanRank_eq_spanFinrank.mpr h, Set.ncard, Set.encard,
     ENat.card, generators_card, toNat_toENat, ← spanFinrank]
  exact (fg_iff_spanRank_eq_spanFinrank.mpr h).symm

/-- The span of the generators equals the submodule. -/
lemma span_generators (p : Submodule R M) : span R (generators p) = p :=
  (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).2

/-- The elements of the generators are in the submodule. -/
lemma FG.generators_mem (p : Submodule R M) : generators p ⊆ p := by
  nth_rw 2 [← span_generators p]
  exact subset_span (s := generators p)

lemma spanRank_sup_le_sum_spanRank {p q : Submodule R M} :
    (p ⊔ q).spanRank ≤ p.spanRank + q.spanRank := by
  apply (FG.spanRank_le_iff_exists_span_set_card_le (p ⊔ q)).mpr
  obtain ⟨sp, ⟨hp₁, rfl⟩⟩ := exists_span_set_card_eq_spanRank p
  obtain ⟨sq, ⟨hq₁, rfl⟩⟩ := exists_span_set_card_eq_spanRank q
  exact ⟨sp ∪ sq, ⟨hp₁ ▸ hq₁ ▸ (Cardinal.mk_union_le sp sq), span_union sp sq⟩⟩

section rank

-- Commented out since `StrongRankProperty` and `OrzechProperty` are not imported.
-- proof_wanted rank_eq_spanRank [Module.Free M] [StrongRankProperty R] :
--     M.rank = (⊤ : Submodule R M).spanRank

-- proof_wanted rank_le_spanRank [OrzechProperty R] :
--     M.rank ≤ (⊤ : Submodule R M).spanRank

end rank

end Submodule
