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

In this file, we define the minimum cardinality of generating set for a submodule, which is
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
submodule, generating set, span rank
-/

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

namespace Submodule

/-- The minimum cardinality of a generating set of a submodule, possibly infinite, with type
  `ℕ∞`. If no finite generating set exists, the span rank is defined to be `⊤`. -/
noncomputable def spanRank (p : Submodule R M) : ℕ∞ :=
  ⨅ (s : Set M) (_ : span R s = p), s.encard

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

/-- A submodule's spanRank is not top if and only if it is finitely generated -/
@[simp]
lemma spanRank_ne_top_iff_fg {p : Submodule R M} :
    p.spanRank ≠ ⊤ ↔ p.FG := by
  simp [spanRank, Submodule.fg_def, and_comm]

/-- A submodule is finitely generated if and only if its spanRank is equal to its spanFinrank -/
lemma fg_iff_spanRank_eq_spanFinrank {p : Submodule R M} :
    p.FG ↔ p.spanRank = p.spanFinrank := by
  rw [spanFinrank, ← spanRank_ne_top_iff_fg, ← ENat.coe_toNat_eq_self, eq_comm]

/-- Constructs indexed generating elements whose cardinality equals `spanFinrank` for a finitely
  generated submodule.-/
theorem FG.exists_fun_spanFinrank_span_range_eq {p : Submodule R M} (h : p.FG) :
    ∃ f : Fin p.spanFinrank → M, span R (Set.range f) = p := by
  haveI : Nonempty { s // s.Finite ∧ span R s = p } := by
    rcases h with ⟨s, hs⟩
    exact ⟨s, ⟨Finset.finite_toSet s, hs⟩⟩
  obtain ⟨⟨s, h₁, h₂⟩, h₃ : h₁.toFinset.card = _⟩ :
    p.spanFinrank ∈ _ := by rw [spanFinrank_eq_iInf]; exact Nat.sInf_mem (Set.range_nonempty _)
  rw [← h₃]
  letI : Fintype (@Set.Elem M s) := h₁.fintype
  have temp : h₁.toFinset.card = @Fintype.card (@Set.Elem M s)
    (Fintype.ofFinite (@Set.Elem M s)) := by rw [Set.Finite.card_toFinset h₁]
  let f' :=  Fintype.equivFinOfCardEq temp.symm
  use Subtype.val ∘ f'.symm
  rw [Set.range_comp, Set.range_eq_univ.mpr]
  · simpa using h₂
  · exact f'.symm.surjective

/-- For a finitely generated submodule, its spanRank is less than or equal to n
  if and only if there are elements indexed by (Fin n) that generates the submodule. -/
lemma FG.spanRank_le_iff_exists_span_range_eq {p : Submodule R M} {n : ℕ} :
    p.spanRank ≤ n ↔ ∃ f : Fin n → M, span R (Set.range f) = p := by
  classical
  constructor
  · intro e
    have h := spanRank_ne_top_iff_fg.mp (e.trans_lt (WithTop.coe_lt_top n)).ne
    obtain ⟨f, hf⟩ := FG.exists_fun_spanFinrank_span_range_eq h
    use fun i => if h : i.1 < p.spanFinrank then f (Fin.castLT i h) else 0
    simp_rw [← hf]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      dsimp only
      split_ifs
      · apply Submodule.subset_span
        exact Set.mem_range_self _
      · exact (span R (Set.range f)).zero_mem
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      simp only [SetLike.mem_coe]
      apply Submodule.subset_span
      rw [fg_iff_spanRank_eq_spanFinrank] at h
      have he : (p.spanFinrank : WithTop Nat) ≤ n := by rwa [h] at e
      use Fin.castLE (ENat.coe_le_coe.mp he) x
      simp_all only [Fin.coe_castLE, Fin.is_lt, dite_true]
      rfl
  · rintro ⟨f, hf⟩
    let s : { s : Set M // s.Finite ∧ span R s = p} := ⟨Set.range f, Set.finite_range f, hf⟩
    calc
      p.spanRank
      ≤ s.2.1.toFinset.card := by
        rw [spanRank_eq_iInf]
        exact csInf_le (OrderBot.bddBelow _) (Set.mem_range_self _)
      _ = (Finset.univ.image f).card := by
        congr 2; ext
        simp only [Set.toFinite_toFinset, Set.mem_toFinset, Finset.mem_image, Finset.mem_univ,
          true_and]
        exact Set.mem_range
      _ ≤ n := by
        simp only [Nat.cast_le]
        convert Finset.card_image_le
        rw [Finset.card_univ, Fintype.card_fin]

/-- Generating elements for the submodule of minimum cardinality. -/
noncomputable def FG.generators {p : Submodule R M} (h : p.FG) : Fin p.spanFinrank → M :=
  Classical.choose (exists_fun_spanFinrank_span_range_eq h)

/-- The span of the generators equals the submodule -/
lemma FG.span_range_generators {p : Submodule R M} (h : p.FG) :
    span R (Set.range (generators h)) = p :=
  Classical.choose_spec (exists_fun_spanFinrank_span_range_eq h)

/-- The elements of the generators are in the submodule -/
lemma FG.generators_mem {p : Submodule R M} (h : p.FG) (i : Fin p.spanFinrank) :
    generators h i ∈ p := by
  simp_rw [← span_range_generators h]
  exact subset_span (Set.mem_range_self i)

@[simp]
lemma spanRank_eq_zero_iff_eq_bot {I : Submodule R M} : I.spanRank = 0 ↔ I = ⊥ := by
  constructor
  · intro e
    have H : Submodule.FG I := by
      rw [← Submodule.spanRank_ne_top_iff_fg, e]
      trivial
    rw [fg_iff_spanRank_eq_spanFinrank.mp H, ← WithTop.coe_zero, WithTop.coe_zero,
        Nat.cast_eq_zero] at e
    have := H.exists_fun_spanFinrank_span_range_eq
    rw [e] at this
    obtain ⟨f, hf⟩ := this
    rwa [show Set.range f = ∅ by simp, Submodule.span_empty, eq_comm] at hf
  · rintro rfl
    rw [← bot_eq_zero, eq_bot_iff, bot_eq_zero, ← WithTop.coe_zero]
    apply Submodule.FG.spanRank_le_iff_exists_span_range_eq.mpr
    exact ⟨fun _ ↦ 0, by simp⟩

lemma spanRank_sup_le_sum_spanRank {p q : Submodule R M} :
    (p ⊔ q).spanRank ≤ p.spanRank + q.spanRank := by
  by_cases hp : Submodule.FG p
  swap
  · rw [← Submodule.spanRank_ne_top_iff_fg, not_ne_iff] at hp
    rw [hp, top_add]
    exact le_top
  by_cases hq : Submodule.FG q
  swap
  · rw [← Submodule.spanRank_ne_top_iff_fg, not_ne_iff] at hq
    rw [hq, add_top]
    exact le_top
  obtain ⟨f, hf⟩ := hp.exists_fun_spanFinrank_span_range_eq
  obtain ⟨g, hg⟩ := hq.exists_fun_spanFinrank_span_range_eq
  rw [Submodule.fg_iff_spanRank_eq_spanFinrank] at hp hq
  rw [hp, hq, ← Nat.cast_add]
  rw [FG.spanRank_le_iff_exists_span_range_eq]
  refine ⟨(Sum.elim f g) ∘ finSumFinEquiv.symm, ?_⟩
  rw [Set.range_comp, Set.range_eq_univ.mpr (Equiv.surjective _), Set.image_univ,
    Set.Sum.elim_range, Submodule.span_union, hf, hg]

lemma spanRank_span_set_finite {s : Set R} (hs : s.Finite) :
    (Submodule.span R s).spanRank ≤ hs.toFinset.card := by
  rw [Submodule.FG.spanRank_le_iff_exists_span_range_eq]
  refine ⟨Subtype.val ∘ hs.toFinset.equivFin.symm, ?_⟩
  rw [Set.range_comp, Set.range_eq_univ.mpr (Equiv.surjective _), Set.image_univ,
    Subtype.range_val]
  congr
  ext
  exact hs.mem_toFinset

@[simp]
lemma spanRank_bot : (⊥ : Ideal R).spanRank = 0 :=
  Submodule.spanRank_eq_zero_iff_eq_bot.mpr rfl

end Submodule
