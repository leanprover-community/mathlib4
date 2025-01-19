/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Xuchun Li, Jingting Wang, Andrew Yang
-/
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Minimum Cardinality of Generating Set for Submodules

In this file, we define the minimum cardinality of a generating set for a submodule,
which is implemented as `minGeneratorCard` and `spanRank`.

## Main Definitions

* `minGeneratorCard`: The minimum cardinality of a generating set of a submodule as a natural
  number. If no finite generating set exists, the minimum cardinality is defined to be `0`.
* `spanRank`: The span rank of a submodule, possibly infinite, with type `WithTop ℕ`.
* `FG.minGenerator`: For a finitely generated submodule, get a minimal generating function.

## Main Results

* `FG.exists_fun_minGeneratorCard_span_range_eq` : Any finitely generated submodule has a generating
  family of cardinality equal to `minGeneratorCard`.

## Tags
submodule, generating set, span rank

-/

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

namespace Submodule

/-- The minimum cardinality of a generating set for a submodule. If the minimum cardinality
of a generating set is infinity, then the minimum cardinality is defined to be `0`. -/
noncomputable
def minGeneratorCard (p : Submodule R M) : ℕ :=
  ⨅ s : { s : Set M // s.Finite ∧ span R s = p}, s.2.1.toFinset.card

/-- The span rank of a submodule, possibly infinite -/
noncomputable
def spanRank (p : Submodule R M) : WithTop ℕ :=
  ⨅ s : { s : Set M // s.Finite ∧ span R s = p}, s.2.1.toFinset.card

/-- A submodule's span rank is not top if and only if it is finitely generated -/
lemma spanRank_ne_top_iff_fg {p : Submodule R M} :
    p.spanRank ≠ ⊤ ↔ p.FG := by
  simp [spanRank, Submodule.fg_def]

/-- A submodule is finitely generated if and only if there exists a finite set generating it -/
lemma fg_iff_card_finset_nonempty {p : Submodule R M} :
  p.FG ↔ Set.Nonempty (Finset.card '' { s : Finset M | span R (s : Set M) = p }) := by
  exact Set.image_nonempty.symm

/-- A submodule is finitely generated if and only if
its spanrank equals its minimum generator cardinality -/
lemma fg_iff_spanrank_eq_minGeneratorCard {p : Submodule R M} :
    p.FG ↔ p.spanRank = p.minGeneratorCard := by
  constructor
  · intro h
    haveI : Nonempty { s // s.Finite ∧ span R s = p } := by
      rwa [nonempty_subtype, ← fg_def]
    exact (WithTop.coe_iInf (OrderBot.bddBelow
      (Set.range fun i ↦ (minGeneratorCard.proof_1 p i).toFinset.card))).symm
  intro e
  rw [← spanRank_ne_top_iff_fg, e]
  exact WithTop.coe_ne_top

/-- Constructs a generating function whose cardinality equals
  `minGeneratorCard` for a finitely generated submodule.-/
theorem FG.exists_fun_minGeneratorCard_span_range_eq {p : Submodule R M} (h : p.FG) :
  ∃ f : Fin p.minGeneratorCard → M, span R (Set.range f) = p := by
  haveI : Nonempty { s // s.Finite ∧ span R s = p } := by
    rcases h with ⟨s, hs⟩
    use s
    constructor
    · exact Finset.finite_toSet s
    · exact hs
  obtain ⟨⟨s, h₁, h₂⟩, h₃ : h₁.toFinset.card = _⟩ :
    p.minGeneratorCard ∈ _ := Nat.sInf_mem (Set.range_nonempty _)
  rw [<- h₃]
  let f := ((@Fintype.ofFinite s h₁).equivFin).invFun
  letI t1 : Finite (@Set.Elem M s) := h₁
  letI t2 : Fintype (@Set.Elem M s) := h₁.fintype
  have temp : h₁.toFinset.card = @Fintype.card (@Set.Elem M s)
    (Fintype.ofFinite (@Set.Elem M s)) := by
      rw [Set.Finite.card_toFinset h₁]
  let f' := temp ▸ f
  let f' :=  Fintype.equivFinOfCardEq temp.symm
  use Subtype.val ∘ f'.symm
  rw [Set.range_comp, Set.range_eq_univ.mpr]
  · simp_all only [nonempty_subtype, Set.toFinite_toFinset, Set.toFinset_card,
    Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq, t2]
  exact f'.symm.surjective

/-- For a finitely generated submodule, its spanRank is less than or equal to n
    if and only if there exists a generating function from fin n -/
lemma FG.spanRank_le_iff_exists_span_range_eq {p : Submodule R M} {n : ℕ} :
  p.spanRank ≤ n ↔ ∃ f : Fin n → M, span R (Set.range f) = p := by
  classical
  constructor
  · intro e
    have h := spanRank_ne_top_iff_fg.mp (e.trans_lt (WithTop.coe_lt_top n)).ne
    obtain ⟨f, hf⟩ := FG.exists_fun_minGeneratorCard_span_range_eq h
    let f' : Fin n → M := fun i => if h : i.1 < p.minGeneratorCard then f (Fin.castLT i h) else 0
    use f'
    rw [← hf]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      dsimp only [f']
      split_ifs
      · apply Submodule.subset_span
        exact Set.mem_range_self _
      · exact (span R (Set.range f)).zero_mem
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      dsimp only [f']
      apply Submodule.subset_span
      rw [fg_iff_spanrank_eq_minGeneratorCard] at h
      have he : (p.minGeneratorCard : WithTop Nat) ≤ n := by rwa [h] at e
      use Fin.castLE (ENat.coe_le_coe.mp he) x
      dsimp [f']
      simp only [Fin.is_lt, ↓reduceDIte]
      rfl
  · rintro ⟨f, hf⟩
    let s : { s : Set M // s.Finite ∧ span R s = p} :=
      ⟨Set.range f, Set.finite_range f, hf⟩
    calc p.spanRank
        ≤ s.2.1.toFinset.card := csInf_le (OrderBot.bddBelow _) (Set.mem_range_self _)
        _ = (Finset.univ.image f).card := by congr 2; ext; simp; exact Set.mem_range
        _ ≤ n := by
          simp [WithTop.coe_le_coe]
          convert Finset.card_image_le
          rw [Finset.card_univ, Fintype.card_fin]

/-- An arbitrarily chosen generating family of minimal cardinality. -/
noncomputable def FG.minGenerator {p : Submodule R M} (h : p.FG) : Fin p.minGeneratorCard → M :=
  Classical.choose (exists_fun_minGeneratorCard_span_range_eq h)

/-- The span of the minimal generator equals the submodule -/
lemma FG.span_range_minGenerator {p : Submodule R M} (h : p.FG) :
  span R (Set.range (minGenerator h)) = p :=
  Classical.choose_spec (exists_fun_minGeneratorCard_span_range_eq h)

/-- The minimal generator elements are in the submodule -/
lemma FG.minGenerator_mem {p : Submodule R M} (h : p.FG) (i) :
  minGenerator h i ∈ p := by
  have := span_range_minGenerator h
  simp_rw [← this]
  exact subset_span (Set.mem_range_self i)

end Submodule
