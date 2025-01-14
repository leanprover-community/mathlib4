import Mathlib.RingTheory.Finiteness.Defs

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
lemma spanRankNeTop_iff {p : Submodule R M} :
  p.spanRank ≠ ⊤ ↔ p.FG := by
  simp [spanRank, Submodule.fg_def]

/- For a finitely generated submodule, there exists a generating function from
    its minimum generator cardinality -/
theorem exists_generator_eq_min_generator_card {p : Submodule R M} (h : p.FG) :
  ∃ f : Fin p.minGeneratorCard → M, span R (Set.range f) = p := by
  obtain ⟨s, hs⟩ := h
  sorry
  /-
  let s' : { s : Set M // s.Finite ∧ span R s = p} := ⟨s, hs.1, hs.2⟩
  have nonempty : ∃ x, x ∈ ({ s : { s : Set M // s.Finite ∧ span R s = p} // True } : Set _) := by
    exists s'
  obtain ⟨⟨s, h₁, h₂⟩, h₃⟩ := Nat.sInf_mem nonempty
  have h₅ : h₁.toFinset.card = p.minGeneratorCard := h₃
  let e₁ := h₁.toFinset.equivFin
  let e₂ : Fin h₁.toFinset.card ≃ Fin p.minGeneratorCard := by
    rw [h₅]
    exact Equiv.refl _
  let f : Fin p.minGeneratorCard → M := fun i => (e₁.symm (e₂.symm i)).val
  existsi f
  rw [← h₂]
  apply span_eq_span_iff.mpr
  constructor
  · sorry  -- Proof of subset relation
  · sorry  -- Proof of reverse subset relation
  -/

/-- For a finitely generated submodule, its spanRank is less than or equal to n
    if and only if there exists a generating function from fin n -/
lemma minGeneratorCardLeIff_exists {p : Submodule R M} {n : ℕ} :
  p.spanRank ≤ n ↔ ∃ f : Fin n → M, span R (Set.range f) = p := by
  constructor
  · intro e
    have h := spanRankNeTop_iff.mp (e.trans_lt (WithTop.coe_lt_top n)).ne
    obtain ⟨f, hf⟩ := exists_generator_eq_min_generator_card h
    sorry
    --exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    let s : { s : Set M // s.Finite ∧ span R s = p} :=
      ⟨Set.range f, Set.finite_range f, hf⟩
    sorry
    /-calc p.spanRank
        ≤ s.2.1.toFinset.card := cInf_le (OrderBot.bddBelow _) (Set.mem_range_self _)
    _ = (Finset.univ.image f).card := by
        congr! 2
        ext
        simp
    _ ≤ n := by
        rw [WithTop.coe_le_coe]
        convert Finset.card_image_le
        rw [Finset.card_univ, Fintype.card_fin]-/

/-- For a finitely generated submodule, get a minimal generating function -/
noncomputable def minGenerator {p : Submodule R M} (h : p.FG) : Fin p.minGeneratorCard → M :=
  Classical.choose (exists_generator_eq_min_generator_card h)

/-- The span of the minimal generator equals the submodule -/
lemma spanMinGeneratorRange {p : Submodule R M} (h : p.FG) :
  span R (Set.range (minGenerator h)) = p :=
  Classical.choose_spec (exists_generator_eq_min_generator_card h)

/-- The minimal generator elements are in the submodule -/
lemma minGeneratorMem {p : Submodule R M} (h : p.FG) (i) :
  minGenerator h i ∈ p := by
  have := spanMinGeneratorRange h
  sorry
  --rw [← this]
  --exact subset_span (Set.mem_range_self i)
end Submodule
