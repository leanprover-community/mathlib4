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

theorem exists_generator_eq_min_generator_card {p : Submodule R M} (h : p.FG) :
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
  have temp : h₁.toFinset.card = @Fintype.card (@Set.Elem M s) (Fintype.ofFinite (@Set.Elem M s)) := by
    rw [Set.Finite.card_toFinset h₁]
  let f' := temp ▸ f
  let f' :=  Fintype.equivFinOfCardEq temp.symm
  use Subtype.val ∘ f'.symm
  rw [Set.range_comp, Set.range_eq_univ.mpr]
  simp_all only [nonempty_subtype, Set.toFinite_toFinset, Set.toFinset_card, Set.image_univ,
    Subtype.range_coe_subtype, Set.setOf_mem_eq, t2]
  exact f'.symm.surjective

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
#min_imports
end Submodule
