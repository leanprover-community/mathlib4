import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Combinatorics.SimpleGraph.Basic


/-!
# Vertex covers
This file defines **vertex covers** for a simple graph `G : SimpleGraph V` as subsets `C : Set V`
that meet every edge.  It provides two notions of minimality:

* `Set.min_size_cover` — a vertex cover of *minimum cardinality* among all covers;
* `Set.minimal_cover` — an *inclusion-minimal* vertex cover (no proper subset is a cover).


## Tags
vertex cover, minimum vertex cover, minimal vertex cover
-/


variable {V : Type*} {G : SimpleGraph V} {C : Set V}

open Set
open scoped Cardinal

def SimpleGraph.IsVertexCover (G : SimpleGraph V) (C : Set V) := ∀ ⦃v w⦄, G.Adj v w → v ∈ C ∨ w ∈ C

def SimpleGraph.IsMinSizeCover (C : Set V) :=
   G.IsVertexCover C ∧ ∀ (C' : Set V), G.IsVertexCover C' → #C' ≥ #C

def SimpleGraph.IsMinimalCover (C : Set V) :=
   G.IsVertexCover C ∧ ∀ C' ≤ C, G.IsVertexCover C' → C' = C

lemma top_is_cover : G.IsVertexCover ⊤ := by intro v w hadj; left; simp

lemma min_size_cover_exists : ∃ C : Set V, G.IsMinSizeCover C := by
  let S := {C : Set V | G.IsVertexCover C}
  have nonempty : Nonempty S := ⟨⊤, top_is_cover⟩
  let f : S → Cardinal := fun C => #C
  let ⟨κ, ⟨⟨C, hκC⟩, hminC⟩⟩ := Cardinal.lt_wf.has_min (Set.range f) (Set.range_nonempty f)
  refine ⟨C, ⟨C.prop, ?_⟩⟩
  intro C' hC'
  have : ¬f ⟨C', hC'⟩ < κ := hminC (f ⟨C', hC'⟩) (by simp)
  simpa [f, hκC] using this

lemma minimal_cover_no_isolated (hminc : G.IsMinimalCover C) : ∀ v ∈ C, ∃ w, G.Adj v w := by
  by_contra! hcontra
  obtain ⟨v, ⟨hvc, hnadj⟩⟩ := hcontra
  let C' : Set V := C \ {v}
  have hneq : C' ≠ C := fun h => by simp_all [C']
  refine (absurd · hneq) <| hminc.right C' diff_subset ?_

  show G.IsVertexCover C'
  intro w₁ w₂ hadj
  simp only [mem_diff, mem_singleton_iff, C']
  have hwᵢC : w₁ ∈ C ∨ w₂ ∈ C := hminc.left hadj
  rcases hwᵢC with hwᵢC | hwᵢC
  · refine Or.inl ⟨hwᵢC, ?_⟩; by_contra! hwv; exact absurd (hwv ▸ hadj) (hnadj w₂)
  · refine Or.inr ⟨hwᵢC, ?_⟩; by_contra! hwv; exact absurd (hwv ▸ hadj).symm (hnadj w₁)

lemma finite_min_size_cover_minimal (hmin : G.IsMinSizeCover C) (hfinC : C.Finite) :
     G.IsMinimalCover C := by
  refine And.intro hmin.left ?_
  intro C' hle hC'
  refine Set.Finite.eq_of_subset_of_card_le hfinC hle ?_
  have hcardle : #C ≤ #C' := hmin.right C' hC'
  have hfinC' := (Finite.subset hfinC hle)

  suffices h : Nat.card C = #C ∧ Nat.card C' = #↑C' from by
    exact_mod_cast (by simpa [h.1.symm, h.2.symm] using hcardle)
  constructor <;>
  exact Cardinal.cast_toNat_of_lt_aleph0 <| Cardinal.lt_aleph0_iff_finite.mpr (by assumption)
