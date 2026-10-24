module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

variable {V : Type*} {G : SimpleGraph V}

namespace SimpleGraph

def IsPerfectGraph (G : SimpleGraph V) : Prop :=
  ∀ s : Set V, (G.induce s).chromaticNumber = (G.induce s).cliqueNum

noncomputable def induce_induce_iso (s : Set V) (t : Set s) :
    (G.induce s).induce t ≃g G.induce (Subtype.val '' t) where
  toFun v := ⟨v.1.1, v.1, v.2, rfl⟩
  invFun v :=
    ⟨Classical.choose v.2, (Classical.choose_spec v.2).1⟩
  left_inv v := by
    ext
    exact (Classical.choose_spec (⟨v.1, v.2, rfl⟩ : ∃ x ∈ t, x.val = v.1.1)).2
  right_inv v := by
    ext
    exact (Classical.choose_spec v.2).2
  map_rel_iff' := by
    intros
    rfl

theorem perfect_iff_subgraph_perfect :
    G.IsPerfectGraph ↔ ∀ s : Set V, (G.induce s).IsPerfectGraph := by
  constructor
  · intro hG s t
    rw [IsPerfectGraph] at hG
    let iso := @induce_induce_iso V G s t
    have h_chrom := Iso.chromaticNumber_eq iso
    have h_clique := Iso.cliqueNum_eq iso
    simp_all only [comap_comap, Function.Embedding.coe_subtype]
  · intro h s
    specialize h s
    rw [IsPerfectGraph] at h
    let s1 : Set s := Subtype.val ⁻¹' s
    specialize h s1
    let iso := @induce_induce_iso V G s s1
    have h_set : Subtype.val '' s1 = s := by
      simp [s1]
    have h_chrom := by
      have h_eq := Iso.chromaticNumber_eq iso
      rwa [h_set] at h_eq
    have h_clique := by
      have h_eq := Iso.cliqueNum_eq iso
      rwa [h_set] at h_eq
    rw [h_chrom,h_clique] at h
    simpa only using h

end SimpleGraph
