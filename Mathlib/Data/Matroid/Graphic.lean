import Mathlib.Data.Matroid.Basic
import Mathlib

theorem SimpleGraph.IsAcyclic.mono {V : Type*} {G H : SimpleGraph V} (h : G ≤ H)
    (hH : H.IsAcyclic) : G.IsAcyclic :=
  fun _ c hc ↦ hH (c.map (.ofLE h)) (hc.map Function.injective_id)

open SimpleGraph
namespace Matroid


def graphicIndepMatroid {V : Type*} (G : SimpleGraph V) : IndepMatroid (Sym2 V) := by
  refine
    IndepMatroid.ofFinitary G.edgeSet
      (fun c ↦ c ⊆ G.edgeSet ∧ (SimpleGraph.fromEdgeSet c).IsAcyclic)
      ?empty ?subset ?aug ?compact ?ground
  case empty => simp
  case ground => simp_all
  case subset =>
    rintro I J ⟨hJG, hJ⟩ hIJ
    exact ⟨hIJ.trans hJG, hJ.mono (by gcongr)⟩
  case aug =>
    rintro I B ⟨hIE, hI⟩ hI' hB
    simp only [maximal_subset_iff, hIE, hI, and_self, and_imp, true_and, not_forall,
      Classical.not_imp, exists_prop] at hI'
    obtain ⟨J, hJG, hJ, hIJ, hIJ'⟩ := hI'
    sorry
  case compact =>
    sorry

end Matroid
