import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
import Mathlib.AlgebraicTopology.Anodyne

noncomputable section

open CategoryTheory Limits SimplicialCategory

open scoped Simplicial

namespace SSet

/--
A morphism of simplicial sets is a Kan fibration if it has the right lifting property wrt
every horn inclusion  `Λ[n, i] ⟶ Δ[n]`. -/
def KanFibration : MorphismProperty SSet := fun _ _ p ↦ HornInclusions.rlp p

lemma kanComplex_of_kanFibration (S T : SSet) (hT : IsTerminal T)
    (h : KanFibration (hT.from S)) :
    KanComplex S where
  hornFilling n i σ₀ := by
    have hh : CommSq σ₀ (hornInclusion n i) (hT.from S) (hT.from _) := ⟨by simp⟩
    obtain ⟨σ, hσ, _⟩ := (h _ (HornInclusion.mk n i)).1 hh
    exact ⟨σ, hσ.symm⟩

lemma kanFibration_of_kanComplex (S T : SSet) [KanComplex S] (hT : IsTerminal T) :
    KanFibration (hT.from S) := by
  rintro _ _ _ hi
  cases hi with
  | mk n i =>
    refine ⟨fun {f _} h ↦ ?_⟩
    obtain ⟨σ, hσ⟩ := KanComplex.hornFilling f
    refine ⟨⟨σ, hσ.symm, hT.hom_ext _ _⟩⟩

lemma kanFibration_iff_rlp_anodyne {S T : SSet} (f : S ⟶ T) : KanFibration f ↔
    ∀ {X Y} (g : X ⟶ Y) (_ : Anodyne g), HasLiftingProperty g f := by
  rw [KanFibration, MorphismProperty.WeakSaturation.rlp_eq]
  exact Iff.rfl

lemma kanFibration_hasLiftingProperty_anodyne {S T U V : SSet} (f : S ⟶ T) (g : U ⟶ V)
    (hf : KanFibration f) (hg : Anodyne g) : HasLiftingProperty g f := by
  rw [kanFibration_iff_rlp_anodyne] at hf
  exact hf _ hg

end SSet
