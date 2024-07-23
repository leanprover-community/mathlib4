import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

universe u

namespace AlgebraicGeometry

open CategoryTheory

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)
variable (hP_local : RingHom.PropertyIsLocal P)
variable (hP_stable : RingHom.StableUnderBaseChange P)

def PretopologyOfRingProp : CategoryTheory.Pretopology Scheme where
  coverings X S := ∀ (Y : Scheme) (f : Y ⟶ X), S f → (affineLocally P f)
  has_isos X Y f h := by
    rw [Set.mem_def]
    intro Z g hg
    cases hg
    exact hP_local.affineLocally_of_isOpenImmersion f
  pullbacks X Y f S hS := by
    rw [Set.mem_def]
    intro T t ht
    cases ht with | mk Z h hh =>
      refine MorphismProperty.StableUnderBaseChange.snd ?_ h f ?_
      · apply AffineTargetMorphismProperty.IsLocal.stableUnderBaseChange
        · exact hP_local.isLocal_sourceAffineLocally
        · exact hP_local.stableUnderBaseChange_sourceAffineLocally hP_stable
      · apply hS _ _ hh
  transitive X S R hS hR := by
    rw [Set.mem_def]
    simp only [Subtype.forall]
    intro Z f hf
    cases hf with | intro Y hY =>
      obtain ⟨g, h, hh, hg, hf⟩ := hY
      rw [← hf]
      have SUC := hP_local.affineLocally_isStableUnderComposition
      apply MorphismProperty.comp_mem
      apply hR h hh Z g hg
      apply hS _ _ hh

/- In general, we want to intersect this with some kind of "pretopology of jointly surjective
families". To define that topology, we need the fact that a base change of a surjective morphism of
schemes is surjective (see [[Stacks], Tag 01S1]). -/
