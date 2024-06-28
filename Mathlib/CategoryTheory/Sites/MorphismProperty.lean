import Mathlib

universe u

namespace AlgebraicGeometry

open CategoryTheory

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)
variable (hP_local : RingHom.PropertyIsLocal P)
variable (hP_stable : RingHom.StableUnderBaseChange P)

variable (J : Pretopology Scheme)

#synth (Inf (GrothendieckTopology Scheme))

def PretopologyOfRingProp : CategoryTheory.Pretopology Scheme where
  coverings X S := S ∈ J _ ∧ ∀ (Y : Scheme) (f : Y ⟶ X), S f → (affineLocally P f)
  has_isos X Y f h := by
    rw [Set.mem_def]
    simp only [Subtype.forall]
    constructor
    · apply J.has_isos
    · intro Z g hg
      cases hg
      exact hP_local.affineLocally_of_isOpenImmersion f
  pullbacks X Y f S hS := by
    rw [Set.mem_def]
    simp only [Subtype.forall]
    obtain ⟨lS, rS⟩ := hS
    constructor
    · apply J.pullbacks
      exact lS
    · intro T t ht
      cases ht with | mk Z h hh =>
        refine CategoryTheory.MorphismProperty.StableUnderBaseChange.snd ?_ h f ?_
        · apply AffineTargetMorphismProperty.IsLocal.stableUnderBaseChange
          · exact hP_local.isLocal_sourceAffineLocally
          · exact hP_local.stableUnderBaseChange_sourceAffineLocally hP_stable
        · apply rS _ _ hh
  transitive X S R hS hR := by
    rw [Set.mem_def]
    simp only [Subtype.forall]
    obtain ⟨lS, rS⟩ := hS
    constructor
    · apply J.transitive
      · exact lS
      · intros _ f hf
        exact (hR f hf).1
    · intro Z f hf
      cases hf with | intro Y hY =>
        obtain ⟨g, h, hh, ⟨hg, hf⟩⟩ := hY
        rw [← hf]
        have ⟨_, hg'⟩ := hR h hh
        have hg'' := hg' Z g hg
        have SUC := hP_local.affineLocally_isStableUnderComposition
        apply CategoryTheory.MorphismProperty.comp_mem
        apply hg''
        apply rS _ _ hh
