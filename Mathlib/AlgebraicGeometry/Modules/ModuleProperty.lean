module

public import Mathlib

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

universe u

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

abbrev pullback' {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) : X.Modules :=
    (pullback f).obj M

def OpenLocus (P : ∀ {X : Scheme.{u}}, ObjectProperty X.Modules) (M : X.Modules) : X.Opens :=
  ⟨{x | ∃ (U : Scheme.{u}) (f : U ⟶ X) (_ : IsOpenImmersion f),
    x ∈ f.opensRange ∧ P (M.restrict f)}, by
  rw [isOpen_iff_forall_mem_open]
  intro x ⟨U, f, hf, hxU, hP⟩
  exact ⟨f.opensRange, fun y hy => ⟨U, f, hf, hy, hP⟩, f.opensRange.2, hxU⟩⟩

variable (P : ∀ {X : Scheme.{u}}, ObjectProperty X.Modules) (M : X.Modules)

lemma openLocus_def (x : X) : x ∈ OpenLocus P M ↔ ∃ (U : Scheme.{u}) (f : U ⟶ X)
    (_ : IsOpenImmersion f), x ∈ f.opensRange ∧ P (M.restrict f) := by simp [OpenLocus]

class IsPullbackStable : Prop where
  pullback_is : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules), P M → P (M.pullback' f)

lemma prop_of_pullback [IsPullbackStable P] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) (h : P M) : P (M.pullback' f) :=
  IsPullbackStable.pullback_is f M h

class IsRestrictStable : Prop where
  restrict_is : ∀ X Y (f : X ⟶ Y) (_ : IsOpenImmersion f) (M : Y.Modules),
    P M → P (M.restrict f)

lemma prop_of_restrict [IsRestrictStable P] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) [IsOpenImmersion f] (h : P M) : P (M.restrict f) :=
  IsRestrictStable.restrict_is X Y f ‹_› M h

instance [IsPullbackStable P] [∀ X, (P (X := X)).IsClosedUnderIsomorphisms] :
    IsRestrictStable P := by
  constructor
  intro X Y f _ M h
  let φ : M.restrict f ≅ _ := (restrictFunctorIsoPullback f).app M
  exact ObjectProperty.prop_of_iso P φ.symm <| M.prop_of_pullback P f h

abbrev restrictRestrictIso {U Y : Scheme.{u}} (f : U ⟶ Y) [IsOpenImmersion f]
    (g : Y ⟶ X) [IsOpenImmersion g] : M.restrict (f ≫ g) ≅ (M.restrict g).restrict f :=
  (restrictFunctorComp f g).app M

@[simp]
theorem restrict_locus_eq_preimage_locus [IsRestrictStable P]
    [∀ X, (P (X := X)).IsClosedUnderIsomorphisms] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) : OpenLocus P (M.restrict f) = f ⁻¹ᵁ OpenLocus P M := by
  apply le_antisymm
  · intro x h
    rw [openLocus_def] at h
    obtain ⟨U, ι, _, hx, hM⟩ := h
    rw [TopologicalSpace.Opens.mem_map, openLocus_def]
    use U, ι ≫ f, inferInstance, by aesop
    exact ObjectProperty.prop_of_iso P (M.restrictRestrictIso ι f).symm hM
  · intro x h
    rw [TopologicalSpace.Opens.mem_map, openLocus_def] at h
    obtain ⟨U, ι, _, hx, hM⟩ := h
    rw [openLocus_def]
    use Limits.pullback f ι, Limits.pullback.fst f ι, inferInstance, by
      rwa [Scheme.Hom.opensRange_pullbackFst]
    apply ObjectProperty.prop_of_iso P (M.restrictRestrictIso _ f)
    simp_rw [Limits.pullback.condition]
    apply ObjectProperty.prop_of_iso P (M.restrictRestrictIso _ _).symm
    exact prop_of_restrict P _ _ hM

class IsLocal : Prop where
  isLocal : ∀ X {M : X.Modules} (𝒰 : OpenCover.{u} X), (∀ i, P (M.restrict (𝒰.f i))) → P M

theorem openLocus_eq_top_iff [IsLocal P] : OpenLocus P M = ⊤ ↔ P M := sorry

end AlgebraicGeometry.Scheme.Modules
