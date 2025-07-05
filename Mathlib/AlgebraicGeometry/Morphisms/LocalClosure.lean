/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Local closure of morphism properties

We define the source local closure of a property `P` wrt. a morphism property `W` and show it
inherits stability properties from `P`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable (W : MorphismProperty Scheme.{u})

/-- The source (Zariski-)local closure of `P` is satisfied if there exists
an open cover of the source on which `P` is satisfied. -/
def SourceLocalClosure (P : MorphismProperty Scheme.{u}) : MorphismProperty Scheme.{u} :=
  fun X _ f ↦ ∃ (𝒰 : Scheme.Cover.{u} W X), ∀ (i : 𝒰.J), P (𝒰.map i ≫ f)

namespace SourceLocalClosure

variable (P Q : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}}

/-- A choice of open cover on which `P` is satisfied if `f` satisfies the source local closure
of `P`. -/
noncomputable def openCover {f : X ⟶ Y} (hf : SourceLocalClosure W P f) : Scheme.Cover.{u} W X :=
  hf.choose

lemma property_openCoverMap_comp (f : X ⟶ Y) (hf : SourceLocalClosure W P f) (i : hf.openCover.J) :
    P (hf.openCover.map i ≫ f) :=
  hf.choose_spec i

lemma le [W.ContainsIdentities] [W.RespectsIso] : P ≤ SourceLocalClosure W P :=
  fun X Y f hf ↦ ⟨X.coverOfIsIso (𝟙 X), by simpa⟩

lemma iff_forall_exists [P.RespectsIso] {f : X ⟶ Y} :
    SourceLocalClosure IsOpenImmersion P f ↔ ∀ (x : X), ∃ (U : X.Opens), x ∈ U ∧ P (U.ι ≫ f) := by
  refine ⟨fun ⟨𝒰, hf⟩ x ↦ ?_, fun H ↦ ?_⟩
  · refine ⟨(𝒰.map (𝒰.f x)).opensRange, 𝒰.covers x, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, P.cancel_left_of_respectsIso]
    apply hf
  · choose U hx hf using H
    exact ⟨.mkOfCovers X (fun x ↦ U x) (fun _ ↦ (U _).ι) (fun x ↦ ⟨x, ⟨x, hx x⟩, rfl⟩)
      fun _ ↦ inferInstance, hf⟩

variable [W.IsStableUnderBaseChange] [Scheme.IsJointlySurjectivePreserving W]

instance [P.RespectsLeft Q] [Q.IsStableUnderBaseChange] :
    (SourceLocalClosure W P).RespectsLeft Q := by
  refine ⟨fun {X Y} Z f hf g ⟨𝒰, hg⟩ ↦ ⟨𝒰.pullbackCover f, fun i ↦ ?_⟩⟩
  simpa [pullback.condition_assoc] using
    RespectsLeft.precomp (Q := Q) _ (Q.pullback_snd _ _ hf) _ (hg i)

instance [P.RespectsRight Q] : (SourceLocalClosure W P).RespectsRight Q := by
  refine ⟨fun {X Y} Z f hf g ⟨𝒰, hg⟩ ↦ ⟨𝒰, fun i ↦ ?_⟩⟩
  rw [← Category.assoc]
  exact RespectsRight.postcomp _ hf _ (hg i)

instance [P.RespectsIso] : (SourceLocalClosure W P).RespectsIso where

instance [P.RespectsIso] [P.RespectsLeft @IsOpenImmersion] :
    IsLocalAtSource (SourceLocalClosure IsOpenImmersion P) where
  iff_of_openCover' {X Y} f 𝒰 := by
    refine ⟨fun ⟨𝒱, h⟩ ↦ fun i ↦ ⟨𝒱.pullbackCover (𝒰.map i), fun j ↦ ?_⟩, fun h ↦ ?_⟩
    · simpa [pullback.condition_assoc] using
        RespectsLeft.precomp (Q := @IsOpenImmersion) _ inferInstance _ (h j)
    · choose 𝒱 h𝒱 using h
      exact ⟨𝒰.bind 𝒱, fun i ↦ h𝒱 _ _⟩

instance [P.IsStableUnderBaseChange] : (SourceLocalClosure W P).IsStableUnderBaseChange := by
  refine .mk' fun X Y S f g _ ⟨𝒰, hg⟩ ↦ ⟨𝒰.pullbackCover (pullback.snd f g), fun i ↦ ?_⟩
  simpa [← pullbackLeftPullbackSndIso_hom_fst, P.cancel_left_of_respectsIso] using
    P.pullback_fst _ _ (hg i)

instance [W.ContainsIdentities] [P.ContainsIdentities] :
    (SourceLocalClosure W P).ContainsIdentities :=
  ⟨fun X ↦ ⟨X.coverOfIsIso (𝟙 X), fun _ ↦ P.id_mem _⟩⟩

instance [W.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] :
    (SourceLocalClosure W P).IsStableUnderComposition := by
  refine ⟨fun {X Y Z} f g ⟨𝒰, hf⟩ ⟨𝒱, hg⟩ ↦ ?_⟩
  refine ⟨𝒰.bind fun i ↦ (𝒱.pullbackCover (𝒰.map i ≫ f)), fun i ↦ ?_⟩
  simpa [← pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.condition_assoc] using
    P.comp_mem _ _ (P.pullback_snd _ _ (hf _)) (hg i.snd)

instance [W.IsMultiplicative] [P.IsStableUnderBaseChange] [P.IsMultiplicative] :
    (SourceLocalClosure W P).IsMultiplicative where

end SourceLocalClosure

variable {X Y : Scheme.{u}}

/-- A local isomorphism of schemes is a morphism that is (Zariski-)source-locally an
open immersion. -/
@[mk_iff]
class IsLocalIso (f : X ⟶ Y) : Prop where
  exists_isOpenImmersion (x : X) : ∃ (U : X.Opens), x ∈ U ∧ IsOpenImmersion (U.ι ≫ f)

namespace IsLocalIso

variable (f : X ⟶ Y)

lemma eq_sourceLocalClosure_isOpenImmersion :
    @IsLocalIso = SourceLocalClosure IsOpenImmersion IsOpenImmersion := by
  ext
  rw [isLocalIso_iff, SourceLocalClosure.iff_forall_exists]

instance : IsLocalAtSource @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

instance : IsMultiplicative @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

instance : IsStableUnderBaseChange @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

/-- `IsLocalIso` is weaker than every source-Zariski-local property containing identities. -/
lemma le_of_isLocalAtSource (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities]
    [IsLocalAtSource P] : @IsLocalIso ≤ P := by
  intro X Y f hf
  obtain ⟨𝒰, h⟩ := eq_sourceLocalClosure_isOpenImmersion ▸ hf
  rw [IsLocalAtSource.iff_of_openCover 𝒰 (P := P)]
  exact fun _ ↦ IsLocalAtSource.of_isOpenImmersion _

/-- `IsLocalIso` is the weakest source-Zariski-local property containing identities. -/
lemma eq_iInf :
    @IsLocalIso = ⨅ (P : MorphismProperty Scheme.{u}) (_ : P.ContainsIdentities)
      (_ : IsLocalAtSource P), P := by
  refine le_antisymm ?_ ?_
  · simp only [le_iInf_iff]
    apply le_of_isLocalAtSource
  · refine iInf_le_of_le @IsLocalIso (iInf_le_of_le inferInstance (iInf_le _ ?_))
    infer_instance

end IsLocalIso

end AlgebraicGeometry
