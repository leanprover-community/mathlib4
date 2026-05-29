/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact

/-!
# Sheaves for the quasi-compact topology

In this file we show that a presheaf is a sheaf in the `AlgebraicGeometry.Scheme.propQCTopology`
if and only if it is a sheaf in the Zariski topology and a sheaf on single object
`P`-coverings of affine schemes.
-/

public section

universe w' w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]

set_option backward.isDefEq.respectTransparency false in
/-- A presheaf of types is a sheaf for the `P`-qc topology if and only if it is a sheaf
for the Zariski topology and satisfies the sheaf property for all single object coverings
`{ f : Spec S ⟶ Spec R }` where `f` satisfies `P`. -/
@[stacks 022H]
nonrec lemma isSheaf_type_propQCTopology_iff [P.IsMultiplicative] (F : Scheme.{u}ᵒᵖ ⥤ Type*)
    [IsZariskiLocalAtSource P] :
    Presieve.IsSheaf (propQCTopology P) F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          Presieve.IsSheafFor F (.singleton (Spec.map f)) := by
  refine ⟨fun hF ↦ ⟨?_, fun {R S} f hf hs ↦ ?_⟩, fun ⟨hzar, hff⟩ ↦ ?_⟩
  · exact Presieve.isSheaf_of_le _ zariskiTopology_le_propQCTopology hF
  · apply hF.isSheafFor
    rw [← Hom.presieve₀_cover _ hf]
    exact Cover.mem_propQCTopology _
  · rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
    intro T (𝒰 : Scheme.Cover _ _)
    wlog hT : ∃ (R : CommRingCat.{u}), T = Spec R generalizing T
    · refine T.affineOneHypercover.isSheafFor_of_pullback hzar ?_ ?_
      · intro i
        rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
          ← Presieve.isSheafFor_iff_generate]
        exact this (𝒰.pullback₂ (T.affineCover.f i)) ⟨_, rfl⟩
      · intro i j k
        rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
        apply Presieve.IsSheafFor.isSeparatedFor
        rw [← Presieve.ofArrows_pullback]
        exact this (𝒰.pullback₂ _) ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hT
    wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
    · obtain ⟨𝒱, f, hfin, ho⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
      have H (V : Scheme.{u}) (f : V ⟶ Spec R) : Presieve.IsSheafFor F
          (.ofArrows (𝒱.cover.pullback₂ f).X (𝒱.cover.pullback₂ f).f) := by
        refine V.affineOneHypercover.isSheafFor_of_pullback hzar (fun i ↦ ?_) (fun i j k ↦ ?_)
        · rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
            ← Presieve.isSheafFor_iff_generate]
          let 𝒰' := (𝒱.cover.pullback₂ f).pullback₂ (V.affineCover.f i)
          exact this _ (.ofQuasiCompactCover 𝒰' (qc := by dsimp [𝒰']; infer_instance))
            ⟨fun j ↦ .of_isIso (pullbackLeftPullbackSndIso (𝒱.f j) f (V.affineCover.f i)).hom, hfin⟩
        · rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
            ← Presieve.isSeparatedFor_iff_generate]
          exact (this _ (.ofQuasiCompactCover ((𝒱.cover.pullback₂ f).pullback₂ _)
              (qc := by dsimp; infer_instance))
            ⟨fun l ↦ .of_isIso (pullbackLeftPullbackSndIso (𝒱.f l) f _).hom, hfin⟩).isSeparatedFor
      refine f.isSheafFor_iff ?_ fun f ↦ (H _ f).isSeparatedFor
      exact this _ (.ofQuasiCompactCover 𝒱.cover)
        ⟨fun i ↦ inferInstanceAs <| IsAffine (Spec _), hfin⟩
    obtain ⟨_, _⟩ := h𝒰
    let 𝒰' := 𝒰.forgetQc.sigma
    rw [← Scheme.Cover.forgetQc_toPreZeroHypercover,
      ← Scheme.Cover.isSheafFor_sigma_iff hzar, Presieve.ofArrows_of_unique]
    have : IsAffine (𝒰.forgetQc.sigma.X default) := by dsimp; infer_instance
    let f : Spec _ ⟶ Spec R := (𝒰.forgetQc.sigma.X default).isoSpec.inv ≫ 𝒰.forgetQc.sigma.f default
    obtain ⟨φ, hφ⟩ := Spec.map_surjective f
    rw [Presieve.isSheafFor_singleton_iff_of_iso _ (Spec.map φ)
      (𝒰.forgetQc.sigma.X default).isoSpec (by simp [hφ, f])]
    refine hff _ ?_ ?_
    · simpa only [hφ, f] using IsZariskiLocalAtSource.comp (𝒰.forgetQc.sigma.map_prop _) _
    · simp only [hφ, f, Cover.sigma_I₀, PUnit.default_eq_unit, Cover.sigma_X, Cover.sigma_f, f]
      have : Surjective (Sigma.desc 𝒰.f) := inferInstanceAs <| Surjective (Sigma.desc 𝒰.forgetQc.f)
      infer_instance

variable {A : Type*} [Category* A]

/-- A presheaf is a sheaf for the `P`-qc topology if and only if it is a sheaf
for the Zariski topology and satisfies the sheaf property for all single object coverings
`{ f : Spec S ⟶ Spec R }` where `f` satisfies `P`. -/
@[stacks 022H]
nonrec lemma isSheaf_propQCTopology_iff [P.IsMultiplicative] (F : Scheme.{u}ᵒᵖ ⥤ A)
    [IsZariskiLocalAtSource P] :
    Presheaf.IsSheaf (propQCTopology P) F ↔
      Presheaf.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          ∀ (M : A),
          Presieve.IsSheafFor (F ⋙ coyoneda.obj (.op M)) (.singleton (Spec.map f)) := by
  grind [Presheaf.IsSheaf, isSheaf_type_propQCTopology_iff]

end AlgebraicGeometry
