/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou, Adam Topaz
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.JointlySurjective
import Mathlib.CategoryTheory.Sites.MorphismProperty

/-!

# Site defined by a morphism property

Given a multiplicative morphism property `P` that is stable under base change, we define the
associated precoverage on the category of schemes, where coverings are given
by jointly surjective families of morphisms satisfying `P`.

-/

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

namespace Scheme

/-- A morphism property of schemes is said to preserve joint surjectivity, if
for any pair of morphisms `f : X ⟶ S` and `g : Y ⟶ S` where `g` satisfies `P`,
any pair of points `x : X` and `y : Y` with `f x = g y` can be lifted to a point
of `X ×[S] Y`.

In later files, this will be automatic, since this holds for any morphism `g`
(see `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`). But at
this early stage in the import tree, we only know it for open immersions. -/
class IsJointlySurjectivePreserving (P : MorphismProperty Scheme.{u}) where
  exists_preimage_fst_triplet_of_prop {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hg : P g) (x : X) (y : Y) (h : f x = g y) :
    ∃ a : ↑(pullback f g), pullback.fst f g a = x

variable {P : MorphismProperty Scheme.{u}}

lemma IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
    [IsJointlySurjectivePreserving P] {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : P f) (x : X) (y : Y) (h : f x = g y) :
    ∃ a : ↑(pullback f g), (pullback.snd f g).base a = y := by
  let iso := pullbackSymmetry f g
  haveI : HasPullback g f := hasPullback_symmetry f g
  obtain ⟨a, ha⟩ := exists_preimage_fst_triplet_of_prop hf y x h.symm
  use (pullbackSymmetry f g).inv a
  rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_inv_comp_snd]

instance : IsJointlySurjectivePreserving @IsOpenImmersion where
  exists_preimage_fst_triplet_of_prop {X Y S f g} _ hg x y h := by
    rw [← show _ = (pullback.fst _ _ : pullback f g ⟶ _).base from
        PreservesPullback.iso_hom_fst Scheme.forgetToTop f g]
    have : x ∈ Set.range (pullback.fst f.base g.base) := by
      rw [TopCat.pullback_fst_range f.base g.base]
      use y
    obtain ⟨a, ha⟩ := this
    use (PreservesPullback.iso Scheme.forgetToTop f g).inv a
    rwa [← TopCat.comp_app, Iso.inv_hom_id_assoc]

/-- The precoverage on `Scheme` of jointly surjective families. -/
abbrev jointlySurjectivePrecoverage : Precoverage Scheme.{u} :=
  Types.jointlySurjectivePrecoverage.comap Scheme.forget

variable (P : MorphismProperty Scheme.{u})

/-- The precoverage on `Scheme` induced by `P` is given by jointly surjective families of
`P`-morphisms. -/
def precoverage : Precoverage Scheme.{u} :=
  jointlySurjectivePrecoverage ⊓ P.precoverage

@[simp]
lemma ofArrows_mem_precoverage_iff {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} :
    .ofArrows X f ∈ precoverage P S ↔ (∀ x, ∃ i, x ∈ Set.range (f i).base) ∧ ∀ i, P (f i) := by
  simp_rw [← Scheme.forget_map, ← Scheme.forget_obj,
    ← Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
  exact ⟨fun hmem ↦ ⟨hmem.1, fun i ↦ hmem.2 ⟨i⟩⟩, fun h ↦ ⟨h.1, fun {Y} g ⟨i⟩ ↦ h.2 i⟩⟩

instance [P.IsStableUnderComposition] : (precoverage P).IsStableUnderComposition := by
  dsimp only [precoverage]; infer_instance

instance [P.ContainsIdentities] [P.RespectsIso] : (precoverage P).HasIsos := by
  dsimp only [precoverage]; infer_instance

instance [IsJointlySurjectivePreserving P] [P.IsStableUnderBaseChange] :
    (precoverage P).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g T p₁ p₂ H := by
    rw [ofArrows_mem_precoverage_iff] at hf ⊢
    refine ⟨fun x ↦ ?_, fun i ↦ P.of_isPullback (H i).flip (hf.2 i)⟩
    obtain ⟨i, y, hy⟩ := hf.1 (g x)
    have := (H i).hasPullback
    obtain ⟨w, hw⟩ := IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop (hf.2 i)
      (f := g) x y hy.symm
    use i, (H i).isoPullback.inv w
    simpa [← Scheme.Hom.comp_apply]

/-- The Zariski precoverage on the category of schemes is the precoverage defined by
jointly surjective families of open immersions. -/
abbrev zariskiPrecoverage : Precoverage Scheme.{u} := precoverage @IsOpenImmersion

end AlgebraicGeometry.Scheme
