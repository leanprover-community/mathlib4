/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou, Adam Topaz
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.MorphismProperty

/-!

# Site defined by a morphism property

Given a multiplicative morphism property `P` that is stable under base change, we define the
associated (pre)topology on the category of schemes, where coverings are given
by jointly surjective families of morphisms satisfying `P`.

## TODO

- Define the small site on `Over P Q X`.

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
    (hg : P g) (x : X) (y : Y) (h : f.base x = g.base y) :
    ∃ a : ↑(pullback f g), (pullback.fst f g).base a = x

variable (P : MorphismProperty Scheme.{u})

lemma IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
    [IsJointlySurjectivePreserving P] {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : P f) (x : X) (y : Y) (h : f.base x = g.base y) :
    ∃ a : ↑(pullback f g), (pullback.snd f g).base a = y := by
  let iso := pullbackSymmetry f g
  haveI : HasPullback g f := hasPullback_symmetry f g
  obtain ⟨a, ha⟩ := exists_preimage_fst_triplet_of_prop hf y x h.symm
  use (pullbackSymmetry f g).inv.base a
  rwa [← Scheme.comp_base_apply, pullbackSymmetry_inv_comp_snd]

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

variable (P : MorphismProperty Scheme.{u})
  [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
  [P.HasPullbacks]

structure IsCover {X : Scheme.{u}} (R : Presieve X) : Prop where
  jointlySurjective : ∀ x : X, ∃ (Y : Scheme.{u}) (y : Y) (f : Y ⟶ X), R f ∧ f.base y = x
  prop {Y : Scheme.{u}} (f : Y ⟶ X) : R f → P f

def coverage : Coverage Scheme.{u} where
  covering X S := IsCover P S
  pullback X Y f S hS := by
    have : S.HasPullback f := ⟨fun {W} p hp ↦ P.hasPullback _ _ (hS.prop p hp)⟩
    refine ⟨.pullbackArrows f S, ⟨?_, ?_⟩, ?_⟩
    · intro y
      obtain ⟨Z, z, g, hg, hz⟩ := hS.jointlySurjective (f.base y)
      have hPg : P g := hS.prop g hg
      have : HasPullback g f := P.hasPullback _ _ hPg
      obtain ⟨w, hw⟩ :=
        IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop (P := P) hPg z y hz
      exact ⟨pullback g f, w, pullback.snd g f, .mk Z g hg, hw⟩
    · rintro Z g ⟨W, p, hp⟩
      have : HasPullback p f := P.hasPullback _ _ (hS.prop p hp)
      apply P.pullback_snd _ _ (hS.prop p hp)
    · exact Presieve.FactorsThruAlong.pullbackArrows f S

@[simp]
lemma ofArrows_mem_coverage_iff {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} :
    Presieve.ofArrows X f ∈ coverage P S ↔ (∀ x, ∃ i, x ∈ Set.range (f i).base) ∧ ∀ i, P (f i) := by
  refine ⟨fun hmem ↦ ⟨fun x ↦ ?_, fun i ↦ hmem.2 _ ⟨i⟩⟩,
      fun h ↦ ⟨fun x ↦ ?_, fun {Y} g ⟨i⟩ ↦ h.2 i⟩⟩
  · obtain ⟨Y, y, g, ⟨i⟩, heq⟩ := hmem.1 x
    use i, y
  · obtain ⟨i, y, h⟩ := h.1 x
    use X i, y, f i, ⟨i⟩

instance [P.IsStableUnderComposition] : (coverage P).IsStableUnderComposition where
  mem_covering_comp {ι} S X f hf σ Y g hg := by
    refine ⟨fun x ↦ ?_, fun {W} p ⟨i⟩ ↦ ?_⟩
    · obtain ⟨-, w, -, ⟨i⟩, hw⟩ := hf.jointlySurjective x
      obtain ⟨-, z, -, ⟨j⟩, hz⟩ := (hg i).jointlySurjective w
      clear Y; clear Y
      use Y i j, z, g i j ≫ f i,  .mk (Sigma.mk i j), ?_
      simp [hz, hw]
    · exact P.comp_mem _ _ ((hg i.1).prop _ (.mk i.snd)) (hf.prop _ (.mk i.1))

instance : (coverage P).IsStableUnderBaseChange where
  mem_covering_of_isPullback {ι} S X f hf Y g T p₁ p₂ H := by
    rw [ofArrows_mem_coverage_iff] at hf ⊢
    refine ⟨fun x ↦ ?_, fun i ↦ P.of_isPullback (H i).flip (hf.2 i)⟩
    obtain ⟨i, y, hy⟩ := hf.1 (g.base x)
    have := (H i).hasPullback
    obtain ⟨w, hw⟩ := IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop (hf.2 i)
      (f := g) x y hy.symm
    use i, (H i).isoPullback.inv.base w
    simpa [← Scheme.comp_base_apply]

end AlgebraicGeometry.Scheme
