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

-/

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

namespace Scheme

/-- A morphism property of schemes is said to preserve joint surjectivity, if
for any pair of morphisms `f : X ⟶ S` and `g : Y ⟶ S` where `g` satisfies `P`,
any pair of points `x : X` and `y : Y` with `f x = g y` can be lifted to a point
of `X ×[S] Y`.

The coverings are defined via existence of a `P`-cover. This is convenient in practice, as one
directly has the cover available. For a pretopology generating the same Grothendieck topology, see
`AlgebraicGeometry.Scheme.grothendieckTopology_eq_inf`.
-/
def pretopology : Pretopology Scheme.{u} where
  coverings Y S := ∃ (U : Cover.{u} P Y), S = Presieve.ofArrows U.X U.f
  has_isos _ _ f _ := ⟨coverOfIsIso f, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨U, rfl⟩
    exact ⟨U.pullbackCover' f, (Presieve.ofArrows_pullback _ _ _).symm⟩
  transitive := by
    rintro X _ T ⟨U, rfl⟩ H
    choose V hV using H
    use U.bind (fun j => V (U.f j) ⟨j⟩)
    simpa only [Cover.bind, ← hV] using Presieve.ofArrows_bind U.X U.f _
      (fun _ f H => (V f H).X) (fun _ f H => (V f H).f)

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

/-- The precoverage on `Scheme` defined by jointly surjective families. -/
def jointlySurjectivePrecoverage : Precoverage Scheme.{u} where
  coverings X R := ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), R f ∧ x ∈ Set.range f.base

instance : jointlySurjectivePrecoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg x := by
    obtain ⟨-, -, ⟨i⟩, w, hw⟩ := hf x
    obtain ⟨-, -, ⟨j⟩, z, hz⟩ := (hg i) w
    clear Y; clear Y
    use Y i j, g i j ≫ f i, .mk (Sigma.mk i j), z
    simp [hz, hw]

instance : jointlySurjectivePrecoverage.HasIsos where
  mem_coverings_of_isIso {S T} f hf x := by
    use S, f, ⟨⟩, (inv f).base x
    simp [← Scheme.comp_base_apply]

variable (P : MorphismProperty Scheme.{u})

/-- The precoverage on `Scheme` induced by `P` is given by jointly surjective families of
`P`-morphisms. -/
def precoverage : Precoverage Scheme.{u} :=
  jointlySurjectivePrecoverage ⊓ P.precoverage

@[simp]
lemma ofArrows_mem_precoverage_iff {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} :
    .ofArrows X f ∈ precoverage P S ↔ (∀ x, ∃ i, x ∈ Set.range (f i).base) ∧ ∀ i, P (f i) := by
  refine ⟨fun hmem ↦ ⟨fun x ↦ ?_, fun i ↦ hmem.2 ⟨i⟩⟩,
      fun h ↦ ⟨fun x ↦ ?_, fun {Y} g ⟨i⟩ ↦ h.2 i⟩⟩
  · obtain ⟨Y, g, ⟨i⟩, hrange⟩ := hmem.1 x
    use i
  · obtain ⟨i, h⟩ := h.1 x
    use X i, f i, ⟨i⟩

instance [P.IsStableUnderComposition] : (precoverage P).IsStableUnderComposition := by
  dsimp only [precoverage]; infer_instance

lemma pretopology_le_inf [IsJointlySurjectivePreserving ⊤] :
    pretopology P ≤ jointlySurjectivePretopology ⊓ P.pretopology := by
  rintro X S ⟨𝒰, rfl⟩
  refine ⟨fun x ↦ ?_, fun _ _ ⟨i⟩ ↦ 𝒰.map_prop i⟩
  obtain ⟨a, ha⟩ := 𝒰.covers x
  refine ⟨𝒰.X (𝒰.idx x), a, 𝒰.f (𝒰.idx x), ⟨_⟩, ha⟩

/--
The Grothendieck topology defined by `P`-covers agrees with the Grothendieck
topology induced by the intersection of the pretopology of surjective families with
the pretopology defined by `P`.

Note: Because of size issues, this does not hold on the level of pretopologies: A presieve
in the intersection can have up to `Type (u + 1)` many components, while in the definition
of `AlgebraicGeometry.Scheme.pretopology` we only allow `Type u` many components.
-/
lemma grothendieckTopology_eq_inf [IsJointlySurjectivePreserving ⊤] :
    grothendieckTopology P = (jointlySurjectivePretopology ⊓ P.pretopology).toGrothendieck := by
  apply le_antisymm ((Pretopology.gi Scheme.{u}).gc.monotone_l (pretopology_le_inf P))
  intro X S ⟨T, ⟨hs, hP⟩, hle⟩
  let _ : Type (u + 1) := Presieve X
  let J := (Y : Scheme.{u}) × (Y ⟶ X)
  choose Y y f hf hy using hs
  let 𝒰 : Cover.{u} P X :=
    { I₀ := X
      X := Y
      f := f
      idx := id
      covers := fun x ↦ ⟨y x, hy x⟩
      map_prop := fun x ↦ hP (hf x)
    }
  refine ⟨Presieve.ofArrows 𝒰.X 𝒰.f, ⟨𝒰, rfl⟩, ?_⟩
  rintro Z g ⟨x⟩
  exact hle _ (hf x)

variable {P}

lemma pretopology_cover {Y : Scheme.{u}} (𝒰 : Cover.{u} P Y) :
    pretopology P Y (Presieve.ofArrows 𝒰.X 𝒰.f) :=
  ⟨𝒰, rfl⟩

lemma grothendieckTopology_cover {X : Scheme.{u}} (𝒰 : Cover.{v} P X) :
    grothendieckTopology P X (Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f)) := by
  let 𝒱 : Cover.{u} P X :=
    { I₀ := X
      X := fun x ↦ 𝒰.X (𝒰.idx x)
      f := fun x ↦ 𝒰.f (𝒰.idx x)
      idx := id
      covers := 𝒰.covers
      map_prop := fun _ ↦ 𝒰.map_prop _
    }
  refine ⟨_, pretopology_cover 𝒱, ?_⟩
  rintro _ _ ⟨y⟩
  exact ⟨_, 𝟙 _, 𝒰.f (𝒰.idx y), ⟨_⟩, by simp [𝒱]⟩

section

variable {Q : MorphismProperty Scheme.{u}} [Q.IsMultiplicative] [Q.RespectsIso]
  [Q.IsStableUnderBaseChange] [IsJointlySurjectivePreserving Q]

lemma pretopology_le_pretopology (hPQ : P ≤ Q) :
    pretopology P ≤ pretopology Q := by
  rintro X - ⟨𝒰, rfl⟩
  use 𝒰.changeProp Q (fun j ↦ hPQ _ (𝒰.map_prop j))
  rfl

lemma grothendieckTopology_le_grothendieckTopology (hPQ : P ≤ Q) :
    grothendieckTopology P ≤ grothendieckTopology Q :=
  (Pretopology.gi Scheme.{u}).gc.monotone_l (pretopology_le_pretopology hPQ)

end

end AlgebraicGeometry.Scheme
