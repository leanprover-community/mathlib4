/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou, Adam Topaz
-/
import Mathlib.AlgebraicGeometry.Pullbacks
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

namespace AlgebraicGeometry.Scheme

variable (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.RespectsIso]
  [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]

/--
The pretopology on the category of schemes defined by covering families where the components
satisfy `P`.

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

/-- The Grothendieck topology on the category of schemes induced by the pretopology defined by
`P`-covers. -/
abbrev grothendieckTopology : GrothendieckTopology Scheme.{u} :=
  (pretopology P).toGrothendieck

/-- The pretopology on the category of schemes defined by jointly surjective families.

Note: The assumption `IsJointlySurjectivePreserving ⊤` is mathematically unneeded, and only here
to reduce imports. To satisfy it, use `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`. -/
def jointlySurjectivePretopology [IsJointlySurjectivePreserving ⊤] : Pretopology Scheme.{u} where
  coverings X S :=
    ∀ x : X, ∃ (Y : Scheme.{u}) (y : Y) (f : Y ⟶ X) (hf : S f), f.base y = x
  has_isos X Y f hf x := by
    use Y, (inv f).base x, f
    simp [← Scheme.comp_base_apply]
  pullbacks X Y f S hS x := by
    obtain ⟨Z, z, g, hg, hz⟩ := hS (f.base x)
    obtain ⟨w, hw⟩ :=
      IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop (P := ⊤) trivial z x hz
    use pullback g f, w, pullback.snd g f
    simpa [hw] using Presieve.pullbackArrows.mk Z g hg
  transitive X S T hS hT x := by
    obtain ⟨Y, y, f, hf, hy⟩ := hS x
    obtain ⟨Z, z, g, hg, hz⟩ := hT f hf y
    use Z, z, g ≫ f
    simpa [hz, hy] using Presieve.bind_comp f hf hg

@[deprecated (since := "2025-08-18")] alias surjectiveFamiliesPretopology :=
  jointlySurjectivePretopology

/-- The jointly surjective topology on `Scheme` is defined by the same condition as the jointly
surjective pretopology. -/
def jointlySurjectiveTopology [IsJointlySurjectivePreserving ⊤] :
    GrothendieckTopology Scheme.{u} :=
  jointlySurjectivePretopology.toGrothendieck.copy (fun X s ↦ jointlySurjectivePretopology X ↑s) <|
    funext fun _ ↦ Set.ext fun s ↦
      ⟨fun ⟨_, hp, hps⟩ x ↦ let ⟨Y, y, u, hu, hyx⟩ := hp x; ⟨Y, y, u, hps _ hu, hyx⟩,
      fun hs ↦ ⟨s, hs, le_rfl⟩⟩

theorem mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology
    [IsJointlySurjectivePreserving ⊤] {X : Scheme.{u}} {s : Sieve X} :
    s ∈ jointlySurjectiveTopology X ↔ jointlySurjectivePretopology X ↑s :=
  Iff.rfl

lemma jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology
    [IsJointlySurjectivePreserving ⊤] :
    jointlySurjectiveTopology.{u} = jointlySurjectivePretopology.toGrothendieck :=
  GrothendieckTopology.copy_eq

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
