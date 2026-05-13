/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
/-!

# Birationality and Rationality of schemes.

This file defines partial isomorphisms between schemes and uses them to formalize
birationality and rationality.

## Main definitions

- `Scheme.PartialIso X Y`: an isomorphism between a dense open subscheme of `X` and a
  dense open subscheme of `Y`.
- `Scheme.Birational X Y`: `X` and `Y` are birational, i.e. there exists a `PartialIso X Y`.
- `Scheme.BirationalOver S X Y`: `X` and `Y` are birational over `S`.
- `Scheme.IsRationalOver S X`: `X` is rational over `S`, i.e. birational over `S` to some
  affine space `𝔸(Fin n; S)`.

-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/-- A partial isomorphism from `X` to `Y` is an isomorphism between dense open subschemes
of `X` and `Y`. -/
structure PartialIso (X Y : Scheme.{u}) where
  /-- The source open subscheme of a partial isomorphism. -/
  source : X.Opens
  dense_source : Dense (source : Set X)
  /-- The target open subscheme of a partial isomorphism. -/
  target : Y.Opens
  dense_target : Dense (target : Set Y)
  /-- The underlying isomorphism of a partial isomorphism. -/
  iso : source.toScheme ≅ target.toScheme

namespace PartialIso

variable {X Y Z S : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}

lemma ext_iff (f g : X.PartialIso Y) :
    f = g ↔ ∃ (e : f.source = g.source) (e' : g.target = f.target),
      f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e' := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U₁, hU₁, U₂, hU₂, f⟩ := f
    obtain ⟨V₁, hV₁, V₂, hU₂, g⟩ := g
    simp only [forall_exists_index]
    rintro rfl rfl e
    simpa using e

@[ext]
lemma ext (f g : X.PartialIso Y) (e : f.source = g.source) (e' : g.target = f.target)
    (H : f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e') : f = g := by
  rw [ext_iff]
  exact ⟨e, e', H⟩

variable (X) in
/-- The identity partial isomorphism on `X`, defined on all of `X`. -/
@[simps]
def refl : X.PartialIso X where
  source := ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := Iso.refl _

/-- The inverse of a partial isomorphism. -/
@[symm, simps]
def symm (f : X.PartialIso Y) : Y.PartialIso X where
  source := f.target
  dense_source := f.dense_target
  target := f.source
  dense_target := f.dense_source
  iso := f.iso.symm

lemma isOver_symm (f : X.PartialIso Y) (hf : f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX) :
    f.symm.iso.hom ≫ f.symm.target.ι ≫ sX = f.symm.source.ι ≫ sY := by
  simpa [← cancel_epi f.iso.hom] using hf.symm

/-- Compose two partial isomorphisms along a proof that the target of `f` equals the source
of `g`. See `trans` for the version that does not require this. -/
@[simps]
noncomputable def trans' (f : X.PartialIso Y) (g : Y.PartialIso Z) (e : f.target = g.source) :
    X.PartialIso Z where
  source := f.source
  dense_source := f.dense_source
  target := g.target
  dense_target := g.dense_target
  iso := f.iso ≪≫ Y.isoOfEq e ≪≫ g.iso

lemma isOver_trans' (f : X.PartialIso Y) (g : Y.PartialIso Z) (e : f.target = g.source)
    (hf : f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX)
    (hg : g.iso.hom ≫ g.target.ι ≫ sZ = g.source.ι ≫ sY) :
    (trans' f g e).iso.hom ≫ (trans' f g e).target.ι ≫ sZ = (trans' f g e).source.ι ≫ sX := by
  simp [← hf, hg]

/-- Restrict the source of a partial isomorphism to a smaller dense open. -/
@[simps source target iso]
noncomputable def restrictSource (f : X.PartialIso Y) (U : Opens X) (hU : Dense (U : Set X))
    (hU' : U ≤ f.source) : X.PartialIso Y where
  source := U
  dense_source := hU
  target := f.target.ι ''ᵁ f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U
  dense_target :=
    have := PartialMap.Opens.isDominant_ι f.dense_target
    f.target.ι.denseRange.dense_image f.target.ι.continuous <|
      f.iso.hom.denseRange.dense_image f.iso.hom.continuous <|
        hU.preimage f.source.ι.isOpenEmbedding.isOpenMap
  iso := (Opens.isoOfLE hU').symm ≪≫
    (f.iso.hom.isoImage (f.source.ι ⁻¹ᵁ U)) ≪≫
    (f.target.ι.isoImage (f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U))

lemma isOver_restrictSource (f : X.PartialIso Y)
    (hf : f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX)
    (U : Opens X) (hU : Dense (U : Set X)) (hU' : U ≤ f.source) :
    (f.restrictSource U hU hU').iso.hom ≫ (f.restrictSource U hU hU').target.ι ≫ sY =
      (f.restrictSource U hU hU').source.ι ≫ sX := by
  simp [hf]

/-- Restrict the target of a partial isomorphism to a smaller dense open. -/
@[simps! source target iso]
noncomputable def restrictTarget (f : X.PartialIso Y) (U : Opens Y) (hU : Dense (U : Set Y))
    (hU' : U ≤ f.target) : X.PartialIso Y :=
  (f.symm.restrictSource U hU hU').symm

lemma isOver_restrictTarget (f : X.PartialIso Y)
    (hf : f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX) (U : Opens Y) (hU : Dense (U : Set Y))
    (hU' : U ≤ f.target) :
    (f.restrictTarget U hU hU').iso.hom ≫ (f.restrictTarget U hU hU').target.ι ≫ sY =
      (f.restrictTarget U hU hU').source.ι ≫ sX :=
  isOver_symm _ (isOver_restrictSource _ (isOver_symm f hf) U hU hU')

/-- Compose two partial isomorphisms, restricting to the intersection of the intermediate opens. -/
@[trans, simps! source target iso]
noncomputable def trans (f : X.PartialIso Y) (g : Y.PartialIso Z) : X.PartialIso Z :=
  have := f.dense_target.inter_of_isOpen_right g.dense_source g.source.2
  (f.restrictTarget _ this inf_le_left).trans' (g.restrictSource _ this inf_le_right) rfl

lemma isOver_trans (f : X.PartialIso Y) (g : Y.PartialIso Z)
    (hf : f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX)
    (hg : g.iso.hom ≫ g.target.ι ≫ sZ = g.source.ι ≫ sY) :
    (f.trans g).iso.hom ≫ (f.trans g).target.ι ≫ sZ = (f.trans g).source.ι ≫ sX :=
  isOver_trans' _ _ rfl (isOver_restrictTarget _ hf _ _ _) (isOver_restrictSource _ hg _ _ _)

/-- The underlying partial map of a partial isomorphism. -/
@[simps]
def toPartialMap (f : X.PartialIso Y) : X.PartialMap Y where
  domain := f.source
  dense_domain := f.dense_source
  hom := f.iso.hom ≫ f.target.ι

/-- The underlying rational map of a partial isomorphism. -/
abbrev toRationalMap (f : X.PartialIso Y) : X ⤏ Y := f.toPartialMap.toRationalMap

/-- A scheme isomorphism viewed as a partial isomorphism defined on all of `X` and `Y`. -/
@[simps]
noncomputable def _root_.CategoryTheory.Iso.toPartialIso (f : X ≅ Y) : X.PartialIso Y where
  source := ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := X.topIso ≪≫ f ≪≫ Y.topIso.symm

end PartialIso

/-- `X` and `Y` are birational if there exists a partial isomorphism between them. -/
def Birational (X Y : Scheme.{u}) : Prop := Nonempty (PartialIso X Y)

/-- Choose a partial isomorphism witnessing that `X` and `Y` are birational. -/
noncomputable def Birational.partialIso {X Y : Scheme.{u}} (h : Birational X Y) :
    PartialIso X Y :=
  Classical.choice h

@[refl]
lemma Birational.refl (X : Scheme.{u}) : Birational X X :=
  ⟨.refl X⟩

@[symm]
lemma Birational.symm {X Y : Scheme.{u}} (h : Birational X Y) : Birational Y X :=
  ⟨h.partialIso.symm⟩

@[trans]
lemma Birational.trans {X Y Z : Scheme.{u}} (h₁ : Birational X Y) (h₂ : Birational Y Z) :
    Birational X Z :=
  ⟨h₁.partialIso.trans h₂.partialIso⟩

/-- `X` and `Y` are birational over `S` if there exists a partial isomorphism between them
that is compatible with the structure maps to `S`. -/
def BirationalOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) : Prop :=
  ∃ f : PartialIso X Y, f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX

/-- Choose a partial isomorphism witnessing that `X` and `Y` are birational over `S`. -/
noncomputable def BirationalOver.partialIso {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (h : BirationalOver sX sY) :=
  h.choose

lemma BirationalOver.partialIso_isOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (h : BirationalOver sX sY) :
    h.partialIso.iso.hom ≫ h.partialIso.target.ι ≫ sY = h.partialIso.source.ι ≫ sX :=
  h.choose_spec

@[refl]
lemma BirationalOver.refl {S X : Scheme.{u}} (sX : X ⟶ S) : BirationalOver sX sX :=
  ⟨.refl X, by simp⟩

@[symm]
lemma BirationalOver.symm {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (h : BirationalOver sX sY) : BirationalOver sY sX :=
  ⟨h.partialIso.symm, PartialIso.isOver_symm _ h.partialIso_isOver⟩

@[trans]
lemma BirationalOver.trans {S X Y Z : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}
    (h₁ : BirationalOver sX sY) (h₂ : BirationalOver sY sZ) :
    BirationalOver sX sZ :=
  ⟨h₁.partialIso.trans h₂.partialIso,
    PartialIso.isOver_trans _ _ h₁.partialIso_isOver h₂.partialIso_isOver⟩

/-- `X` is rational over `S` (or `S`-rational) if it is birational over `S` to some
affine space `𝔸(n; S)`. -/
@[mk_iff]
class IsRationalOver {S X : Scheme.{u}} (sX : X ⟶ S) : Prop where
  exists_birationalOver_affineSpace' : ∃ (n : Type u), BirationalOver sX (𝔸(n; S) ↘ S)

lemma exists_birationalOver_affineSpace {S X : Scheme.{u}} (sX : X ⟶ S)
    [IsRationalOver sX] : ∃ (n : Type u), BirationalOver sX (𝔸(n; S) ↘ S) :=
  IsRationalOver.exists_birationalOver_affineSpace'

instance (S : Scheme.{u}) (n : Type u) : IsRationalOver (𝔸(n; S) ↘ S) where
  exists_birationalOver_affineSpace' := ⟨n, .refl _⟩

/-- If a scheme `X` is `S`-birational to an `S`-rational scheme `Y`, then `X` is `S`-rational. -/
lemma BirationalOver.isRationalOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsRationalOver sY] (h : BirationalOver sX sY) : IsRationalOver sX := by
  obtain ⟨n, hn⟩ := exists_birationalOver_affineSpace sY
  exact ⟨n, h.trans hn⟩

section DenseOpen

variable {X S : Scheme.{u}} (U : Opens X) (sX : X ⟶ S)

/-- A dense open set `U : Opens X` induces a partial isomorphism between `U` and `X`. -/
@[simps]
def Opens.partialIso_of_dense (hU : Dense (U : Set X)) : PartialIso U X where
  source := ⊤
  dense_source := dense_univ
  target := U
  dense_target := hU
  iso := U.toScheme.topIso

/-- A dense open set `U : Opens X` is birational to `X`. -/
lemma Opens.birational_of_dense (hU : Dense (U : Set X)) : Birational U X :=
  ⟨U.partialIso_of_dense hU⟩

/-- A dense open set `U : Opens X` of a scheme `X` over `S` is `S`-birational to `X`. -/
lemma Opens.birationalOver_of_dense (hU : Dense (U : Set X)) : BirationalOver (U.ι ≫ sX) sX :=
  ⟨U.partialIso_of_dense hU, by simp⟩

/-- A dense open set `U : Opens X` of a `S`-rational scheme `X` is `S`-rational. -/
lemma Opens.isRationalOver_of_dense (hU : Dense (U : Set X)) [IsRationalOver sX] :
    IsRationalOver (U.ι ≫ sX) := by
  obtain ⟨n, hn⟩ := exists_birationalOver_affineSpace sX
  exact ⟨n, (U.birationalOver_of_dense sX hU).trans hn⟩

end DenseOpen

section OpenImmersion

variable {X U S : Scheme.{u}} 

/-- A dominant open immersion `f : U ⟶ X` induced a partial isomorphism between `U` and `X`. -/
@[simps! source target iso]
noncomputable def Hom.partialIso (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] :=
  f.isoOpensRange.toPartialIso.trans' (f.opensRange.partialIso_of_dense f.denseRange) rfl

lemma Hom.birational (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] : Birational U X :=
  ⟨f.partialIso⟩

lemma Hom.birationalOver (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] (sX : X ⟶ S) (sU : U ⟶ S)
    (hf : f ≫ sX = sU) : BirationalOver sU sX :=
  ⟨f.partialIso, by simp [hf]⟩

end OpenImmersion

end Scheme

end AlgebraicGeometry
