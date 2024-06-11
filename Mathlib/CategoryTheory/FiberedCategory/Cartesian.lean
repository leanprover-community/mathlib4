/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Cartesian morphisms

This file defines cartesian resp. strongly cartesian morphisms in a based category.

## Main definitions
`IsCartesian p f φ` expresses that `φ` is a cartesian arrow lying over `f` with respect to `p` in
the sense of SGA 1 VI 5.1. This means that for any morphism `φ' : a' ⟶ b` lying over `f` there is
a unique morphism `τ : a' ⟶ a` lying over `𝟙 R`, such that `φ' = τ ≫ φ`.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

/-- The proposition that a morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is a
cartesian arrow, see SGA 1 VI 5.1. -/
class Functor.IsCartesian {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) extends
    IsHomLift p f φ : Prop where
  universal_property {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'

namespace Functor.IsCartesian

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsCartesian p f φ]

section

variable {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ']

/-- Given a cartesian arrow `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, a morphism `φ' : a' ⟶ b`
lifting `𝟙 R`, then `IsCartesian.map f φ φ'` is the morphism `a' ⟶ a` obtained from the universal
property of `φ`. -/
protected noncomputable def map : a' ⟶ a :=
  Classical.choose <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ'

instance map_isHomLift : IsHomLift p (𝟙 R) (IsCartesian.map p f φ φ') :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').1.1

@[reassoc (attr := simp)]
lemma fac : IsCartesian.map p f φ φ' ≫ φ = φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').1.2

/-- Given a cartesian arrow `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, a morphism `φ' : a' ⟶ b`
lifting `𝟙 R`, and a morphism `ψ : a' ⟶ a` such that `g ≫ ψ = φ'`. Then `ψ` is the map induced
by the universal property of `φ`. -/
lemma map_uniq (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') :
    ψ = IsCartesian.map p f φ φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').2
    ψ ⟨inferInstance, hψ⟩

/-- Given a cartesian arrow `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, a morphism `φ' : a' ⟶ b`
lifting `𝟙 R`, and two morphisms `ψ ψ' : a' ⟶ a` such that `g ≫ ψ = φ' = g ≫ ψ'`. Then we must
have `ψ = ψ'`. -/
lemma eq_of_fac {ψ ψ' : a' ⟶ a} [IsHomLift p (𝟙 R) ψ]
    [IsHomLift p (𝟙 R) ψ'] (hcomp : ψ ≫ φ = φ') (hcomp' : ψ' ≫ φ = φ') : ψ = ψ' := by
  rw [map_uniq p f φ φ' ψ hcomp, map_uniq p f φ φ' ψ' hcomp']

end

@[simp]
lemma map_self : IsCartesian.map p f φ φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]

/-- The canonical isomorphism between the domains of two cartesian arrows
lying over the same object. -/
@[simps]
noncomputable def domainUniqueUpToIso {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] : a' ≅ a where
  hom := IsCartesian.map p f φ φ'
  inv := IsCartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ'
    apply eq_of_fac p (p.map φ') φ' φ' (by simp) (id_comp _)
  inv_hom_id := by
    subst_hom_lift p f φ
    apply eq_of_fac p (p.map φ) φ φ (by simp) (id_comp _)

/-- Precomposing a cartesian morphism with an isomorphism lifting the identity is cartesian. -/
instance of_iso_comp {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom] :
    IsCartesian p f (φ'.hom ≫ φ) where
  universal_property := by
    intro c ψ hψ
    use IsCartesian.map p f φ ψ ≫ φ'.inv
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_comp_inv]
    apply map_uniq
    simp only [assoc, hτ₂]

/-- Postcomposing a cartesian morphism with an isomorphism lifting the identity is cartesian. -/
instance of_comp_iso {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom] :
    IsCartesian p f (φ ≫ φ'.hom) where
  universal_property := by
    intro c ψ hψ
    use IsCartesian.map p f φ (ψ ≫ φ'.inv)
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    simp only [Iso.eq_comp_inv, assoc, hτ₂]

end Functor.IsCartesian
