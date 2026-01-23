/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# (2,1)-categories

A bicategory `B` is said to be locally groupoidal (or a (2,1)-category) if for every pair
of objects `x, y`, the Hom-category `x ⟶ y` is a groupoid (which is expressed using the
`CategoryTheory.IsGroupoid` typeclass).

Given a bicategory `B`, we construct a bicategory `Pith B` which is obtained from `B`
by discarding non-invertible 2-morphisms. This is realized in practice by applying
`Core` to each hom-category of `C`. By construction, `Pith B` is a (2,1)-category,
and for every (2,1)-category B', every pseudofunctor `B' ⥤ B` factors (essentially) uniquely
through the inclusion from `Pith B` to `B` (see
`CategoryTheory.Bicategory.Pith.pseudofunctorToPith`).

## References
- [Kerodon, section 1.2.2](https://kerodon.net/tag/02GD).

-/

@[expose] public section

namespace CategoryTheory.Bicategory

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

/-- A bicategory is locally groupoidal if the categories of 1-morphisms are groupoids. -/
@[kerodon 009Q]
abbrev IsLocallyGroupoid (B : Type u₁) [Bicategory.{w₁, v₁} B] := ∀ (b c : B), IsGroupoid (b ⟶ c)

/-- Given a bicategory `B`, `Pith B` is the bicategory obtained by discarding the non-invertible
2-cells from `B`. We implement this as a wrapper type for `B`, and use `CategoryTheory.Core`
to discard the non-invertible morphisms. -/
@[kerodon 00AL]
structure Pith (B : Type u₁) where
  /-- The underlying object of the bicategory. -/
  as : B

namespace Pith

variable (B : Type u₁)

theorem mk_as (b : Pith B) : mk b.as = b := rfl

instance [Inhabited B] : Inhabited (Pith B) := ⟨⟨default⟩⟩

instance categoryStruct [Bicategory.{w₁, v₁} B] : CategoryStruct (Pith B) where
  Hom a b := Core (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.of ≫ g.of⟩

variable [Bicategory.{w₁, v₁} B]

-- @[simps!] in categoryStruct puts `Core (a.as ⟶ b.as)` in the hyps for the next two
-- lemmas, so we record them manually instead.
@[simp]
lemma id_of (a : Pith B) : (𝟙 a : a ⟶ a).of = 𝟙 a.as := rfl

@[simp]
lemma comp_of {a b c : Pith B} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).of = f.of ≫ g.of := rfl

instance homGroupoid (a b : Pith B) :
    Groupoid.{w₁} (a ⟶ b) := inferInstanceAs <| Groupoid <| Core _

@[ext]
lemma hom₂_ext {a b : Pith B} {x y : a ⟶ b} {f g : x ⟶ y} (h : f.iso.hom = g.iso.hom) :
    f = g := CoreHom.ext <| Iso.ext h

@[simp, reassoc]
lemma comp₂_iso_hom {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z} :
    (f ≫ g).iso.hom = f.iso.hom ≫ g.iso.hom := rfl

@[simp, reassoc]
lemma comp₂_iso_inv {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z} :
    (f ≫ g).iso.inv = g.iso.inv ≫ f.iso.inv := rfl

@[simp]
lemma id₂_iso_hom {a b : Pith B} {x : a ⟶ b} : (𝟙 x : x ⟶ x).iso.hom = 𝟙 _ := rfl

@[simp]
lemma id₂_iso_inv {a b : Pith B} {x : a ⟶ b} : (𝟙 x : x ⟶ x).iso.inv = 𝟙 _ := rfl

@[simps! whiskerLeft_iso_hom whiskerLeft_iso_inv whiskerRight_iso_hom whiskerRight_iso_inv
associator_hom_iso associator_inv_iso_hom associator_inv_iso_inv leftUnitor_hom_iso
leftUnitor_inv_iso_hom rightUnitor_hom_iso rightUnitor_inv_iso_hom rightUnitor_inv_iso_inv]
instance : Bicategory.{w₁, v₁} (Pith B) where
  whiskerLeft x _ _ f := CoreHom.mk <| whiskerLeftIso x.of (CoreHom.iso f)
  whiskerRight f y := CoreHom.mk <| whiskerRightIso (CoreHom.iso f) y.of
  leftUnitor x := Core.isoMk <| leftUnitor x.of
  rightUnitor x := Core.isoMk <| rightUnitor x.of
  associator x y z := Core.isoMk <| associator x.of y.of z.of
  whisker_exchange η θ := by
    ext
    simp [whisker_exchange]

/-- The pith is a (2,1)-category. -/
example : IsLocallyGroupoid (Pith B) := by infer_instance

/-- The canonical inclusion from the pith of `B` to `B`, as a Pseudofunctor. -/
@[simps]
def inclusion : Pseudofunctor (Pith B) B where
  obj x := x.as
  map f := f.of
  map₂ η := η.iso.hom
  mapId _ := .refl _
  mapComp _ _ := .refl _

variable {B} in
/-- Any pseudofunctor from a (2,1)-category to a bicategory factors through
the pith of the target bicategory. -/
@[simps!]
noncomputable def pseudofunctorToPith {B' : Type u₂} [Bicategory.{w₂, v₂} B']
    [IsLocallyGroupoid B'] (F : Pseudofunctor B' B) :
    Pseudofunctor B' (Pith B) where
  obj x := .mk <| F.obj x
  map f := .mk <| F.map f
  map₂ f := .mk <| asIso <| F.map₂ f
  mapId x := Core.isoMk <| F.mapId x
  mapComp f g := Core.isoMk <| F.mapComp f g

section

variable {B} {B' : Type u₂} [Bicategory.{w₂, v₂} B'] [IsLocallyGroupoid B'] (F : Pseudofunctor B' B)

/-- The hom direction of the (strong) natural isomorphism of pseudofunctors
between `(pseudofunctorToPith F).comp (inclusion B)` and `F`. -/
noncomputable def pseudofunctorToPithCompInclusionStrongIsoHom :
    ((pseudofunctorToPith F).comp (inclusion B)).StrongTrans F where
  app b' := 𝟙 _
  naturality f := (ρ_ _) ≪≫ (λ_ _).symm

/-- The inv direction of the (strong) natural isomorphism of pseudofunctors
between `(pseudofunctorToPith F).comp (inclusion B)` and `F`. -/
noncomputable def pseudofunctorToPithCompInclusionStrongIsoInv :
    F.StrongTrans ((pseudofunctorToPith F).comp (inclusion B)) where
  app b' := 𝟙 _
  naturality f := (ρ_ _) ≪≫ (λ_ _).symm

end

end Pith

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]

/-- If `B` is a (2,1)-category, then every lax functor `F` from a bicategory to `B` defines a
`CategoryTheory.LaxFunctor.PseudoCore` structure on `F` that can be used to promote `F` to a
pseudofunctor using `CategoryTheory.Pseudofunctor.mkOfLax`. -/
@[simps!]
noncomputable def Pseudofunctor.ofLaxFunctorToLocallyGroupoid
    {B' : Type u₂} [Bicategory.{w₂, v₂} B'] [IsLocallyGroupoid B] (F : LaxFunctor B' B) :
    F.PseudoCore where
  mapIdIso x := (asIso (F.mapId x)).symm
  mapCompIso f g := (asIso <| F.mapComp f g).symm

/-- If `B` is a (2,1)-category, then every oplax functor `F` from a bicategory to `B` defines
a `CategoryTheory.OplaxFunctor.PseudoCore` structure on `F` that can be used to promote `F`
to a pseudofunctor using `CategoryTheory.Pseudofunctor.mkOfOplax`. -/
@[simps!]
noncomputable def Pseudofunctor.ofOplaxFunctorToLocallyGroupoid
    {B' : Type u₂} [Bicategory.{w₂, v₂} B'] [IsLocallyGroupoid B] (F : OplaxFunctor B' B) :
    F.PseudoCore where
  mapIdIso x := asIso (F.mapId x)
  mapCompIso f g := asIso (F.mapComp f g)

end CategoryTheory.Bicategory
