/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types

/-!
# The colimit type of a functor to types

Given a category `J` (with `J : Type u` and `[Category.{v} J]`) and
a functor `F : J ⥤ Type w₀`, we introduce a type `F.ColimitType : Type (max u w₀)`,
which satisfies a certain universal property of the colimit: it is defined
as a suitable quotient of `Σ j, F.obj j`. This universal property is not
expressed in a categorical way (as in general `Type (max u w₀)`
is not the same as `Type u`).

We also introduce a notion of cocone of `F : J ⥤ Type w₀`, this is `F.CoconeTypes`,
or more precisely `Functor.CoconeTypes.{w₁} F`, which consists of a candidate
colimit type for `F` which is in `Type w₁` (in case `w₁ = w₀`, we shall show
this is the same as the data of `c : Cocone F` in the categorical sense).
Given `c : F.CoconeTypes`, we also introduce a property `c.IsColimit` which says
that the canonical map `F.ColimitType → c.pt` is a bijection, and we shall show (TODO)
that when `w₁ = w₀`, it is equivalent to saying that the corresponding cocone
in a categorical sense is a colimit.

## TODO
* refactor `DirectedSystem` and the construction of colimits in `Type`
  by using `Functor.ColimitType`.
* add a similar API for limits in `Type`?

-/

universe w₃ w₂ w₁ w₀ w₀' v u

assert_not_exists CategoryTheory.Limits.Cocone

namespace CategoryTheory

variable {J : Type u} [Category.{v} J]

namespace Functor

variable (F : J ⥤ Type w₀)

/-- Given a functor `F : J ⥤ Type w₀`, this is a "cocone" of `F` where
we allow the point `pt` to be in a different universe than `w`. -/
structure CoconeTypes where
  /-- the point of the cocone -/
  pt : Type w₁
  /-- a family of maps to `pt` -/
  ι (j : J) : F.obj j → pt
  ι_naturality {j j' : J} (f : j ⟶ j') :
      (ι j').comp (F.map f) = ι j := by aesop

namespace CoconeTypes

attribute [simp] ι_naturality

variable {F}

@[simp]
lemma ι_naturality_apply (c : CoconeTypes.{w₁} F) {j j' : J} (f : j ⟶ j') (x : F.obj j) :
    c.ι j' (F.map f x) = c.ι j x :=
  congr_fun (c.ι_naturality f) x

/-- Given `c : F.CoconeTypes` and a map `φ : c.pt → T`, this is
the cocone for `F` obtained by postcomposition with `φ`. -/
@[simps -fullyApplied]
def postcomp (c : CoconeTypes.{w₁} F) {T : Type w₂} (φ : c.pt → T) :
    F.CoconeTypes where
  pt := T
  ι j := φ.comp (c.ι j)

/-- The cocone for `G : J ⥤ Type w₀'` that is deduced from a cocone for `F : J ⥤ Type w₀`
and a natural map `G.obj j → F.obj j` for all `j : J`. -/
@[simps -fullyApplied]
def precompose (c : CoconeTypes.{w₁} F) {G : J ⥤ Type w₀'} (app : ∀ j, G.obj j → F.obj j)
    (naturality : ∀ {j j'} (f : j ⟶ j'), app j' ∘ G.map f = F.map f ∘ app j) :
    CoconeTypes.{w₁} G where
  pt := c.pt
  ι j := c.ι j ∘ app j
  ι_naturality f := by
    rw [Function.comp_assoc, naturality, ← Function.comp_assoc, ι_naturality]

end CoconeTypes

/-- Given `F : J ⥤ Type w₀`, this is the relation `Σ j, F.obj j` which
generates an equivalence relation such that the quotient identifies
to the colimit type of `F`. -/
def ColimitTypeRel : (Σ j, F.obj j) → (Σ j, F.obj j) → Prop :=
  fun p p' ↦ ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2

/-- The colimit type of a functor `F : J ⥤ Type w₀`. (It may not
be in `Type w₀`.) -/
def ColimitType : Type (max u w₀) := Quot F.ColimitTypeRel

/-- The canonical maps `F.obj j → F.ColimitType`. -/
def ιColimitType (j : J) (x : F.obj j) : F.ColimitType :=
  Quot.mk _ ⟨j, x⟩

lemma ιColimitType_eq_iff {j j' : J} (x : F.obj j) (y : F.obj j') :
    F.ιColimitType j x = F.ιColimitType j' y ↔
      Relation.EqvGen F.ColimitTypeRel ⟨j, x⟩ ⟨ j', y⟩ :=
  Quot.eq

lemma ιColimitType_jointly_surjective (t : F.ColimitType) :
    ∃ j x, F.ιColimitType j x = t := by
  obtain ⟨_, _⟩ := t
  exact ⟨_, _, rfl⟩

@[simp]
lemma ιColimitType_map {j j' : J} (f : j ⟶ j') (x : F.obj j) :
    F.ιColimitType j' (F.map f x) = F.ιColimitType j x :=
  (Quot.sound ⟨f, rfl⟩).symm

/-- The cocone corresponding to `F.ColimitType`. -/
@[simps -fullyApplied]
def coconeTypes : F.CoconeTypes where
  pt := F.ColimitType
  ι j := F.ιColimitType j

/-- An heterogeneous universe version of the universal property of the colimit is
satisfied by `F.ColimitType` together the maps `F.ιColimitType j`. -/
def descColimitType (c : F.CoconeTypes) : F.ColimitType → c.pt :=
  Quot.lift (fun ⟨j, x⟩ ↦ c.ι j x) (by rintro _ _ ⟨_, _⟩; aesop)

@[simp]
lemma descColimitType_comp_ι (c : F.CoconeTypes) (j : J) :
    (F.descColimitType c).comp (F.ιColimitType j) = c.ι j := rfl

@[simp]
lemma descColimitType_ιColimitType_apply (c : F.CoconeTypes) (j : J) (x : F.obj j) :
    F.descColimitType c (F.ιColimitType j x) = c.ι j x := rfl

namespace CoconeTypes

variable {F} (c : CoconeTypes.{w₁} F)

lemma descColimitType_surjective_iff :
    Function.Surjective (F.descColimitType c) ↔
      ∀ (z : c.pt), ∃ (i : J) (x : F.obj i), c.ι i x = z := by
  constructor
  · intro h z
    obtain ⟨⟨i, x⟩, rfl⟩ := h z
    exact ⟨i, x, rfl⟩
  · intro h z
    obtain ⟨i, x, rfl⟩ := h z
    exact ⟨F.ιColimitType i x, rfl⟩

/-- Given `F : J ⥤ Type w₀` and `c : F.CoconeTypes`, this is the property
that `c` is a colimit. It is defined by saying the canonical map
`F.descColimitType c : F.ColimitType → c.pt` is a bijection. -/
structure IsColimit : Prop where
  bijective : Function.Bijective (F.descColimitType c)

namespace IsColimit

variable {c} (hc : c.IsColimit)

include hc

/-- Given `F : J ⥤ Type w₀`, and `c : F.CoconeTypes` a cocone that is colimit,
this is the equivalence `F.ColimitType ≃ c.pt`. -/
@[simps! apply]
noncomputable def equiv : F.ColimitType ≃ c.pt :=
  Equiv.ofBijective _ hc.bijective

@[simp]
lemma equiv_symm_ι_apply (j : J) (x : F.obj j) :
    hc.equiv.symm (c.ι j x) = F.ιColimitType j x :=
  hc.equiv.injective (by simp)

lemma ι_jointly_surjective (y : c.pt) :
    ∃ j x, c.ι j x = y := by
  obtain ⟨z, rfl⟩ := hc.equiv.surjective y
  obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective z
  exact ⟨j, x, rfl⟩

lemma funext {T : Type w₂} {f g : c.pt → T}
    (h : ∀ j, f.comp (c.ι j) = g.comp (c.ι j)) : f = g := by
  funext y
  obtain ⟨j, x, rfl⟩ := hc.ι_jointly_surjective y
  exact congr_fun (h j) x

lemma exists_desc (c' : CoconeTypes.{w₂} F) :
    ∃ (f : c.pt → c'.pt), ∀ (j : J), f.comp (c.ι j) = c'.ι j :=
  ⟨(F.descColimitType c').comp hc.equiv.symm, by aesop⟩

/-- If `F : J ⥤ Type w₀` and `c : F.CoconeTypes` is colimit, then
`c` satisfies a heterogeneous universe version of the universal
property of colimits. -/
noncomputable def desc (c' : CoconeTypes.{w₂} F) : c.pt → c'.pt :=
  (hc.exists_desc c').choose

@[simp]
lemma fac (c' : CoconeTypes.{w₂} F) (j : J) :
    (hc.desc c').comp (c.ι j) = c'.ι j :=
  (hc.exists_desc c').choose_spec j

@[simp]
lemma fac_apply (c' : CoconeTypes.{w₂} F) (j : J) (x : F.obj j) :
    hc.desc c' (c.ι j x) = c'.ι j x :=
  congr_fun (hc.fac c' j) x

lemma of_equiv {c' : CoconeTypes.{w₂} F} (e : c.pt ≃ c'.pt)
    (he : ∀ j x, c'.ι j x = e (c.ι j x)) : c'.IsColimit where
  bijective := by
    convert Function.Bijective.comp e.bijective hc.bijective
    ext y
    obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
    aesop

end IsColimit

/-- Structure which expresses that `c : F.CoconeTypes`
satisfies the universal property of the colimit of types:
compatible families of maps `F.obj j → T` (where `T`
is any type in a specified universe) descend in a unique
way as maps `c.pt → T`. -/
structure IsColimitCore where
  /-- any cocone descends (in a unique way) as a map -/
  desc (c' : CoconeTypes.{w₂} F) : c.pt → c'.pt
  fac (c' : CoconeTypes.{w₂} F) (j : J) :
    (desc c').comp (c.ι j) = c'.ι j := by aesop
  funext {T : Type w₂} {f g : c.pt → T}
    (h : ∀ j, f.comp (c.ι j) = g.comp (c.ι j)) : f = g

namespace IsColimitCore

attribute [simp] fac

variable {c}

@[simp]
lemma fac_apply (hc : IsColimitCore.{w₂} c)
    (c' : CoconeTypes.{w₂} F) (j : J) (x : F.obj j) :
    hc.desc c' (c.ι j x) = c'.ι j x :=
  congr_fun (hc.fac c' j) x

/-- Any structure `IsColimitCore.{max w₂ w₃} c` can be
lowered to `IsColimitCore.{w₂} c` -/
def down (hc : IsColimitCore.{max w₂ w₃} c) :
    IsColimitCore.{w₂} c where
  desc c' := Equiv.ulift.toFun.comp
    (hc.desc (c'.postcomp Equiv.ulift.{w₃}.symm))
  fac c' j := by
    rw [Function.comp_assoc, hc.fac]
    rfl
  funext {T f g} h := by
    suffices Equiv.ulift.{w₃}.invFun.comp f =
        Equiv.ulift.invFun.comp g by
      ext x
      simpa using congr_fun this x
    exact hc.funext (fun j ↦ by simp [Function.comp_assoc, h])

/-- A colimit cocone for `F : J ⥤ Type w₀` induces a colimit cocone
for `G : J ⥤ Type w₉'` when we have a natural equivalence `G.obj j ≃ F.obj j`
for all `j : J`. -/
def precompose (hc : IsColimitCore.{w₂} c)
    {G : J ⥤ Type w₀'} (e : ∀ j, G.obj j ≃ F.obj j)
    (naturality : ∀ {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j) :
    IsColimitCore.{w₂} (c.precompose _ naturality) where
  desc c' := hc.desc (c'.precompose _ (FunctorToTypes.naturality_symm e naturality))
  fac c' j := by
    rw [precompose_ι, ← Function.comp_assoc, hc.fac, precompose_ι, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id]
  funext {T f g} h := hc.funext (fun j ↦ by
    ext x
    obtain ⟨y, rfl⟩ := (e j).surjective x
    exact congr_fun (h j) y)

end IsColimitCore

variable {c} in
/-- When `c : F.CoconeTypes` satisfies the property
`c.IsColimit`, this is a term in `IsColimitCore.{w₂} c`
for any universe `w₂`. -/
@[simps]
noncomputable def IsColimit.isColimitCore (hc : c.IsColimit) :
    IsColimitCore.{w₂} c where
  desc := hc.desc
  funext := hc.funext

lemma IsColimitCore.isColimit (hc : IsColimitCore.{max u w₀ w₁} c) :
    c.IsColimit where
  bijective := by
    let e : F.ColimitType ≃ c.pt :=
      { toFun := F.descColimitType c
        invFun := (down.{max u w₁} hc).desc F.coconeTypes
        left_inv y := by
          obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
          simp
        right_inv := by
          have : (F.descColimitType c).comp
              ((down.{max u w₁} hc).desc F.coconeTypes) = id :=
            (down.{max u w₀} hc).funext (fun j ↦ by
              rw [Function.id_comp, Function.comp_assoc, fac,
                coconeTypes_ι, descColimitType_comp_ι])
          exact congr_fun this }
    exact e.bijective

variable {c} in
lemma IsColimit.precompose (hc : c.IsColimit) {G : J ⥤ Type w₀'} (e : ∀ j, G.obj j ≃ F.obj j)
    (naturality : ∀ {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j) :
    (c.precompose _ naturality).IsColimit :=
  (hc.isColimitCore.precompose e naturality).isColimit

lemma isColimit_precompose_iff {G : J ⥤ Type w₀'} (e : ∀ j, G.obj j ≃ F.obj j)
    (naturality : ∀ {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j) :
    (c.precompose _ naturality).IsColimit ↔ c.IsColimit :=
  ⟨fun hc ↦ (hc.precompose (fun j ↦ (e j).symm)
      (FunctorToTypes.naturality_symm e naturality)).of_equiv (Equiv.refl _) (by simp),
    fun hc ↦ hc.precompose e naturality⟩

end CoconeTypes

lemma isColimit_coconeTypes : F.coconeTypes.IsColimit where
  bijective := by
    convert Function.bijective_id
    ext y
    obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
    rfl

end Functor

end CategoryTheory
