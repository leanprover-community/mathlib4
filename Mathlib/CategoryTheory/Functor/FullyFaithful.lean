/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.NatIso
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic

#align_import category_theory.functor.fully_faithful from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Full and faithful functors

We define typeclasses `Full` and `Faithful`, decorating functors.

## Main definitions and results
* Use `F.map_injective` to retrieve the fact that `F.map` is injective when `[Faithful F]`.
* Similarly, `F.map_surjective` states that `F.map` is surjective when `[Full F]`.
* Use `F.preimage` to obtain preimages of morphisms when `[Full F]`.
* We prove some basic "cancellation" lemmas for full and/or faithful functors, as well as a
  construction for "dividing" a functor by a faithful functor, see `Faithful.div`.
* `Full F` carries data, so definitional properties of the preimage can be used when using
  `F.preimage`. To obtain an instance of `Full F` non-constructively, you can use `fullOfExists`
  and `fullOfSurjective`.

See `CategoryTheory.Equivalence.of_fullyFaithful_ess_surj` for the fact that a functor is an
equivalence if and only if it is fully faithful and essentially surjective.

-/


-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor `F : C ⥤ D` is full if for each `X Y : C`, `F.map` is surjective.
In fact, we use a constructive definition, so the `Full F` typeclass contains data,
specifying a particular preimage of each `f : F.obj X ⟶ F.obj Y`.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class Full (F : C ⥤ D) where
  /-- The data of a preimage for every `f : F.obj X ⟶ F.obj Y`. -/
  preimage : ∀ {X Y : C} (_ : F.obj X ⟶ F.obj Y), X ⟶ Y
  /-- The property that `Full.preimage f` of maps to `f` via `F.map`. -/
  witness : ∀ {X Y : C} (f : F.obj X ⟶ F.obj Y), F.map (preimage f) = f := by aesop_cat
#align category_theory.full CategoryTheory.Full
#align category_theory.full.witness CategoryTheory.Full.witness

attribute [simp] Full.witness


/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4:
#[`map_injective'] [] -/
/-- A functor `F : C ⥤ D` is faithful if for each `X Y : C`, `F.map` is injective.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class Faithful (F : C ⥤ D) : Prop where
  /-- `F.map` is injective for each `X Y : C`. -/
  map_injective : ∀ {X Y : C}, Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
    aesop_cat
#align category_theory.faithful CategoryTheory.Faithful
#align category_theory.faithful.map_injective CategoryTheory.Faithful.map_injective

namespace Functor

variable {X Y : C}

theorem map_injective (F : C ⥤ D) [Faithful F] :
    Function.Injective <| (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  Faithful.map_injective
#align category_theory.functor.map_injective CategoryTheory.Functor.map_injective

theorem mapIso_injective (F : C ⥤ D) [Faithful F] :
    Function.Injective <| (F.mapIso : (X ≅ Y) → (F.obj X ≅ F.obj Y))  := fun _ _ h =>
  Iso.ext (map_injective F (congr_arg Iso.hom h : _))
#align category_theory.functor.map_iso_injective CategoryTheory.Functor.mapIso_injective

/-- The specified preimage of a morphism under a full functor. -/
@[pp_dot]
def preimage (F : C ⥤ D) [Full F] (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  Full.preimage.{v₁, v₂} f
#align category_theory.functor.preimage CategoryTheory.Functor.preimage

@[simp]
theorem image_preimage (F : C ⥤ D) [Full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
    F.map (preimage F f) = f := by unfold preimage; aesop_cat
#align category_theory.functor.image_preimage CategoryTheory.Functor.image_preimage

theorem map_surjective (F : C ⥤ D) [Full F] :
    Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  fun f => ⟨F.preimage f, F.image_preimage f⟩
#align category_theory.functor.map_surjective CategoryTheory.Functor.map_surjective

/-- Deduce that `F` is full from the existence of preimages, using choice. -/
noncomputable def fullOfExists (F : C ⥤ D)
    (h : ∀ (X Y : C) (f : F.obj X ⟶ F.obj Y), ∃ p, F.map p = f) : Full F := by
  choose p hp using h
  exact ⟨@p, @hp⟩
#align category_theory.functor.full_of_exists CategoryTheory.Functor.fullOfExists

/-- Deduce that `F` is full from surjectivity of `F.map`, using choice. -/
noncomputable def fullOfSurjective (F : C ⥤ D)
    (h : ∀ X Y : C, Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) : Full F :=
  fullOfExists _ h
#align category_theory.functor.full_of_surjective CategoryTheory.Functor.fullOfSurjective

end Functor

section

variable {F : C ⥤ D} [Full F] [Faithful F] {X Y Z : C}

@[simp]
theorem preimage_id : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
  F.map_injective (by simp)
#align category_theory.preimage_id CategoryTheory.preimage_id

@[simp]
theorem preimage_comp (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    F.preimage (f ≫ g) = F.preimage f ≫ F.preimage g :=
  F.map_injective (by simp)
#align category_theory.preimage_comp CategoryTheory.preimage_comp

@[simp]
theorem preimage_map (f : X ⟶ Y) : F.preimage (F.map f) = f :=
  F.map_injective (by simp)
#align category_theory.preimage_map CategoryTheory.preimage_map

variable (F)

namespace Functor

/-- If `F : C ⥤ D` is fully faithful, every isomorphism `F.obj X ≅ F.obj Y` has a preimage. -/
@[simps]
def preimageIso (f : F.obj X ≅ F.obj Y) :
    X ≅ Y where
  hom := F.preimage f.hom
  inv := F.preimage f.inv
  hom_inv_id := F.map_injective (by simp)
  inv_hom_id := F.map_injective (by simp)
#align category_theory.functor.preimage_iso CategoryTheory.Functor.preimageIso
#align category_theory.functor.preimage_iso_inv CategoryTheory.Functor.preimageIso_inv
#align category_theory.functor.preimage_iso_hom CategoryTheory.Functor.preimageIso_hom

@[simp]
theorem preimageIso_mapIso (f : X ≅ Y) : F.preimageIso (F.mapIso f) = f := by
  ext
  simp
#align category_theory.functor.preimage_iso_map_iso CategoryTheory.Functor.preimageIso_mapIso

end Functor

/-- If the image of a morphism under a fully faithful functor in an isomorphism,
then the original morphisms is also an isomorphism.
-/
theorem isIso_of_fully_faithful (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f :=
  ⟨⟨F.preimage (inv (F.map f)), ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩
#align category_theory.is_iso_of_fully_faithful CategoryTheory.isIso_of_fully_faithful

/-- If `F` is fully faithful, we have an equivalence of hom-sets `X ⟶ Y` and `F X ⟶ F Y`. -/
@[simps]
def equivOfFullyFaithful {X Y} :
    (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun f := F.map f
  invFun f := F.preimage f
  left_inv f := by simp
  right_inv f := by simp
#align category_theory.equiv_of_fully_faithful CategoryTheory.equivOfFullyFaithful
#align category_theory.equiv_of_fully_faithful_apply CategoryTheory.equivOfFullyFaithful_apply
#align category_theory.equiv_of_fully_faithful_symm_apply CategoryTheory.equivOfFullyFaithful_symm_apply

/-- If `F` is fully faithful, we have an equivalence of iso-sets `X ≅ Y` and `F X ≅ F Y`. -/
@[simps]
def isoEquivOfFullyFaithful {X Y} :
    (X ≅ Y) ≃ (F.obj X ≅ F.obj Y) where
  toFun f := F.mapIso f
  invFun f := F.preimageIso f
  left_inv f := by simp
  right_inv f := by
    ext
    simp
#align category_theory.iso_equiv_of_fully_faithful CategoryTheory.isoEquivOfFullyFaithful
#align category_theory.iso_equiv_of_fully_faithful_symm_apply CategoryTheory.isoEquivOfFullyFaithful_symm_apply
#align category_theory.iso_equiv_of_fully_faithful_apply CategoryTheory.isoEquivOfFullyFaithful_apply

end

section

variable {E : Type*} [Category E] {F G : C ⥤ D} (H : D ⥤ E) [Full H] [Faithful H]

/-- We can construct a natural transformation between functors by constructing a
natural transformation between those functors composed with a fully faithful functor. -/
@[simps]
def natTransOfCompFullyFaithful (α : F ⋙ H ⟶ G ⋙ H) :
    F ⟶ G where
  app X := (equivOfFullyFaithful H).symm (α.app X)
  naturality X Y f := by
    dsimp
    apply H.map_injective
    simpa using α.naturality f
#align category_theory.nat_trans_of_comp_fully_faithful CategoryTheory.natTransOfCompFullyFaithful
#align category_theory.nat_trans_of_comp_fully_faithful_app CategoryTheory.natTransOfCompFullyFaithful_app

/-- We can construct a natural isomorphism between functors by constructing a natural isomorphism
between those functors composed with a fully faithful functor. -/
@[simps!]
def natIsoOfCompFullyFaithful (i : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => (isoEquivOfFullyFaithful H).symm (i.app X)) fun f => by
    dsimp
    apply H.map_injective
    simpa using i.hom.naturality f
#align category_theory.nat_iso_of_comp_fully_faithful CategoryTheory.natIsoOfCompFullyFaithful
#align category_theory.nat_iso_of_comp_fully_faithful_hom_app CategoryTheory.natIsoOfCompFullyFaithful_hom_app
#align category_theory.nat_iso_of_comp_fully_faithful_inv_app CategoryTheory.natIsoOfCompFullyFaithful_inv_app

theorem natIsoOfCompFullyFaithful_hom (i : F ⋙ H ≅ G ⋙ H) :
    (natIsoOfCompFullyFaithful H i).hom = natTransOfCompFullyFaithful H i.hom := by
  ext
  simp [natIsoOfCompFullyFaithful]
#align category_theory.nat_iso_of_comp_fully_faithful_hom CategoryTheory.natIsoOfCompFullyFaithful_hom

theorem natIsoOfCompFullyFaithful_inv (i : F ⋙ H ≅ G ⋙ H) :
    (natIsoOfCompFullyFaithful H i).inv = natTransOfCompFullyFaithful H i.inv := by
  ext
  simp [← preimage_comp]
#align category_theory.nat_iso_of_comp_fully_faithful_inv CategoryTheory.natIsoOfCompFullyFaithful_inv

/-- Horizontal composition with a fully faithful functor induces a bijection on
natural transformations. -/
@[simps]
def NatTrans.equivOfCompFullyFaithful :
    (F ⟶ G) ≃ (F ⋙ H ⟶ G ⋙ H) where
  toFun α := α ◫ 𝟙 H
  invFun := natTransOfCompFullyFaithful H
  left_inv := by aesop_cat
  right_inv := by aesop_cat
#align category_theory.nat_trans.equiv_of_comp_fully_faithful CategoryTheory.NatTrans.equivOfCompFullyFaithful
#align category_theory.nat_trans.equiv_of_comp_fully_faithful_apply CategoryTheory.NatTrans.equivOfCompFullyFaithful_apply
#align category_theory.nat_trans.equiv_of_comp_fully_faithful_symm_apply CategoryTheory.NatTrans.equivOfCompFullyFaithful_symm_apply

/-- Horizontal composition with a fully faithful functor induces a bijection on
natural isomorphisms. -/
@[simps]
def NatIso.equivOfCompFullyFaithful :
    (F ≅ G) ≃ (F ⋙ H ≅ G ⋙ H) where
  toFun e := NatIso.hcomp e (Iso.refl H)
  invFun := natIsoOfCompFullyFaithful H
  left_inv := by aesop_cat
  right_inv := by aesop_cat
#align category_theory.nat_iso.equiv_of_comp_fully_faithful CategoryTheory.NatIso.equivOfCompFullyFaithful
#align category_theory.nat_iso.equiv_of_comp_fully_faithful_symm_apply CategoryTheory.NatIso.equivOfCompFullyFaithful_symm_apply
#align category_theory.nat_iso.equiv_of_comp_fully_faithful_apply CategoryTheory.NatIso.equivOfCompFullyFaithful_apply

end

end CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

instance Full.id : Full (𝟭 C) where preimage f := f
#align category_theory.full.id CategoryTheory.Full.id

instance Faithful.id : Faithful (𝟭 C) := { }
#align category_theory.faithful.id CategoryTheory.Faithful.id

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

variable (F F' : C ⥤ D) (G : D ⥤ E)

instance Faithful.comp [Faithful F] [Faithful G] :
    Faithful (F ⋙ G) where map_injective p := F.map_injective (G.map_injective p)
#align category_theory.faithful.comp CategoryTheory.Faithful.comp

theorem Faithful.of_comp [Faithful <| F ⋙ G] : Faithful F :=
  -- Porting note: (F ⋙ G).map_injective.of_comp has the incorrect type
  { map_injective := fun {_ _} => Function.Injective.of_comp (F ⋙ G).map_injective }
#align category_theory.faithful.of_comp CategoryTheory.Faithful.of_comp

section

variable {F F'}

/-- If `F` is full, and naturally isomorphic to some `F'`, then `F'` is also full. -/
def Full.ofIso [Full F] (α : F ≅ F') :
    Full F' where
  preimage {X Y} f := F.preimage ((α.app X).hom ≫ f ≫ (α.app Y).inv)
  witness f := by simp [← NatIso.naturality_1 α]
#align category_theory.full.of_iso CategoryTheory.Full.ofIso

theorem Faithful.of_iso [Faithful F] (α : F ≅ F') : Faithful F' :=
  { map_injective := fun h =>
      F.map_injective (by rw [← NatIso.naturality_1 α.symm, h, NatIso.naturality_1 α.symm]) }
#align category_theory.faithful.of_iso CategoryTheory.Faithful.of_iso

end

variable {F G}

theorem Faithful.of_comp_iso {H : C ⥤ E} [Faithful H] (h : F ⋙ G ≅ H) : Faithful F :=
  @Faithful.of_comp _ _ _ _ _ _ F G (Faithful.of_iso h.symm)
#align category_theory.faithful.of_comp_iso CategoryTheory.Faithful.of_comp_iso

alias _root_.CategoryTheory.Iso.faithful_of_comp := Faithful.of_comp_iso
#align category_theory.iso.faithful_of_comp CategoryTheory.Iso.faithful_of_comp

-- We could prove this from `Faithful.of_comp_iso` using `eq_to_iso`,
-- but that would introduce a cyclic import.
theorem Faithful.of_comp_eq {H : C ⥤ E} [ℋ : Faithful H] (h : F ⋙ G = H) : Faithful F :=
  @Faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)
#align category_theory.faithful.of_comp_eq CategoryTheory.Faithful.of_comp_eq

alias _root_.Eq.faithful_of_comp := Faithful.of_comp_eq
#align eq.faithful_of_comp Eq.faithful_of_comp

variable (F G)
/-- “Divide” a functor by a faithful functor. -/
protected def Faithful.div (F : C ⥤ E) (G : D ⥤ E) [Faithful G] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq (G.map (map f)) (F.map f)) : C ⥤ D :=
  { obj, map := @map,
    map_id := by
      intros X
      apply G.map_injective
      apply eq_of_heq
      trans F.map (𝟙 X)
      · exact h_map
      · rw [F.map_id, G.map_id, h_obj X]
    map_comp := by
      intros X Y Z f g
      refine G.map_injective <| eq_of_heq <| h_map.trans ?_
      simp only [Functor.map_comp]
      convert HEq.refl (F.map f ≫ F.map g)
      all_goals { first | apply h_obj | apply h_map } }
#align category_theory.faithful.div CategoryTheory.Faithful.div

-- This follows immediately from `Functor.hext` (`Functor.hext h_obj @h_map`),
-- but importing `CategoryTheory.EqToHom` causes an import loop:
-- CategoryTheory.EqToHom → CategoryTheory.Opposites →
-- CategoryTheory.Equivalence → CategoryTheory.FullyFaithful
theorem Faithful.div_comp (F : C ⥤ E) [Faithful F] (G : D ⥤ E) [Faithful G] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq (G.map (map f)) (F.map f)) :
    Faithful.div F G obj @h_obj @map @h_map ⋙ G = F := by
  -- Porting note: Have to unfold the structure twice because the first one recovers only the
  -- prefunctor `F_pre`
  cases' F with F_pre _ _; cases' G with G_pre _ _
  cases' F_pre with F_obj _; cases' G_pre with G_obj _
  unfold Faithful.div Functor.comp
  -- Porting note: unable to find the lean4 analogue to `unfold_projs`, works without it
  have : F_obj = G_obj ∘ obj := (funext h_obj).symm
  subst this
  congr
  simp only [Function.comp_apply, heq_eq_eq] at h_map
  ext
  exact h_map
#align category_theory.faithful.div_comp CategoryTheory.Faithful.div_comp

theorem Faithful.div_faithful (F : C ⥤ E) [Faithful F] (G : D ⥤ E) [Faithful G] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq (G.map (map f)) (F.map f)) :
    Faithful (Faithful.div F G obj @h_obj @map @h_map) :=
  (Faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp
#align category_theory.faithful.div_faithful CategoryTheory.Faithful.div_faithful

instance Full.comp [Full F] [Full G] :
    Full (F ⋙ G) where preimage f := F.preimage (G.preimage f)
#align category_theory.full.comp CategoryTheory.Full.comp

/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full. -/
def Full.ofCompFaithful [Full <| F ⋙ G] [Faithful G] :
    Full F where
  preimage f := (F ⋙ G).preimage (G.map f)
  witness _ := G.map_injective ((F ⋙ G).image_preimage _)
#align category_theory.full.of_comp_faithful CategoryTheory.Full.ofCompFaithful

/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full. -/
def Full.ofCompFaithfulIso {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [Full H] [Faithful G]
    (h : F ⋙ G ≅ H) : Full F :=
  @Full.ofCompFaithful _ _ _ _ _ _ F G (Full.ofIso h.symm) _
#align category_theory.full.of_comp_faithful_iso CategoryTheory.Full.ofCompFaithfulIso

/-- Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful functor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`.
-/
def fullyFaithfulCancelRight {F G : C ⥤ D} (H : D ⥤ E) [Full H] [Faithful H]
    (comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => H.preimageIso (comp_iso.app X)) fun f =>
    H.map_injective (by simpa using comp_iso.hom.naturality f)
#align category_theory.fully_faithful_cancel_right CategoryTheory.fullyFaithfulCancelRight

@[simp]
theorem fullyFaithfulCancelRight_hom_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [Faithful H]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).hom.app X = H.preimage (comp_iso.hom.app X) :=
  rfl
#align category_theory.fully_faithful_cancel_right_hom_app CategoryTheory.fullyFaithfulCancelRight_hom_app

@[simp]
theorem fullyFaithfulCancelRight_inv_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [Faithful H]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).inv.app X = H.preimage (comp_iso.inv.app X) :=
  rfl
#align category_theory.fully_faithful_cancel_right_inv_app CategoryTheory.fullyFaithfulCancelRight_inv_app

end CategoryTheory
