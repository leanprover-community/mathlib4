/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.NatIso
import Mathlib.Logic.Equiv.Defs

#align_import category_theory.functor.fully_faithful from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Full and faithful functors

We define typeclasses `Full` and `Faithful`, decorating functors. These typeclasses
carry no data. However, we also introduce a structure `Functor.FullyFaithful` which
contains the data of the inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of the
map induced on morphisms by a functor `F`.

## Main definitions and results
* Use `F.map_injective` to retrieve the fact that `F.map` is injective when `[Faithful F]`.
* Similarly, `F.map_surjective` states that `F.map` is surjective when `[Full F]`.
* Use `F.preimage` to obtain preimages of morphisms when `[Full F]`.
* We prove some basic "cancellation" lemmas for full and/or faithful functors, as well as a
  construction for "dividing" a functor by a faithful functor, see `Faithful.div`.

See `CategoryTheory.Equivalence.of_fullyFaithful_ess_surj` for the fact that a functor is an
equivalence if and only if it is fully faithful and essentially surjective.

-/


-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor

/-- A functor `F : C ⥤ D` is full if for each `X Y : C`, `F.map` is surjective.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class Full (F : C ⥤ D) : Prop where
  map_surjective {X Y : C} : Function.Surjective (F.map (X := X) (Y := Y))
#align category_theory.full CategoryTheory.Functor.Full

/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4:
#[`map_injective'] [] -/
/-- A functor `F : C ⥤ D` is faithful if for each `X Y : C`, `F.map` is injective.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class Faithful (F : C ⥤ D) : Prop where
  /-- `F.map` is injective for each `X Y : C`. -/
  map_injective : ∀ {X Y : C}, Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
    aesop_cat
#align category_theory.faithful CategoryTheory.Functor.Faithful
#align category_theory.faithful.map_injective CategoryTheory.Functor.Faithful.map_injective

variable {X Y : C}

theorem map_injective (F : C ⥤ D) [Faithful F] :
    Function.Injective <| (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  Faithful.map_injective
#align category_theory.functor.map_injective CategoryTheory.Functor.map_injective

lemma map_injective_iff (F : C ⥤ D) [Faithful F] {X Y : C} (f g : X ⟶ Y) :
    F.map f = F.map g ↔ f = g :=
  ⟨fun h => F.map_injective h, fun h => by rw [h]⟩

theorem mapIso_injective (F : C ⥤ D) [Faithful F] :
    Function.Injective <| (F.mapIso : (X ≅ Y) → (F.obj X ≅ F.obj Y))  := fun _ _ h =>
  Iso.ext (map_injective F (congr_arg Iso.hom h : _))
#align category_theory.functor.map_iso_injective CategoryTheory.Functor.mapIso_injective

theorem map_surjective (F : C ⥤ D) [Full F] :
    Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  Full.map_surjective
#align category_theory.functor.map_surjective CategoryTheory.Functor.map_surjective

/-- The choice of a preimage of a morphism under a full functor. -/
noncomputable def preimage (F : C ⥤ D) [Full F] (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  (F.map_surjective f).choose
#align category_theory.functor.preimage CategoryTheory.Functor.preimage

@[simp]
theorem map_preimage (F : C ⥤ D) [Full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
    F.map (preimage F f) = f :=
  (F.map_surjective f).choose_spec
#align category_theory.functor.image_preimage CategoryTheory.Functor.map_preimage

variable {F : C ⥤ D} [Full F] [F.Faithful] {X Y Z : C}

@[simp]
theorem preimage_id : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
  F.map_injective (by simp)
#align category_theory.preimage_id CategoryTheory.Functor.preimage_id

@[simp]
theorem preimage_comp (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    F.preimage (f ≫ g) = F.preimage f ≫ F.preimage g :=
  F.map_injective (by simp)
#align category_theory.preimage_comp CategoryTheory.Functor.preimage_comp

@[simp]
theorem preimage_map (f : X ⟶ Y) : F.preimage (F.map f) = f :=
  F.map_injective (by simp)
#align category_theory.preimage_map CategoryTheory.Functor.preimage_map

variable (F)

/-- If `F : C ⥤ D` is fully faithful, every isomorphism `F.obj X ≅ F.obj Y` has a preimage. -/
@[simps]
noncomputable def preimageIso (f : F.obj X ≅ F.obj Y) :
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

/-- Structure containing the data of inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of `F.map`
in order to express that `F` is a fully faithful functor. -/
structure FullyFaithful where
  /-- The inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of `F.map`. -/
  preimage {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y
  map_preimage {X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage f) = f := by aesop_cat
  preimage_map {X Y : C} (f : X ⟶ Y) : preimage (F.map f) = f := by aesop_cat

namespace FullyFaithful

attribute [simp] map_preimage preimage_map

/-- A `FullyFaithful` structure can be obtained from the assumption the `F` is both
full and faithful. -/
noncomputable def ofFullyFaithful [F.Full] [F.Faithful] :
    F.FullyFaithful where
  preimage := F.preimage

variable {F}
variable (hF : F.FullyFaithful)

/-- The equivalence `(X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y)` given by `h : F.FullyFaithful`. -/
@[simps]
def homEquiv {X Y : C} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := hF.preimage
  left_inv _ := by simp
  right_inv _ := by simp

lemma map_injective {X Y : C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g :=
  hF.homEquiv.injective h

lemma map_surjective {X Y : C} :
    Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  hF.homEquiv.surjective

lemma map_bijective (X Y : C) :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  hF.homEquiv.bijective

lemma full : F.Full where
  map_surjective := hF.map_surjective

lemma faithful : F.Faithful where
  map_injective := hF.map_injective

/-- The unique isomorphism `X ≅ Y` which induces an isomorphism `F.obj X ≅ F.obj Y`
when `hF : F.FullyFaithful`. -/
@[simps]
def preimageIso {X Y : C} (e : F.obj X ≅ F.obj Y) : X ≅ Y where
  hom := hF.preimage e.hom
  inv := hF.preimage e.inv
  hom_inv_id := hF.map_injective (by simp)
  inv_hom_id := hF.map_injective (by simp)

lemma isIso_of_isIso_map {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f := by
  simpa using (hF.preimageIso (asIso (F.map f))).isIso_hom

/-- The equivalence `(X ≅ Y) ≃ (F.obj X ≅ F.obj Y)` given by `h : F.FullyFaithful`. -/
@[simps]
def isoEquiv {X Y : C} : (X ≅ Y) ≃ (F.obj X ≅ F.obj Y) where
  toFun := F.mapIso
  invFun := hF.preimageIso
  left_inv := by aesop_cat
  right_inv := by aesop_cat

variable (C) in
/-- The identity functor is fully faithful. -/
@[simps]
def id : (𝟭 C).FullyFaithful where
  preimage f := f

variable {E : Type*} [Category E]

/-- Fully faithful functors are stable by composition. -/
@[simps]
def comp {G : D ⥤ E} (hG : G.FullyFaithful) : (F ⋙ G).FullyFaithful where
  preimage f := hF.preimage (hG.preimage f)

/-- If `F ⋙ G` is fully faithful and `G` is faithful, then `F` is fully faithful. -/
def ofCompFaithful {G : D ⥤ E} [G.Faithful] (hFG : (F ⋙ G).FullyFaithful) :
    F.FullyFaithful where
  preimage f := hFG.preimage (G.map f)
  map_preimage f := G.map_injective (hFG.map_preimage (G.map f))
  preimage_map f := hFG.preimage_map f

end FullyFaithful

end Functor


section

variable (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C}

/-- If the image of a morphism under a fully faithful functor in an isomorphism,
then the original morphisms is also an isomorphism.
-/
theorem isIso_of_fully_faithful (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f :=
  ⟨⟨F.preimage (inv (F.map f)), ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩
#align category_theory.is_iso_of_fully_faithful CategoryTheory.isIso_of_fully_faithful


end

end CategoryTheory

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]

instance Full.id : Full (𝟭 C) where map_surjective := Function.surjective_id
#align category_theory.full.id CategoryTheory.Functor.Full.id

instance Faithful.id : Functor.Faithful (𝟭 C) := { }
#align category_theory.faithful.id CategoryTheory.Functor.Faithful.id

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
variable (F F' : C ⥤ D) (G : D ⥤ E)

instance Faithful.comp [F.Faithful] [G.Faithful] :
    (F ⋙ G).Faithful  where map_injective p := F.map_injective (G.map_injective p)
#align category_theory.faithful.comp CategoryTheory.Functor.Faithful.comp

theorem Faithful.of_comp [(F ⋙ G).Faithful] : F.Faithful :=
  -- Porting note: (F ⋙ G).map_injective.of_comp has the incorrect type
  { map_injective := fun {_ _} => Function.Injective.of_comp (F ⋙ G).map_injective }
#align category_theory.faithful.of_comp CategoryTheory.Functor.Faithful.of_comp

instance (priority := 100) [Quiver.IsThin C] : F.Faithful where

section

variable {F F'}

/-- If `F` is full, and naturally isomorphic to some `F'`, then `F'` is also full. -/
lemma Full.of_iso [Full F] (α : F ≅ F') : Full F' where
  map_surjective {X Y} f :=
    ⟨F.preimage ((α.app X).hom ≫ f ≫ (α.app Y).inv), by simp [← NatIso.naturality_1 α]⟩
#align category_theory.full.of_iso CategoryTheory.Functor.Full.of_iso

theorem Faithful.of_iso [F.Faithful] (α : F ≅ F') : F'.Faithful :=
  { map_injective := fun h =>
      F.map_injective (by rw [← NatIso.naturality_1 α.symm, h, NatIso.naturality_1 α.symm]) }
#align category_theory.faithful.of_iso CategoryTheory.Functor.Faithful.of_iso

end

variable {F G}

theorem Faithful.of_comp_iso {H : C ⥤ E} [H.Faithful] (h : F ⋙ G ≅ H) : F.Faithful :=
  @Faithful.of_comp _ _ _ _ _ _ F G (Faithful.of_iso h.symm)
#align category_theory.faithful.of_comp_iso CategoryTheory.Functor.Faithful.of_comp_iso

alias _root_.CategoryTheory.Iso.faithful_of_comp := Faithful.of_comp_iso
#align category_theory.iso.faithful_of_comp CategoryTheory.Iso.faithful_of_comp

-- We could prove this from `Faithful.of_comp_iso` using `eq_to_iso`,
-- but that would introduce a cyclic import.
theorem Faithful.of_comp_eq {H : C ⥤ E} [ℋ : H.Faithful] (h : F ⋙ G = H) : F.Faithful :=
  @Faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)
#align category_theory.faithful.of_comp_eq CategoryTheory.Functor.Faithful.of_comp_eq

alias _root_.Eq.faithful_of_comp := Faithful.of_comp_eq
#align eq.faithful_of_comp Eq.faithful_of_comp

variable (F G)
/-- “Divide” a functor by a faithful functor. -/
protected def Faithful.div (F : C ⥤ E) (G : D ⥤ E) [G.Faithful] (obj : C → D)
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
#align category_theory.faithful.div CategoryTheory.Functor.Faithful.div

-- This follows immediately from `Functor.hext` (`Functor.hext h_obj @h_map`),
-- but importing `CategoryTheory.EqToHom` causes an import loop:
-- CategoryTheory.EqToHom → CategoryTheory.Opposites →
-- CategoryTheory.Equivalence → CategoryTheory.FullyFaithful
theorem Faithful.div_comp (F : C ⥤ E) [F.Faithful] (G : D ⥤ E) [G.Faithful] (obj : C → D)
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
#align category_theory.faithful.div_comp CategoryTheory.Functor.Faithful.div_comp

theorem Faithful.div_faithful (F : C ⥤ E) [F.Faithful] (G : D ⥤ E) [G.Faithful] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq (G.map (map f)) (F.map f)) :
    Functor.Faithful (Faithful.div F G obj @h_obj @map @h_map) :=
  (Faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp
#align category_theory.faithful.div_faithful CategoryTheory.Functor.Faithful.div_faithful

instance Full.comp [Full F] [Full G] : Full (F ⋙ G) where
  map_surjective f := ⟨F.preimage (G.preimage f), by simp⟩
#align category_theory.full.comp CategoryTheory.Functor.Full.comp

/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full. -/
lemma Full.of_comp_faithful [Full <| F ⋙ G] [G.Faithful] : Full F where
  map_surjective f := ⟨(F ⋙ G).preimage (G.map f), G.map_injective ((F ⋙ G).map_preimage _)⟩
#align category_theory.full.of_comp_faithful CategoryTheory.Functor.Full.of_comp_faithful

/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full. -/
lemma Full.of_comp_faithful_iso {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [Full H] [G.Faithful]
    (h : F ⋙ G ≅ H) : Full F := by
  have := Full.of_iso h.symm
  exact Full.of_comp_faithful F G
#align category_theory.full.of_comp_faithful_iso CategoryTheory.Functor.Full.of_comp_faithful_iso

/-- Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful functor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`.
-/
noncomputable def fullyFaithfulCancelRight {F G : C ⥤ D} (H : D ⥤ E) [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => H.preimageIso (comp_iso.app X)) fun f =>
    H.map_injective (by simpa using comp_iso.hom.naturality f)
#align category_theory.fully_faithful_cancel_right CategoryTheory.Functor.fullyFaithfulCancelRight

@[simp]
theorem fullyFaithfulCancelRight_hom_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).hom.app X = H.preimage (comp_iso.hom.app X) :=
  rfl
#align category_theory.fully_faithful_cancel_right_hom_app CategoryTheory.Functor.fullyFaithfulCancelRight_hom_app

@[simp]
theorem fullyFaithfulCancelRight_inv_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).inv.app X = H.preimage (comp_iso.inv.app X) :=
  rfl
#align category_theory.fully_faithful_cancel_right_inv_app CategoryTheory.Functor.fullyFaithfulCancelRight_inv_app

end Functor

-- deprecated on 2024-04-06
@[deprecated] alias Full := Functor.Full
@[deprecated] alias Faithful := Functor.Faithful
@[deprecated] alias preimage_id := Functor.preimage_id
@[deprecated] alias preimage_comp := Functor.preimage_comp
@[deprecated] alias preimage_map := Functor.preimage_map
@[deprecated] alias Faithful.of_comp := Functor.Faithful.of_comp
@[deprecated] alias Full.ofIso := Functor.Full.of_iso
@[deprecated] alias Faithful.of_iso := Functor.Faithful.of_iso
@[deprecated] alias Faithful.of_comp_iso := Functor.Faithful.of_comp_iso
@[deprecated] alias Faithful.of_comp_eq := Functor.Faithful.of_comp_eq
@[deprecated] alias Faithful.div := Functor.Faithful.div
@[deprecated] alias Faithful.div_comp := Functor.Faithful.div_comp
@[deprecated] alias Faithful.div_faithful := Functor.Faithful.div_faithful
@[deprecated] alias Full.ofCompFaithful := Functor.Full.of_comp_faithful
@[deprecated] alias Full.ofCompFaithfulIso := Functor.Full.of_comp_faithful_iso
@[deprecated] alias fullyFaithfulCancelRight := Functor.fullyFaithfulCancelRight
@[deprecated] alias fullyFaithfulCancelRight_hom_app := Functor.fullyFaithfulCancelRight_hom_app
@[deprecated] alias fullyFaithfulCancelRight_inv_app := Functor.fullyFaithfulCancelRight_inv_app

-- deprecated on 2024-04-26
@[deprecated] alias Functor.image_preimage := Functor.map_preimage

end CategoryTheory
