/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.NatIso
import Mathlib.Logic.Equiv.Defs

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

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type*} [Category E]

namespace Functor

/-- A functor `F : C ⥤ D` is full if for each `X Y : C`, `F.map` is surjective. -/
@[stacks 001C]
class Full (F : C ⥤ D) : Prop where
  map_surjective {X Y : C} : Function.Surjective (F.map (X := X) (Y := Y))

/-- A functor `F : C ⥤ D` is faithful if for each `X Y : C`, `F.map` is injective. -/
@[stacks 001C]
class Faithful (F : C ⥤ D) : Prop where
  /-- `F.map` is injective for each `X Y : C`. -/
  map_injective : ∀ {X Y : C}, Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
    cat_disch

variable {X Y : C}

theorem map_injective (F : C ⥤ D) [Faithful F] :
    Function.Injective <| (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  Faithful.map_injective

lemma map_injective_iff (F : C ⥤ D) [Faithful F] {X Y : C} (f g : X ⟶ Y) :
    F.map f = F.map g ↔ f = g :=
  ⟨fun h => F.map_injective h, fun h => by rw [h]⟩

theorem mapIso_injective (F : C ⥤ D) [Faithful F] :
    Function.Injective <| (F.mapIso : (X ≅ Y) → (F.obj X ≅ F.obj Y))  := fun _ _ h =>
  Iso.ext (map_injective F (congr_arg Iso.hom h :))

theorem map_surjective (F : C ⥤ D) [Full F] :
    Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  Full.map_surjective

/-- The choice of a preimage of a morphism under a full functor. -/
noncomputable def preimage (F : C ⥤ D) [Full F] (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  (F.map_surjective f).choose

@[simp]
theorem map_preimage (F : C ⥤ D) [Full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
    F.map (preimage F f) = f :=
  (F.map_surjective f).choose_spec

variable {F : C ⥤ D} {X Y Z : C}

section
variable [Full F] [F.Faithful]

@[simp]
theorem preimage_id : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
  F.map_injective (by simp)

@[simp]
theorem preimage_comp (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    F.preimage (f ≫ g) = F.preimage f ≫ F.preimage g :=
  F.map_injective (by simp)

@[simp]
theorem preimage_map (f : X ⟶ Y) : F.preimage (F.map f) = f :=
  F.map_injective (by simp)

variable (F)

/-- If `F : C ⥤ D` is fully faithful, every isomorphism `F.obj X ≅ F.obj Y` has a preimage. -/
@[simps]
noncomputable def preimageIso (f : F.obj X ≅ F.obj Y) :
    X ≅ Y where
  hom := F.preimage f.hom
  inv := F.preimage f.inv
  hom_inv_id := F.map_injective (by simp)
  inv_hom_id := F.map_injective (by simp)

@[simp]
theorem preimageIso_mapIso (f : X ≅ Y) : F.preimageIso (F.mapIso f) = f := by
  ext
  simp

end

variable (F) in
/-- Structure containing the data of inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of `F.map`
in order to express that `F` is a fully faithful functor. -/
structure FullyFaithful where
  /-- The inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of `F.map`. -/
  preimage {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y
  map_preimage {X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage f) = f := by cat_disch
  preimage_map {X Y : C} (f : X ⟶ Y) : preimage (F.map f) = f := by cat_disch

namespace FullyFaithful

attribute [simp] map_preimage preimage_map

variable (F) in
/-- A `FullyFaithful` structure can be obtained from the assumption the `F` is both
full and faithful. -/
noncomputable def ofFullyFaithful [F.Full] [F.Faithful] :
    F.FullyFaithful where
  preimage := F.preimage

variable (C) in
/-- The identity functor is fully faithful. -/
@[simps]
def id : (𝟭 C).FullyFaithful where
  preimage f := f

section
variable (hF : F.FullyFaithful)

include hF

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

@[simp]
lemma preimage_id {X : C} :
    hF.preimage (𝟙 (F.obj X)) = 𝟙 X :=
  hF.map_injective (by simp)

@[simp, reassoc]
lemma preimage_comp {X Y Z : C} (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    hF.preimage (f ≫ g) = hF.preimage f ≫ hF.preimage g :=
  hF.map_injective (by simp)

lemma full : F.Full where
  map_surjective := hF.map_surjective

lemma faithful : F.Faithful where
  map_injective := hF.map_injective

instance : Subsingleton F.FullyFaithful where
  allEq h₁ h₂ := by
    have := h₁.faithful
    cases h₁ with | mk f₁ hf₁ _ => cases h₂ with | mk f₂ hf₂ _ =>
    simp only [Functor.FullyFaithful.mk.injEq]
    ext
    apply F.map_injective
    rw [hf₁, hf₂]

/-- The unique isomorphism `X ≅ Y` which induces an isomorphism `F.obj X ≅ F.obj Y`
when `hF : F.FullyFaithful`. -/
@[simps]
def preimageIso {X Y : C} (e : F.obj X ≅ F.obj Y) : X ≅ Y where
  hom := hF.preimage e.hom
  inv := hF.preimage e.inv
  hom_inv_id := hF.map_injective (by simp)
  inv_hom_id := hF.map_injective (by simp)

lemma isIso_of_isIso_map {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)] :
    IsIso f := by
  simpa using (hF.preimageIso (asIso (F.map f))).isIso_hom

/-- The equivalence `(X ≅ Y) ≃ (F.obj X ≅ F.obj Y)` given by `h : F.FullyFaithful`. -/
@[simps]
def isoEquiv {X Y : C} : (X ≅ Y) ≃ (F.obj X ≅ F.obj Y) where
  toFun := F.mapIso
  invFun := hF.preimageIso
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Fully faithful functors are stable by composition. -/
@[simps]
def comp {G : D ⥤ E} (hG : G.FullyFaithful) : (F ⋙ G).FullyFaithful where
  preimage f := hF.preimage (hG.preimage f)

end

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


end

end CategoryTheory

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]

instance Full.id : Full (𝟭 C) where map_surjective := Function.surjective_id

instance Faithful.id : Functor.Faithful (𝟭 C) := { }

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
variable (F F' : C ⥤ D) (G : D ⥤ E)

instance Faithful.comp [F.Faithful] [G.Faithful] : (F ⋙ G).Faithful where
  map_injective p := F.map_injective (G.map_injective p)

theorem Faithful.of_comp [(F ⋙ G).Faithful] : F.Faithful :=
  -- Porting note: (F ⋙ G).map_injective.of_comp has the incorrect type
  { map_injective := fun {_ _} => Function.Injective.of_comp (F ⋙ G).map_injective }

instance (priority := 100) [Quiver.IsThin C] : F.Faithful where

section

variable {F F'}

/-- If `F` is full, and naturally isomorphic to some `F'`, then `F'` is also full. -/
lemma Full.of_iso [Full F] (α : F ≅ F') : Full F' where
  map_surjective {X Y} f :=
    ⟨F.preimage ((α.app X).hom ≫ f ≫ (α.app Y).inv), by simp [← NatIso.naturality_1 α]⟩

theorem Faithful.of_iso [F.Faithful] (α : F ≅ F') : F'.Faithful :=
  { map_injective := fun h =>
      F.map_injective (by rw [← NatIso.naturality_1 α.symm, h, NatIso.naturality_1 α.symm]) }

end

variable {F G}

theorem Faithful.of_comp_iso {H : C ⥤ E} [H.Faithful] (h : F ⋙ G ≅ H) : F.Faithful :=
  @Faithful.of_comp _ _ _ _ _ _ F G (Faithful.of_iso h.symm)

alias _root_.CategoryTheory.Iso.faithful_of_comp := Faithful.of_comp_iso

-- We could prove this from `Faithful.of_comp_iso` using `eq_to_iso`,
-- but that would introduce a cyclic import.
theorem Faithful.of_comp_eq {H : C ⥤ E} [ℋ : H.Faithful] (h : F ⋙ G = H) : F.Faithful :=
  @Faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)

alias _root_.Eq.faithful_of_comp := Faithful.of_comp_eq

variable (F G)
/-- “Divide” a functor by a faithful functor. -/
protected def Faithful.div (F : C ⥤ E) (G : D ⥤ E) [G.Faithful] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) ≍ F.map f) : C ⥤ D :=
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
      grind }

-- This follows immediately from `Functor.hext` (`Functor.hext h_obj @h_map`),
-- but importing `CategoryTheory.EqToHom` causes an import loop:
-- CategoryTheory.EqToHom → CategoryTheory.Opposites →
-- CategoryTheory.Equivalence → CategoryTheory.FullyFaithful
theorem Faithful.div_comp (F : C ⥤ E) [F.Faithful] (G : D ⥤ E) [G.Faithful] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) ≍ F.map f) :
    Faithful.div F G obj @h_obj @map @h_map ⋙ G = F := by
  obtain ⟨F_obj, _, _, _⟩ := F; obtain ⟨G_obj, _, _, _⟩ := G
  unfold Faithful.div Functor.comp
  have : F_obj = G_obj ∘ obj := (funext h_obj).symm
  subst this
  congr
  simp only [Function.comp_apply, heq_eq_eq] at h_map
  ext
  exact h_map

theorem Faithful.div_faithful (F : C ⥤ E) [F.Faithful] (G : D ⥤ E) [G.Faithful] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) ≍ F.map f) :
    Functor.Faithful (Faithful.div F G obj @h_obj @map @h_map) :=
  (Faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp

instance Full.comp [Full F] [Full G] : Full (F ⋙ G) where
  map_surjective f := ⟨F.preimage (G.preimage f), by simp⟩

/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full. -/
lemma Full.of_comp_faithful [Full <| F ⋙ G] [G.Faithful] : Full F where
  map_surjective f := ⟨(F ⋙ G).preimage (G.map f), G.map_injective ((F ⋙ G).map_preimage _)⟩

/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full. -/
lemma Full.of_comp_faithful_iso {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [Full H] [G.Faithful]
    (h : F ⋙ G ≅ H) : Full F := by
  have := Full.of_iso h.symm
  exact Full.of_comp_faithful F G

/-- Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful functor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`.
-/
noncomputable def fullyFaithfulCancelRight {F G : C ⥤ D} (H : D ⥤ E) [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => H.preimageIso (comp_iso.app X)) fun f =>
    H.map_injective (by simpa using comp_iso.hom.naturality f)

@[simp]
theorem fullyFaithfulCancelRight_hom_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).hom.app X = H.preimage (comp_iso.hom.app X) :=
  rfl

@[simp]
theorem fullyFaithfulCancelRight_inv_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).inv.app X = H.preimage (comp_iso.inv.app X) :=
  rfl

end Functor
end CategoryTheory
