/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
public import Mathlib.CategoryTheory.Bicategory.Functor.Lax
public import Mathlib.Tactic.CategoryTheory.ToApp

/-!
# Pseudofunctors

A pseudofunctor is an oplax (or lax) functor whose `mapId` and `mapComp` are isomorphisms.
We provide several constructors for pseudofunctors:
* `Pseudofunctor.mk` : the default constructor, which requires `map₂_whiskerLeft` and
  `map₂_whiskerRight` instead of naturality of `mapComp`.

* `Pseudofunctor.mkOfOplax` : construct a pseudofunctor from an oplax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `Pseudofunctor.mkOfOplax'` : similar to `mkOfOplax`, but uses `IsIso` to describe isomorphisms.

* `Pseudofunctor.mkOfLax` : construct a pseudofunctor from a lax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `Pseudofunctor.mkOfLax'` : similar to `mkOfLax`, but uses `IsIso` to describe isomorphisms.

## Main definitions

* `CategoryTheory.Pseudofunctor B C` : a pseudofunctor between bicategories `B` and `C`, which we
  denote by `B ⥤ᵖ C`.
* `CategoryTheory.Pseudofunctor.comp F G` : the composition of pseudofunctors

-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

/-- A pseudofunctor `F` between bicategories `B` and `C` consists of a function between objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphisms `F.map₂`.

Unlike functors between categories, `F.map` does not need to strictly commute with composition,
and does not need to strictly preserve the identity. Instead, there are specified 2-isomorphisms
`F.map (𝟙 a) ≅ 𝟙 (F.obj a)` and `F.map (f ≫ g) ≅ F.map f ≫ F.map g`.

`F.map₂` strictly commutes with compositions and preserves the identity. It also preserves the
associator, the left unitor, and the right unitor modulo some adjustments of domains and codomains
of 2-morphisms.
-/
structure Pseudofunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
    [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  mapId (a : B) : map (𝟙 a) ≅ 𝟙 (obj a)
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ≅ map f ≫ map g
  map₂_whisker_left :
    ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv := by
    cat_disch
  map₂_whisker_right :
    ∀ {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv := by
    cat_disch
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫
      (mapComp f (g ≫ h)).inv := by
    cat_disch
  map₂_left_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = (mapComp (𝟙 a) f).hom ≫ (mapId a).hom ▷ map f ≫ (λ_ (map f)).hom := by
    cat_disch
  map₂_right_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫ map f ◁ (mapId b).hom ≫ (ρ_ (map f)).hom := by
    cat_disch

/-- Notation for a pseudofunctor between bicategories. -/
-- Given similar precedence as ⥤ (26).
scoped[CategoryTheory.Bicategory] infixr:26 " ⥤ᵖ " => Pseudofunctor -- type as \func\^p

initialize_simps_projections Pseudofunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace Pseudofunctor

attribute [simp, to_app (attr := reassoc)]
  map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor map₂_right_unitor

section

open Iso

/-- The underlying prelax functor. -/
add_decl_doc Pseudofunctor.toPrelaxFunctor


attribute [nolint docBlame] CategoryTheory.Pseudofunctor.mapId
  CategoryTheory.Pseudofunctor.mapComp
  CategoryTheory.Pseudofunctor.map₂_whisker_left
  CategoryTheory.Pseudofunctor.map₂_whisker_right
  CategoryTheory.Pseudofunctor.map₂_associator
  CategoryTheory.Pseudofunctor.map₂_left_unitor
  CategoryTheory.Pseudofunctor.map₂_right_unitor

variable (F : B ⥤ᵖ C)

/-- The oplax functor associated with a pseudofunctor. -/
@[simps]
def toOplax : B ⥤ᵒᵖᴸ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).hom
  mapComp := fun f g => (F.mapComp f g).hom

instance hasCoeToOplax : Coe (B ⥤ᵖ C) (B ⥤ᵒᵖᴸ C) :=
  ⟨toOplax⟩

/-- The lax functor associated with a pseudofunctor. -/
@[simps]
def toLax : B ⥤ᴸ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).inv
  mapComp := fun f g => (F.mapComp f g).inv
  map₂_leftUnitor f := by
    rw [← F.map₂Iso_inv, eq_inv_comp, comp_inv_eq]
    simp
  map₂_rightUnitor f := by
    rw [← F.map₂Iso_inv, eq_inv_comp, comp_inv_eq]
    simp

instance hasCoeToLax : Coe (B ⥤ᵖ C) (B ⥤ᴸ C) :=
  ⟨toLax⟩

set_option backward.isDefEq.respectTransparency false in
/-- The identity pseudofunctor. -/
@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : B ⥤ᵖ B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => Iso.refl (𝟙 a)
  mapComp := fun f g => Iso.refl (f ≫ g)

instance : Inhabited (B ⥤ᵖ B) :=
  ⟨id B⟩

set_option backward.isDefEq.respectTransparency false in
/-- Composition of pseudofunctors. -/
@[simps]
def comp (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) : B ⥤ᵖ D where
  toPrelaxFunctor := F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => G.map₂Iso (F.mapId a) ≪≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.map₂Iso (F.mapComp f g)) ≪≫ G.mapComp (F.map f) (F.map g)

section

variable (F : B ⥤ᵖ C) {a b : B}

@[to_app (attr := reassoc)]
lemma mapComp_assoc_right_hom {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom = F.map₂ (α_ f g h).inv ≫
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h ≫
    (α_ (F.map f) (F.map g) (F.map h)).hom :=
  F.toOplax.mapComp_assoc_right _ _ _

@[to_app (attr := reassoc)]
lemma mapComp_assoc_left_hom {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h =
    F.map₂ (α_ f g h).hom ≫ (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom
    ≫ (α_ (F.map f) (F.map g) (F.map h)).inv :=
  F.toOplax.mapComp_assoc_left _ _ _

@[to_app (attr := reassoc)]
lemma mapComp_assoc_right_inv {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map f ◁ (F.mapComp g h).inv ≫ (F.mapComp f (g ≫ h)).inv =
    (α_ (F.map f) (F.map g) (F.map h)).inv ≫ (F.mapComp f g).inv ▷ F.map h ≫
    (F.mapComp (f ≫ g) h).inv ≫ F.map₂ (α_ f g h).hom :=
  F.toLax.mapComp_assoc_right _ _ _

@[to_app (attr := reassoc)]
lemma mapComp_assoc_left_inv {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f g).inv ▷ F.map h ≫ (F.mapComp (f ≫ g) h).inv =
    (α_ (F.map f) (F.map g) (F.map h)).hom ≫ F.map f ◁ (F.mapComp g h).inv ≫
    (F.mapComp f (g ≫ h)).inv ≫ F.map₂ (α_ f g h).inv :=
  F.toLax.mapComp_assoc_left _ _ _

@[to_app (attr := reassoc)]
lemma mapComp_id_left_hom (f : a ⟶ b) : (F.mapComp (𝟙 a) f).hom =
    F.map₂ (λ_ f).hom ≫ (λ_ (F.map f)).inv ≫ (F.mapId a).inv ▷ F.map f := by
  simp

lemma mapComp_id_left (f : a ⟶ b) : (F.mapComp (𝟙 a) f) = F.map₂Iso (λ_ f) ≪≫
    (λ_ (F.map f)).symm ≪≫ (whiskerRightIso (F.mapId a) (F.map f)).symm :=
  Iso.ext <| F.mapComp_id_left_hom f

@[to_app (attr := reassoc)]
lemma mapComp_id_left_inv (f : a ⟶ b) : (F.mapComp (𝟙 a) f).inv =
    (F.mapId a).hom ▷ F.map f ≫ (λ_ (F.map f)).hom ≫ F.map₂ (λ_ f).inv := by
  simp [mapComp_id_left]

lemma whiskerRightIso_mapId (f : a ⟶ b) : whiskerRightIso (F.mapId a) (F.map f) =
    (F.mapComp (𝟙 a) f).symm ≪≫ F.map₂Iso (λ_ f) ≪≫ (λ_ (F.map f)).symm := by
  simp [mapComp_id_left]

@[to_app (attr := reassoc)]
lemma whiskerRight_mapId_hom (f : a ⟶ b) : (F.mapId a).hom ▷ F.map f =
    (F.mapComp (𝟙 a) f).inv ≫ F.map₂ (λ_ f).hom ≫ (λ_ (F.map f)).inv := by
  simp

@[to_app (attr := reassoc)]
lemma whiskerRight_mapId_inv (f : a ⟶ b) : (F.mapId a).inv ▷ F.map f =
    (λ_ (F.map f)).hom ≫ F.map₂ (λ_ f).inv ≫ (F.mapComp (𝟙 a) f).hom := by
  simpa using congrArg (·.inv) (F.whiskerRightIso_mapId f)

@[to_app (attr := reassoc)]
lemma mapComp_id_right_hom (f : a ⟶ b) : (F.mapComp f (𝟙 b)).hom =
    F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv ≫ F.map f ◁ (F.mapId b).inv := by
  simp

lemma mapComp_id_right (f : a ⟶ b) : (F.mapComp f (𝟙 b)) = F.map₂Iso (ρ_ f) ≪≫
    (ρ_ (F.map f)).symm ≪≫ (whiskerLeftIso (F.map f) (F.mapId b)).symm :=
  Iso.ext <| F.mapComp_id_right_hom f

@[to_app (attr := reassoc)]
lemma mapComp_id_right_inv (f : a ⟶ b) : (F.mapComp f (𝟙 b)).inv =
    F.map f ◁ (F.mapId b).hom ≫ (ρ_ (F.map f)).hom ≫ F.map₂ (ρ_ f).inv := by
  simp [mapComp_id_right]

lemma whiskerLeftIso_mapId (f : a ⟶ b) : whiskerLeftIso (F.map f) (F.mapId b) =
    (F.mapComp f (𝟙 b)).symm ≪≫ F.map₂Iso (ρ_ f) ≪≫ (ρ_ (F.map f)).symm := by
  simp [mapComp_id_right]

@[to_app (attr := reassoc)]
lemma whiskerLeft_mapId_hom (f : a ⟶ b) : F.map f ◁ (F.mapId b).hom =
    (F.mapComp f (𝟙 b)).inv ≫ F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv := by
  simp

@[to_app (attr := reassoc)]
lemma whiskerLeft_mapId_inv (f : a ⟶ b) : F.map f ◁ (F.mapId b).inv =
    (ρ_ (F.map f)).hom ≫ F.map₂ (ρ_ f).inv ≫ (F.mapComp f (𝟙 b)).hom := by
  simpa using congrArg (·.inv) (F.whiskerLeftIso_mapId f)

/-- More flexible variant of `mapId`. (See the file `Bicategory.Functor.Strict`
for applications to strict bicategories.) -/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.map f ≅ 𝟙 (F.obj b) :=
  F.map₂Iso (eqToIso (by rw [hf])) ≪≫ F.mapId _

lemma mapId'_eq_mapId (b : B) :
    F.mapId' (𝟙 b) rfl = F.mapId b := by
  simp [mapId']

@[simp]
lemma toLax_mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.toLax.mapId' f hf = (F.mapId' f hf).inv :=
  rfl

@[simp]
lemma toOplax_mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.toOplax.mapId' f hf = (F.mapId' f hf).hom :=
  rfl

/-- More flexible variant of `mapComp`. (See `Bicategory.Functor.Strict`
for applications to strict bicategories.) -/
def mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.map fg ≅ F.map f ≫ F.map g :=
  F.map₂Iso (eqToIso (by rw [h])) ≪≫ F.mapComp f g

lemma mapComp'_eq_mapComp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    F.mapComp' f g _ rfl = F.mapComp f g := by
  simp [mapComp']

@[simp]
lemma toLax_mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.toLax.mapComp' f g fg h = (F.mapComp' f g fg h).inv :=
  rfl

@[simp]
lemma toOplax_mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.toOplax.mapComp' f g fg h = (F.mapComp' f g fg h).hom :=
  rfl

end

/-- Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps]
def mkOfOplax (F : B ⥤ᵒᵖᴸ C) (F' : F.PseudoCore) : B ⥤ᵖ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left := fun f g h η => by
    rw [F'.mapCompIso_hom f g, ← F.mapComp_naturality_right_assoc, ← F'.mapCompIso_hom f h,
      hom_inv_id, comp_id]
  map₂_whisker_right := fun η h => by
    rw [F'.mapCompIso_hom _ h, ← F.mapComp_naturality_left_assoc, ← F'.mapCompIso_hom _ h,
      hom_inv_id, comp_id]
  map₂_associator := fun f g h => by
    rw [F'.mapCompIso_hom (f ≫ g) h, F'.mapCompIso_hom f g, ← F.map₂_associator_assoc, ←
      F'.mapCompIso_hom f (g ≫ h), ← F'.mapCompIso_hom g h, whiskerLeft_hom_inv_assoc,
      hom_inv_id, comp_id]

/-- Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps!]
noncomputable def mkOfOplax' (F : B ⥤ᵒᵖᴸ C) [∀ a, IsIso (F.mapId a)]
    [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : B ⥤ᵖ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => asIso (F.mapId a)
  mapComp := fun f g => asIso (F.mapComp f g)
  map₂_whisker_left := fun f g h η => by
    dsimp
    rw [← assoc, IsIso.eq_comp_inv, F.mapComp_naturality_right]
  map₂_whisker_right := fun η h => by
    dsimp
    rw [← assoc, IsIso.eq_comp_inv, F.mapComp_naturality_left]
  map₂_associator := fun f g h => by
    dsimp
    simp only [← assoc]
    rw [IsIso.eq_comp_inv, ← Bicategory.inv_whiskerLeft, IsIso.eq_comp_inv]
    simp only [assoc, F.map₂_associator]

/-- Construct a pseudofunctor from a lax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps]
def mkOfLax (F : B ⥤ᴸ C) (F' : F.PseudoCore) : B ⥤ᵖ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left f g h η := by
    rw [F'.mapCompIso_inv, ← LaxFunctor.mapComp_naturality_right, ← F'.mapCompIso_inv,
      hom_inv_id_assoc]
  map₂_whisker_right η h := by
    rw [F'.mapCompIso_inv, ← LaxFunctor.mapComp_naturality_left, ← F'.mapCompIso_inv,
      hom_inv_id_assoc]
  map₂_associator {a b c d} f g h := by
    rw [F'.mapCompIso_inv, F'.mapCompIso_inv, ← inv_comp_eq, ← IsIso.inv_comp_eq]
    simp
  map₂_left_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp
  map₂_right_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp

/-- Construct a pseudofunctor from a lax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps!]
noncomputable def mkOfLax' (F : B ⥤ᴸ C) [∀ a, IsIso (F.mapId a)]
    [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : B ⥤ᵖ C :=
  mkOfLax F
  { mapIdIso := fun a => (asIso (F.mapId a)).symm
    mapCompIso := fun f g => (asIso (F.mapComp f g)).symm }

end

end Pseudofunctor

end CategoryTheory
