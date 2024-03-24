/-
Copyright (c) 2023 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Presheaves of modules over a presheaf of rings.

We give a hands-on description of a presheaf of modules over a fixed presheaf of rings `R`,
as a presheaf of abelian groups with additional data.

We also provide two alternative constructors :
* `mk' : CorePresheafOfModules R → PresheafOfModules R` where `M : CorePresheafOfModules R`
consists of a family of unbundled modules over `R.obj X` for all `X`
* `mk'' : BundledCorePresheafOfModules R → PresheafOfModules R`
where `M : BundledCorePresheafOfModules R` consists of a family of objects in
`ModuleCat (R.obj X)` for all `X`

## Future work

* Compare this to the definition as a presheaf of pairs `(R, M)` with specified first part.
* Compare this to the definition as a module object of the presheaf of rings
  thought of as a monoid object.
* (Pre)sheaves of modules over a given sheaf of rings are an abelian category.
* Presheaves of modules over a presheaf of commutative rings form a monoidal category.
* Pushforward and pullback.
-/

universe v v₁ u₁ u

open CategoryTheory LinearMap Opposite

variable {C : Type u₁} [Category.{v₁} C]

/-- A presheaf of modules over a given presheaf of rings,
described as a presheaf of abelian groups, and the extra data of the action at each object,
and a condition relating functoriality and scalar multiplication. -/
structure PresheafOfModules (R : Cᵒᵖ ⥤ RingCat.{u}) where
  presheaf : Cᵒᵖ ⥤ AddCommGroupCat.{v}
  module : ∀ X : Cᵒᵖ, Module (R.obj X) (presheaf.obj X) := by infer_instance
  map_smul : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (x : presheaf.obj X),
    presheaf.map f (r • x) = R.map f r • presheaf.map f x := by aesop_cat

variable {R : Cᵒᵖ ⥤ RingCat.{u}}

namespace PresheafOfModules

attribute [instance] PresheafOfModules.module

/-- The bundled module over an object `X`. -/
def obj (P : PresheafOfModules R) (X : Cᵒᵖ) : ModuleCat (R.obj X) :=
  ModuleCat.of _ (P.presheaf.obj X)

/--
If `P` is a presheaf of modules over a presheaf of rings `R`, both over some category `C`,
and `f : X ⟶ Y` is a morphism in `Cᵒᵖ`, we construct the `R.map f`-semilinear map
from the `R.obj X`-module `P.presheaf.obj X` to the `R.obj Y`-module `P.presheaf.obj Y`.
 -/
def map (P : PresheafOfModules R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    P.obj X →ₛₗ[R.map f] P.obj Y :=
  { toAddHom := (P.presheaf.map f).toAddHom,
    map_smul' := P.map_smul f, }

@[simp]
theorem map_apply (P : PresheafOfModules R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x) :
    P.map f x = (P.presheaf.map f) x :=
  rfl

instance (X : Cᵒᵖ) : RingHomId (R.map (𝟙 X)) where
  eq_id := R.map_id X

instance {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingHomCompTriple (R.map f) (R.map g) (R.map (f ≫ g)) where
  comp_eq := (R.map_comp f g).symm

@[simp]
theorem map_id (P : PresheafOfModules R) (X : Cᵒᵖ) :
    P.map (𝟙 X) = LinearMap.id' := by
  ext
  simp

@[simp]
theorem map_comp (P : PresheafOfModules R) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.map (f ≫ g) = (P.map g).comp (P.map f) := by
  ext
  simp

/-- A morphism of presheaves of modules. -/
structure Hom (P Q : PresheafOfModules R) where
  hom : P.presheaf ⟶ Q.presheaf
  map_smul : ∀ (X : Cᵒᵖ) (r : R.obj X) (x : P.presheaf.obj X), hom.app X (r • x) = r • hom.app X x

namespace Hom

/-- The identity morphism on a presheaf of modules. -/
def id (P : PresheafOfModules R) : Hom P P where
  hom := 𝟙 _
  map_smul _ _ _ := rfl

/-- Composition of morphisms of presheaves of modules. -/
def comp {P Q R : PresheafOfModules R} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  hom := f.hom ≫ g.hom
  map_smul _ _ _ := by simp [Hom.map_smul]

end Hom

instance : Category (PresheafOfModules R) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g

namespace Hom

variable {P Q T : PresheafOfModules R}

/--
The `(X : Cᵒᵖ)`-component of morphism between presheaves of modules
over a presheaf of rings `R`, as an `R.obj X`-linear map. -/
def app (f : Hom P Q) (X : Cᵒᵖ) : P.obj X →ₗ[R.obj X] Q.obj X :=
  { toAddHom := (f.hom.app X).toAddHom
    map_smul' := f.map_smul X }

@[simp]
lemma comp_app (f : P ⟶ Q) (g : Q ⟶ T) (X : Cᵒᵖ) :
    (f ≫ g).app X = (g.app X).comp (f.app X) := rfl

@[ext]
theorem ext {f g : P ⟶ Q} (w : ∀ X, f.app X = g.app X) : f = g := by
  cases f; cases g
  congr
  ext X x
  exact LinearMap.congr_fun (w X) x

section

variable (app : ∀ X, P.obj X →ₗ[R.obj X] Q.obj X)
  (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : P.obj X),
    app Y (P.map f x) = Q.map f (app X x))

/-- A constructor for morphisms in `PresheafOfModules R` that is based on the data
of a family of linear maps over the various rings `R.obj X`. -/
def mk' : P ⟶ Q where
  hom :=
    { app := fun X => (app X).toAddMonoidHom
      naturality := fun X Y f => by ext x; apply naturality }
  map_smul X := (app X).map_smul

@[simp]
lemma mk'_app : (mk' app naturality).app = app := rfl

end

instance : Zero (P ⟶ Q) := ⟨mk 0 (by
  intros
  simp only [Limits.zero_app, AddMonoidHom.zero_apply, smul_zero])⟩

variable (P Q)

@[simp]
lemma zero_app (X : Cᵒᵖ) : (0 : P ⟶ Q).app X = 0 := rfl

variable {P Q}

instance : Add (P ⟶ Q) := ⟨fun f g => mk (f.hom + g.hom) (by
  intros
  simp only [NatTrans.app_add, AddCommGroupCat.hom_add_apply, map_smul, smul_add])⟩

@[simp]
lemma add_app (f g : P ⟶ Q) (X : Cᵒᵖ) : (f + g).app X = f.app X + g.app X := rfl

instance : Sub (P ⟶ Q) := ⟨fun f g => mk (f.hom - g.hom) (by
  intros
  rw [NatTrans.app_sub, AddMonoidHom.sub_apply, AddMonoidHom.sub_apply,
    smul_sub, map_smul, map_smul])⟩

@[simp]
lemma sub_app (f g : P ⟶ Q) (X : Cᵒᵖ) : (f - g).app X = f.app X - g.app X := rfl

instance : Neg (P ⟶ Q) := ⟨fun f => mk (-f.hom) (by
  intros
  rw [NatTrans.app_neg, AddMonoidHom.neg_apply, AddMonoidHom.neg_apply,
    map_smul, smul_neg])⟩

@[simp]
lemma neg_app (f : P ⟶ Q) (X : Cᵒᵖ): (-f).app X = -f.app X := rfl

instance : AddCommGroup (P ⟶ Q) where
  add_assoc := by intros; ext1; simp only [add_app, add_assoc]
  zero_add := by intros; ext1; simp only [add_app, zero_app, zero_add]
  add_left_neg := by intros; ext1; simp only [add_app, neg_app, add_left_neg, zero_app]
  add_zero := by intros; ext1; simp only [add_app, zero_app, add_zero]
  add_comm := by intros; ext1; simp only [add_app]; apply add_comm
  sub_eq_add_neg := by intros; ext1; simp only [add_app, sub_app, neg_app, sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Preadditive (PresheafOfModules R) where
  add_comp := by intros; ext1; simp only [comp_app, add_app, comp_add]
  comp_add := by intros; ext1; simp only [comp_app, add_app, add_comp]

end Hom

variable (R)

/-- The functor from presheaves of modules over a specified presheaf of rings,
to presheaves of abelian groups.
-/
@[simps obj]
def toPresheaf : PresheafOfModules R ⥤ (Cᵒᵖ ⥤ AddCommGroupCat) where
  obj P := P.presheaf
  map f := f.hom

variable {R}

@[simp]
lemma toPresheaf_map_app {P Q : PresheafOfModules R}
    (f : P ⟶ Q) (X : Cᵒᵖ) :
    ((toPresheaf R).map f).app X = (f.app X).toAddMonoidHom := rfl

instance : (toPresheaf R).Additive where

instance : Faithful (toPresheaf R) where
  map_injective {P Q} f g h := by
    ext X x
    have eq := congr_app h X
    simp only [toPresheaf_obj, toPresheaf_map_app] at eq
    simp only [← toAddMonoidHom_coe, eq]

variable (R)

/-- Evaluation on an object `X` gives a functor
`PresheafOfModules R ⥤ ModuleCat (R.obj X)`. -/
@[simps]
def evaluation (X : Cᵒᵖ) : PresheafOfModules.{v} R ⥤ ModuleCat (R.obj X) where
  obj M := M.obj X
  map f := f.app X

variable {R}

/-- Given a presheaf of modules `M` on a category `C` and `f : X ⟶ Y` in `Cᵒᵖ`, this
is the restriction map `M.obj X ⟶ M.obj Y`, considered as a linear map to
the restriction of scalars of `M.obj Y`. -/
noncomputable def restrictionApp {X Y : Cᵒᵖ} (f : X ⟶ Y) (M : PresheafOfModules.{v} R) :
    M.obj X ⟶ (ModuleCat.restrictScalars (R.map f)).obj (M.obj Y) :=
  ModuleCat.semilinearMapAddEquiv (R.map f) _ _ (M.map f)

lemma restrictionApp_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (M : PresheafOfModules R) (x : M.obj X) :
    restrictionApp f M x = M.map f x := by
  rfl

variable (R)

/-- The restriction natural transformation on presheaves of modules, considered as linear maps
to restriction of scalars. -/
@[simps]
noncomputable def restriction {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    evaluation R X ⟶ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f) where
  app := restrictionApp f
  naturality := fun M N φ => by
    ext x
    exact (congr_hom (φ.hom.naturality f) x).symm

variable {R}

attribute [local simp] restrictionApp_apply

lemma restriction_app_id (M : PresheafOfModules R) (X : Cᵒᵖ) :
    restrictionApp (𝟙 X) M =
      (ModuleCat.restrictScalarsId' (R.map (𝟙 X)) (R.map_id X)).inv.app (M.obj X) := by aesop

lemma restriction_app_comp (M : PresheafOfModules R) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    restrictionApp (f ≫ g) M =
      restrictionApp f M ≫
        (ModuleCat.restrictScalars (R.map f)).map (restrictionApp g M) ≫
        (ModuleCat.restrictScalarsComp' _ _ _ (R.map_comp f g)).inv.app (M.obj Z) := by aesop

end PresheafOfModules

variable (R) in
/-- This structure contains the data and axioms in order to
produce a `PresheafOfModules R` from a collection of types
equipped with module structures over the various rings `R.obj X`.
(See the constructor `PresheafOfModules.mk'`.) -/
structure CorePresheafOfModules where
  /-- the datum of a type for each object in `Cᵒᵖ` -/
  obj (X : Cᵒᵖ) : Type v
  /-- the abelian group structure on the types `obj X` -/
  addCommGroup (X : Cᵒᵖ) : AddCommGroup (obj X) := by infer_instance
  /-- the module structure on the types `obj X` over the various rings `R.obj X` -/
  module (X : Cᵒᵖ) : Module (R.obj X) (obj X) := by infer_instance
  /-- the semi-linear restriction maps -/
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X →ₛₗ[R.map f] obj Y
  /-- `map` is compatible with the identities -/
  map_id (X : Cᵒᵖ) (x : obj X) : map (𝟙 X) x = x := by aesop_cat
  /-- `map` is compatible with the composition -/
  map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : obj X) :
    map (f ≫ g) x = map g (map f x) := by aesop_cat

-- this example is meant to test automation: the axioms for `CorePresheafOfModules` are
-- automatically found if we use the data from `M : PresheafOfModules R`
example (M : PresheafOfModules R) : CorePresheafOfModules R where
  obj X := M.obj X
  map f := M.map f

namespace CorePresheafOfModules

attribute [instance] addCommGroup module
attribute [simp] map_id map_comp

variable (M : CorePresheafOfModules R)

/-- The presheaf of abelian groups attached to a `CorePresheafOfModules R`. -/
@[simps]
def presheaf : Cᵒᵖ ⥤ AddCommGroupCat.{v} where
  obj X := AddCommGroupCat.of (M.obj X)
  map f := AddCommGroupCat.ofHom (M.map f).toAddMonoidHom

instance (X : Cᵒᵖ) : Module (R.obj X) (M.presheaf.obj X) := M.module X

end CorePresheafOfModules

namespace PresheafOfModules

/-- Constructor for `PresheafOfModules R` based on a collection of types
equipped with module structures over the various rings `R.obj X`, see
the structure `CorePresheafOfModules`. -/
def mk' (M : CorePresheafOfModules R) : PresheafOfModules R where
  presheaf := M.presheaf

@[simp]
lemma mk'_obj (M : CorePresheafOfModules R) (X : Cᵒᵖ) :
    (mk' M).obj X = ModuleCat.of _ (M.obj X) := rfl

end PresheafOfModules

variable (R) in
/-- This structure contains the data and axioms in order to
produce a `PresheafOfModules R` from a collection of objects
of type `ModuleCat (R.obj X)` for all `X`, and restriction
maps expressed as linear maps to restriction of scalars.
(See the constructor `PresheafOfModules.mk''`.) -/
structure BundledCorePresheafOfModules where
  /-- the datum of a `ModuleCat (R.obj X)` for each object in `Cᵒᵖ` -/
  obj (X : Cᵒᵖ) : ModuleCat.{v} (R.obj X)
  /-- the restriction maps as linear maps to restriction of scalars -/
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ⟶ (ModuleCat.restrictScalars (R.map f)).obj (obj Y)
  /-- `map` is compatible with the identities -/
  map_id (X : Cᵒᵖ) :
    map (𝟙 X) = (ModuleCat.restrictScalarsId' (R.map (𝟙 X)) (R.map_id X)).inv.app (obj X)
  /-- `map` is compatible with the composition -/
  map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ (ModuleCat.restrictScalars (R.map f)).map (map g) ≫
      (ModuleCat.restrictScalarsComp' (R.map f) (R.map g) (R.map (f ≫ g))
        (R.map_comp f g)).inv.app (obj Z)

namespace BundledCorePresheafOfModules

variable (M : BundledCorePresheafOfModules R)

attribute [local simp] map_id map_comp

/-- The obvious map `BundledCorePresheafOfModules R → CorePresheafOfModules R`. -/
noncomputable def toCorePresheafOfModules : CorePresheafOfModules R where
  obj X := (M.obj X).carrier
  map {X Y} f := (ModuleCat.semilinearMapAddEquiv (R.map f) (M.obj X) (M.obj Y)).symm (M.map f)

end BundledCorePresheafOfModules

namespace PresheafOfModules

/-- Constructor for `PresheafOfModules R` based on a collection of objects
of type `ModuleCat (R.obj X)` for all `X`, and restriction maps expressed
as linear maps to restriction of scalars, see
the structure `BundledCorePresheafOfModules`. -/
noncomputable def mk'' (M : BundledCorePresheafOfModules R) : PresheafOfModules R :=
  mk' M.toCorePresheafOfModules

@[simp]
lemma mk''_obj (M : BundledCorePresheafOfModules R) (X : Cᵒᵖ) :
    (mk'' M).obj X = (M.obj X).carrier := rfl

@[simp]
lemma restrictionApp_mk'' (M : BundledCorePresheafOfModules R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    restrictionApp f (mk'' M) = M.map f := rfl

namespace Hom

variable {P Q : PresheafOfModules R}
  (app : ∀ X, P.obj X →ₗ[R.obj X] Q.obj X)
  (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
    restrictionApp f P ≫ (ModuleCat.restrictScalars (R.map f)).map (app Y) =
      ModuleCat.ofHom (app X) ≫ restrictionApp f Q)

/-- A constructor for morphisms in `PresheafOfModules R` that is based on the data
of a family of linear maps over the various rings `R.obj X`, and for which the
naturality condition is stated using the restriction of scalars. -/
def mk'' : P ⟶ Q where
  hom :=
    { app := fun X => (app X).toAddMonoidHom
      naturality := fun X Y f => by
        ext x
        exact congr_hom (naturality f) x }
  map_smul X := (app X).map_smul

@[simp]
lemma mk''_app : (mk'' app naturality).app = app := rfl

end Hom

end PresheafOfModules
