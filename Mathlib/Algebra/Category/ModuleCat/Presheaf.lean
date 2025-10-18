/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Presheaves of modules over a presheaf of rings.

Given a presheaf of rings `R : Cᵒᵖ ⥤ RingCat`, we define the category `PresheafOfModules R`.
An object `M : PresheafOfModules R` consists of a family of modules
`M.obj X : ModuleCat (R.obj X)` for all `X : Cᵒᵖ`, together with the data, for all `f : X ⟶ Y`,
of a functorial linear map `M.map f` from `M.obj X` to the restriction
of scalars of `M.obj Y` via `R.map f`.


## Future work

* Compare this to the definition as a presheaf of pairs `(R, M)` with specified first part.
* Compare this to the definition as a module object of the presheaf of rings
  thought of as a monoid object.
* Presheaves of modules over a presheaf of commutative rings form a monoidal category.
* Pushforward and pullback.
-/

universe v v₁ u₁ u

open CategoryTheory LinearMap Opposite

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (R) in
/-- A presheaf of modules over `R : Cᵒᵖ ⥤ RingCat` consists of family of
objects `obj X : ModuleCat (R.obj X)` for all `X : Cᵒᵖ` together with
functorial maps `obj X ⟶ (ModuleCat.restrictScalars (R.map f)).obj (obj Y)`
for all `f : X ⟶ Y` in `Cᵒᵖ`. -/
structure PresheafOfModules where
  /-- a family of modules over `R.obj X` for all `X` -/
  obj (X : Cᵒᵖ) : ModuleCat.{v} (R.obj X)
  /-- the restriction maps of a presheaf of modules -/
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj Y)
  map_id (X : Cᵒᵖ) :
    map (𝟙 X) = (ModuleCat.restrictScalarsId' (R.map (𝟙 X)).hom
      (congrArg RingCat.Hom.hom (R.map_id X))).inv.app _ := by
        cat_disch
  map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ (ModuleCat.restrictScalars _).map (map g) ≫
      (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom <| R.map_comp f g)).inv.app _ := by cat_disch

namespace PresheafOfModules

attribute [simp] map_id map_comp
attribute [reassoc] map_comp

variable (M M₁ M₂ : PresheafOfModules.{v} R)

protected lemma map_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (m : M.obj X) :
    M.map f (r • m) = R.map f r • M.map f m := by simp

lemma congr_map_apply {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (m : M.obj X) :
    M.map f m = M.map g m := by rw [h]

/-- A morphism of presheaves of modules consists of a family of linear maps which
satisfy the naturality condition. -/
@[ext]
structure Hom where
  /-- a family of linear maps `M₁.obj X ⟶ M₂.obj X` for all `X`. -/
  app (X : Cᵒᵖ) : M₁.obj X ⟶ M₂.obj X
  naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
      M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y) =
        app X ≫ M₂.map f := by cat_disch

attribute [reassoc (attr := simp)] Hom.naturality

instance : Category (PresheafOfModules.{v} R) where
  Hom := Hom
  id _ := { app := fun _ ↦ 𝟙 _ }
  comp f g := { app := fun _ ↦ f.app _ ≫ g.app _ }

variable {M₁ M₂}

@[ext]
lemma hom_ext {f g : M₁ ⟶ M₂} (h : ∀ (X : Cᵒᵖ), f.app X = g.app X) :
    f = g := Hom.ext (by ext1; apply h)

@[simp]
lemma id_app (M : PresheafOfModules R) (X : Cᵒᵖ) : Hom.app (𝟙 M) X = 𝟙 _ := rfl

@[simp]
lemma comp_app {M₁ M₂ M₃ : PresheafOfModules R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    (f ≫ g).app X = f.app X ≫ g.app X := rfl

lemma naturality_apply (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X) :
    Hom.app f Y (M₁.map g x) = M₂.map g (Hom.app f X x) :=
  CategoryTheory.congr_fun (Hom.naturality f g) x

/-- Constructor for isomorphisms in the category of presheaves of modules. -/
@[simps!]
def isoMk (app : ∀ (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X)
    (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
      M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y).hom =
        (app X).hom ≫ M₂.map f := by cat_disch) : M₁ ≅ M₂ where
  hom := { app := fun X ↦ (app X).hom }
  inv :=
    { app := fun X ↦ (app X).inv
      naturality := fun {X Y} f ↦ by
        rw [← cancel_epi (app X).hom, ← reassoc_of% (naturality f), Iso.map_hom_inv_id,
          Category.comp_id, Iso.hom_inv_id_assoc]}

/-- The underlying presheaf of abelian groups of a presheaf of modules. -/
noncomputable def presheaf : Cᵒᵖ ⥤ Ab where
  obj X := (forget₂ _ _).obj (M.obj X)
  map f := AddCommGrpCat.ofHom <| AddMonoidHom.mk' (M.map f) (by simp)

@[simp]
lemma presheaf_obj_coe (X : Cᵒᵖ) :
    (M.presheaf.obj X : Type _) = M.obj X := rfl

@[simp]
lemma presheaf_map_apply_coe {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    DFunLike.coe (α := M.obj X) (β := fun _ ↦ M.obj Y) (M.presheaf.map f).hom x = M.map f x := rfl

instance (M : PresheafOfModules R) (X : Cᵒᵖ) :
    Module (R.obj X) (M.presheaf.obj X) :=
  inferInstanceAs (Module (R.obj X) (M.obj X))

variable (R) in
/-- The forgetful functor `PresheafOfModules R ⥤ Cᵒᵖ ⥤ Ab`. -/
noncomputable def toPresheaf : PresheafOfModules.{v} R ⥤ Cᵒᵖ ⥤ Ab where
  obj M := M.presheaf
  map f :=
    { app := fun X ↦ AddCommGrpCat.ofHom <| AddMonoidHom.mk' (Hom.app f X) (by simp)
      naturality := fun X Y g ↦ by ext x; exact naturality_apply f g x }

@[simp]
lemma toPresheaf_obj_coe (X : Cᵒᵖ) :
    (((toPresheaf R).obj M).obj X : Type _) = M.obj X := rfl

@[simp]
lemma toPresheaf_map_app_apply (f : M₁ ⟶ M₂) (X : Cᵒᵖ) (x : M₁.obj X) :
    DFunLike.coe (α := M₁.obj X) (β := fun _ ↦ M₂.obj X)
      (((toPresheaf R).map f).app X).hom x = f.app X x := rfl

instance : (toPresheaf R).Faithful where
  map_injective {_ _ f g} h := by
    ext X x
    exact congr_fun (((evaluation _ _).obj X ⋙ forget _).congr_map h) x

section

variable (M : Cᵒᵖ ⥤ Ab.{v}) [∀ X, Module (R.obj X) (M.obj X)]
  (map_smul : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (r : R.obj X) (m : M.obj X),
    M.map f (r • m) = R.map f r • M.map f m)

/-- The object in `PresheafOfModules R` that is obtained from `M : Cᵒᵖ ⥤ Ab.{v}` such
that for all `X : Cᵒᵖ`, `M.obj X` is a `R.obj X` module, in such a way that the
restriction maps are semilinear. (This constructor should be used only in cases
when the preferred constructor `PresheafOfModules.mk` is not as convenient as this one.) -/
@[simps]
noncomputable def ofPresheaf : PresheafOfModules.{v} R where
  obj X := ModuleCat.of _ (M.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of _ (M.obj Y)))
    { toFun := fun x ↦ M.map f x
      map_add' := by simp
      map_smul' := fun r m ↦ map_smul f r m }

@[simp]
lemma ofPresheaf_presheaf : (ofPresheaf M map_smul).presheaf = M := rfl

end

/-- The morphism of presheaves of modules `M₁ ⟶ M₂` given by a morphism
of abelian presheaves `M₁.presheaf ⟶ M₂.presheaf`
which satisfy a suitable linearity condition. -/
@[simps]
noncomputable def homMk (φ : M₁.presheaf ⟶ M₂.presheaf)
    (hφ : ∀ (X : Cᵒᵖ) (r : R.obj X) (m : M₁.obj X), φ.app X (r • m) = r • φ.app X m) :
    M₁ ⟶ M₂ where
  app X := ModuleCat.ofHom
    { toFun := φ.app X
      map_add' := by simp
      map_smul' := hφ X }
  naturality := fun f ↦ by
    ext x
    exact CategoryTheory.congr_fun (φ.naturality f) x

instance : Zero (M₁ ⟶ M₂) where
  zero := { app := fun _ ↦ 0 }

variable (M₁ M₂) in
@[simp] lemma zero_app (X : Cᵒᵖ) : (0 : M₁ ⟶ M₂).app X = 0 := rfl

instance : Neg (M₁ ⟶ M₂) where
  neg f :=
    { app := fun X ↦ -f.app X
      naturality := fun {X Y} h ↦ by
        ext x
        simp [← naturality_apply] }

instance : Add (M₁ ⟶ M₂) where
  add f g :=
    { app := fun X ↦ f.app X + g.app X
      naturality := fun {X Y} h ↦ by
        ext x
        simp [← naturality_apply] }

instance : Sub (M₁ ⟶ M₂) where
  sub f g :=
    { app := fun X ↦ f.app X - g.app X
      naturality := fun {X Y} h ↦ by
        ext x
        simp [← naturality_apply] }

@[simp] lemma neg_app (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (-f).app X = -f.app X := rfl
@[simp] lemma add_app (f g : M₁ ⟶ M₂) (X : Cᵒᵖ) : (f + g).app X = f.app X + g.app X := rfl
@[simp] lemma sub_app (f g : M₁ ⟶ M₂) (X : Cᵒᵖ) : (f - g).app X = f.app X - g.app X := rfl

instance : AddCommGroup (M₁ ⟶ M₂) where
  add_assoc := by intros; ext1; simp only [add_app, add_assoc]
  zero_add := by intros; ext1; simp only [add_app, zero_app, zero_add]
  neg_add_cancel := by intros; ext1; simp only [add_app, neg_app, neg_add_cancel, zero_app]
  add_zero := by intros; ext1; simp only [add_app, zero_app, add_zero]
  add_comm := by intros; ext1; simp only [add_app]; apply add_comm
  sub_eq_add_neg := by intros; ext1; simp only [add_app, sub_app, neg_app, sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Preadditive (PresheafOfModules R) where

instance : (toPresheaf R).Additive where

lemma zsmul_app (n : ℤ) (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (n • f).app X = n • f.app X := by
  ext x
  change (toPresheaf R ⋙ (evaluation _ _).obj X).map (n • f) x = _
  rw [Functor.map_zsmul]
  rfl

variable (R)

/-- Evaluation on an object `X` gives a functor
`PresheafOfModules R ⥤ ModuleCat (R.obj X)`. -/
@[simps]
def evaluation (X : Cᵒᵖ) : PresheafOfModules.{v} R ⥤ ModuleCat (R.obj X) where
  obj M := M.obj X
  map f := f.app X

instance (X : Cᵒᵖ) : (evaluation.{v} R X).Additive where

/-- The restriction natural transformation on presheaves of modules, considered as linear maps
to restriction of scalars. -/
@[simps]
noncomputable def restriction {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    evaluation R X ⟶ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f).hom where
  app M := M.map f

/-- The obvious free presheaf of modules of rank `1`. -/
noncomputable def unit : PresheafOfModules R where
  obj X := ModuleCat.of _ (R.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of (R.obj Y) (R.obj Y)))
    { toFun := fun x ↦ R.map f x
      map_add' := by simp
      map_smul' := by cat_disch }

lemma unit_map_one {X Y : Cᵒᵖ} (f : X ⟶ Y) : (unit R).map f (1 : R.obj X) = (1 : R.obj Y) :=
  (R.map f).hom.map_one

variable {R}

/-- The type of sections of a presheaf of modules. -/
def sections (M : PresheafOfModules.{v} R) : Type _ := (M.presheaf ⋙ forget _).sections

/-- Given a presheaf of modules `M`, `s : M.sections` and `X : Cᵒᵖ`, this is the induced
element in `M.obj X`. -/
abbrev sections.eval {M : PresheafOfModules.{v} R} (s : M.sections) (X : Cᵒᵖ) : M.obj X := s.1 X

@[simp]
lemma sections_property {M : PresheafOfModules.{v} R} (s : M.sections)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) : M.map f (s.1 X) = s.1 Y := s.2 f

/-- Constructor for sections of a presheaf of modules. -/
@[simps]
def sectionsMk {M : PresheafOfModules.{v} R} (s : ∀ X, M.obj X)
    (hs : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), M.map f (s X) = s Y) : M.sections where
  val := s
  property f := hs f

@[ext]
lemma sections_ext {M : PresheafOfModules.{v} R} (s t : M.sections)
    (h : ∀ (X : Cᵒᵖ), s.val X = t.val X) : s = t :=
  Subtype.ext (by ext; apply h)

/-- The map `M.sections → N.sections` induced by a morphisms `M ⟶ N` of presheaves of modules. -/
@[simps!]
def sectionsMap {M N : PresheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections) : N.sections :=
  N.sectionsMk (fun X ↦ f.app X (s.1 _))
    (fun X Y g ↦ by rw [← naturality_apply, sections_property])

@[simp]
lemma sectionsMap_comp {M N P : PresheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections) :
    sectionsMap (f ≫ g) s = sectionsMap g (sectionsMap f s) := rfl

@[simp]
lemma sectionsMap_id {M : PresheafOfModules.{v} R} (s : M.sections) :
    sectionsMap (𝟙 M) s = s := rfl

/-- The bijection `(unit R ⟶ M) ≃ M.sections` for `M : PresheafOfModules R`. -/
@[simps! apply_coe]
noncomputable def unitHomEquiv (M : PresheafOfModules R) :
    (unit R ⟶ M) ≃ M.sections where
  toFun f := sectionsMk (fun X ↦ Hom.app f X (1 : R.obj X))
    (by intros; rw [← naturality_apply, unit_map_one])
  invFun s :=
    { app := fun X ↦ ModuleCat.ofHom
        ((LinearMap.ringLmapEquivSelf (R.obj X) ℤ (M.obj X)).symm (s.val X))
      naturality := fun {X Y} f ↦ by
        ext
        dsimp
        change R.map f 1 • s.eval Y = M.map f (1 • s.eval X)
        simp }
  left_inv f := by
    ext X : 2
    exact (LinearMap.ringLmapEquivSelf (R.obj X) ℤ (M.obj X)).symm_apply_apply (f.app X).hom
  right_inv s := by
    ext X
    exact (LinearMap.ringLmapEquivSelf (R.obj X) ℤ (M.obj X)).apply_symm_apply (s.val X)

section module_over_initial

variable (X : Cᵒᵖ) (hX : Limits.IsInitial X)

/-!
## `PresheafOfModules R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X)` when `X` is initial

When `X` is initial, we have `Module (R.obj X) (M.obj c)` for any `c : Cᵒᵖ`.

-/

section

variable (M : PresheafOfModules.{v} R)

/-- Auxiliary definition for `forgetToPresheafModuleCatObj`. -/
noncomputable abbrev forgetToPresheafModuleCatObjObj (Y : Cᵒᵖ) : ModuleCat (R.obj X) :=
  (ModuleCat.restrictScalars (R.map (hX.to Y)).hom).obj (M.obj Y)

-- This should not be a `simp` lemma because `M.obj Y` is missing the `Module (R.obj X)` instance,
-- so `simp`ing breaks downstream proofs.
lemma forgetToPresheafModuleCatObjObj_coe (Y : Cᵒᵖ) :
    (forgetToPresheafModuleCatObjObj X hX M Y : Type _) = M.obj Y := rfl

/-- Auxiliary definition for `forgetToPresheafModuleCatObj`. -/
noncomputable def forgetToPresheafModuleCatObjMap {Y Z : Cᵒᵖ} (f : Y ⟶ Z) :
    forgetToPresheafModuleCatObjObj X hX M Y ⟶
      forgetToPresheafModuleCatObjObj X hX M Z :=
  ModuleCat.ofHom
    (X := forgetToPresheafModuleCatObjObj X hX M Y) (Y := forgetToPresheafModuleCatObjObj X hX M Z)
  { toFun := fun x => M.map f x
    map_add' := by simp
    map_smul' := fun r x => by
      simp only [ModuleCat.restrictScalars.smul_def, RingHom.id_apply, M.map_smul]
      rw [← RingCat.comp_apply, ← R.map_comp]
      congr
      apply hX.hom_ext }

@[simp]
lemma forgetToPresheafModuleCatObjMap_apply {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (m : M.obj Y) :
    (forgetToPresheafModuleCatObjMap X hX M f).hom m = M.map f m := rfl

/--
Implementation of the functor `PresheafOfModules R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X)`
when `X` is initial.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
@[simps]
noncomputable def forgetToPresheafModuleCatObj
    (X : Cᵒᵖ) (hX : Limits.IsInitial X) (M : PresheafOfModules.{v} R) :
    Cᵒᵖ ⥤ ModuleCat (R.obj X) where
  obj Y := forgetToPresheafModuleCatObjObj X hX M Y
  map f := forgetToPresheafModuleCatObjMap X hX M f

end

/--
Implementation of the functor `PresheafOfModules R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X)`
when `X` is initial.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
noncomputable def forgetToPresheafModuleCatMap
    (X : Cᵒᵖ) (hX : Limits.IsInitial X) {M N : PresheafOfModules.{v} R} (f : M ⟶ N) :
    forgetToPresheafModuleCatObj X hX M ⟶ forgetToPresheafModuleCatObj X hX N where
  app Y := ModuleCat.ofHom
      (X := (forgetToPresheafModuleCatObj X hX M).obj Y)
      (Y := (forgetToPresheafModuleCatObj X hX N).obj Y)
    { toFun := f.app Y
      map_add' := by simp
      map_smul' := fun r ↦ (f.app Y).hom.map_smul (R.map (hX.to Y) _) }
  naturality Y Z g := by
    ext x
    exact naturality_apply f g x

/--
The forgetful functor from presheaves of modules over a presheaf of rings `R` to presheaves of
`R(X)`-modules where `X` is an initial object.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
@[simps]
noncomputable def forgetToPresheafModuleCat (X : Cᵒᵖ) (hX : Limits.IsInitial X) :
    PresheafOfModules.{v} R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X) where
  obj M := forgetToPresheafModuleCatObj X hX M
  map f := forgetToPresheafModuleCatMap X hX f

end module_over_initial

end PresheafOfModules
