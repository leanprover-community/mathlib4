/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Quotient
import Mathlib.Combinatorics.Quiver.Path

#align_import category_theory.path_category from "leanprover-community/mathlib"@"c6dd521ebdce53bb372c527569dd7c25de53a08b"

/-!
# The category paths on a quiver.
When `C` is a quiver, `paths C` is the category of paths.

## When the quiver is itself a category
We provide `path_composition : paths C ⥤ C`.

We check that the quotient of the path category of a category by the canonical relation
(paths are related if they compose to the same path) is equivalent to the original category.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

/-- A type synonym for the category of paths in a quiver.
-/
def Paths (V : Type u₁) : Type u₁ := V
#align category_theory.paths CategoryTheory.Paths

instance (V : Type u₁) [Inhabited V] : Inhabited (Paths V) := ⟨(default : V)⟩

variable (V : Type u₁) [Quiver.{v₁ + 1} V]

namespace Paths

instance categoryPaths : Category.{max u₁ v₁} (Paths V) where
  Hom := fun X Y : V => Quiver.Path X Y
  id X := Quiver.Path.nil
  comp f g := Quiver.Path.comp f g
#align category_theory.paths.category_paths CategoryTheory.Paths.categoryPaths

variable {V}

/-- The inclusion of a quiver `V` into its path category, as a prefunctor.
-/
@[simps]
def of : V ⥤q Paths V where
  obj X := X
  map f := f.toPath
#align category_theory.paths.of CategoryTheory.Paths.of

attribute [local ext] Functor.ext

/-- Any prefunctor from `V` lifts to a functor from `paths V` -/
def lift {C} [Category C] (φ : V ⥤q C) : Paths V ⥤ C where
  obj := φ.obj
  map {X} {Y} f :=
    @Quiver.Path.rec V _ X (fun Y _ => φ.obj X ⟶ φ.obj Y) (𝟙 <| φ.obj X)
      (fun _ f ihp => ihp ≫ φ.map f) Y f
  map_id X := rfl
  map_comp f g := by
    induction' g with _ _ g' p ih _ _ _
    · rw [Category.comp_id]
      rfl
    · have : f ≫ Quiver.Path.cons g' p = (f ≫ g').cons p := by apply Quiver.Path.comp_cons
      rw [this]
      simp only at ih ⊢
      rw [ih, Category.assoc]
#align category_theory.paths.lift CategoryTheory.Paths.lift

@[simp]
theorem lift_nil {C} [Category C] (φ : V ⥤q C) (X : V) :
    (lift φ).map Quiver.Path.nil = 𝟙 (φ.obj X) := rfl
#align category_theory.paths.lift_nil CategoryTheory.Paths.lift_nil

@[simp]
theorem lift_cons {C} [Category C] (φ : V ⥤q C) {X Y Z : V} (p : Quiver.Path X Y) (f : Y ⟶ Z) :
    (lift φ).map (p.cons f) = (lift φ).map p ≫ φ.map f := rfl
#align category_theory.paths.lift_cons CategoryTheory.Paths.lift_cons

@[simp]
theorem lift_toPath {C} [Category C] (φ : V ⥤q C) {X Y : V} (f : X ⟶ Y) :
    (lift φ).map f.toPath = φ.map f := by
  dsimp [Quiver.Hom.toPath, lift]
  simp
#align category_theory.paths.lift_to_path CategoryTheory.Paths.lift_toPath

theorem lift_spec {C} [Category C] (φ : V ⥤q C) : of ⋙q (lift φ).toPrefunctor = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rcases φ with ⟨φo, φm⟩
    dsimp [lift, Quiver.Hom.toPath]
    simp only [Category.id_comp]
#align category_theory.paths.lift_spec CategoryTheory.Paths.lift_spec

theorem lift_unique {C} [Category C] (φ : V ⥤q C) (Φ : Paths V ⥤ C)
    (hΦ : of ⋙q Φ.toPrefunctor = φ) : Φ = lift φ := by
  subst_vars
  fapply Functor.ext
  · rintro X
    rfl
  · rintro X Y f
    dsimp [lift]
    induction' f with _ _ p f' ih
    · simp only [Category.comp_id]
      apply Functor.map_id
    · simp only [Category.comp_id, Category.id_comp] at ih ⊢
      -- Porting note: Had to do substitute `p.cons f'` and `f'.toPath` by their fully qualified
      -- versions in this `have` clause (elsewhere too).
      have : Φ.map (Quiver.Path.cons p f') = Φ.map p ≫ Φ.map (Quiver.Hom.toPath f') := by
        convert Functor.map_comp Φ p (Quiver.Hom.toPath f')
      rw [this, ih]
#align category_theory.paths.lift_unique CategoryTheory.Paths.lift_unique

/-- Two functors out of a path category are equal when they agree on singleton paths. -/
@[ext]
theorem ext_functor {C} [Category C] {F G : Paths V ⥤ C} (h_obj : F.obj = G.obj)
    (h : ∀ (a b : V) (e : a ⟶ b), F.map e.toPath =
        eqToHom (congr_fun h_obj a) ≫ G.map e.toPath ≫ eqToHom (congr_fun h_obj.symm b)) :
    F = G := by
  fapply Functor.ext
  · intro X
    rw [h_obj]
  · intro X Y f
    induction' f with Y' Z' g e ih
    · erw [F.map_id, G.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
    · erw [F.map_comp g (Quiver.Hom.toPath e), G.map_comp g (Quiver.Hom.toPath e), ih, h]
      simp only [Category.id_comp, eqToHom_refl, eqToHom_trans_assoc, Category.assoc]
#align category_theory.paths.ext_functor CategoryTheory.Paths.ext_functor

end Paths

variable (W : Type u₂) [Quiver.{v₂ + 1} W]

-- A restatement of `Prefunctor.mapPath_comp` using `f ≫ g` instead of `f.comp g`.
@[simp]
theorem Prefunctor.mapPath_comp' (F : V ⥤q W) {X Y Z : Paths V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.mapPath (f ≫ g) = (F.mapPath f).comp (F.mapPath g) :=
  Prefunctor.mapPath_comp _ _ _
#align category_theory.prefunctor.map_path_comp' CategoryTheory.Prefunctor.mapPath_comp'

end

section

variable {C : Type u₁} [Category.{v₁} C]

open Quiver

-- Porting note:
-- This def was originally marked `@[simp]`, but the meaning is different in lean4: lean4#2042
-- So, the `@[simp]` was removed, and the two equational lemmas below added instead.
/-- A path in a category can be composed to a single morphism. -/
def composePath {X : C} : ∀ {Y : C} (_ : Path X Y), X ⟶ Y
  | _, .nil => 𝟙 X
  | _, .cons p e => composePath p ≫ e
#align category_theory.compose_path CategoryTheory.composePath

@[simp] lemma composePath_nil {X : C} : composePath (Path.nil : Path X X) = 𝟙 X := rfl

@[simp] lemma composePath_cons {X Y Z : C} (p : Path X Y) (e : Y ⟶ Z) :
  composePath (p.cons e) = composePath p ≫ e := rfl

@[simp]
theorem composePath_toPath {X Y : C} (f : X ⟶ Y) : composePath f.toPath = f := Category.id_comp _
#align category_theory.compose_path_to_path CategoryTheory.composePath_toPath

@[simp]
theorem composePath_comp {X Y Z : C} (f : Path X Y) (g : Path Y Z) :
    composePath (f.comp g) = composePath f ≫ composePath g := by
  induction' g with Y' Z' g e ih
  · simp
  · simp [ih]
#align category_theory.compose_path_comp CategoryTheory.composePath_comp

@[simp]
-- Porting note (#11215): TODO get rid of `(id X : C)` somehow?
theorem composePath_id {X : Paths C} : composePath (𝟙 X) = 𝟙 (id X : C) := rfl
#align category_theory.compose_path_id CategoryTheory.composePath_id

@[simp]
theorem composePath_comp' {X Y Z : Paths C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    composePath (f ≫ g) = composePath f ≫ composePath g :=
  composePath_comp f g
#align category_theory.compose_path_comp' CategoryTheory.composePath_comp'

variable (C)

/-- Composition of paths as functor from the path category of a category to the category. -/
@[simps]
def pathComposition : Paths C ⥤ C where
  obj X := X
  map f := composePath f
#align category_theory.path_composition CategoryTheory.pathComposition

-- TODO: This, and what follows, should be generalized to
-- the `HomRel` for the kernel of any functor.
-- Indeed, this should be part of an equivalence between congruence relations on a category `C`
-- and full, essentially surjective functors out of `C`.
/-- The canonical relation on the path category of a category:
two paths are related if they compose to the same morphism. -/
@[simp]
def pathsHomRel : HomRel (Paths C) := fun _ _ p q =>
  (pathComposition C).map p = (pathComposition C).map q
#align category_theory.paths_hom_rel CategoryTheory.pathsHomRel

/-- The functor from a category to the canonical quotient of its path category. -/
@[simps]
def toQuotientPaths : C ⥤ Quotient (pathsHomRel C) where
  obj X := Quotient.mk X
  map f := Quot.mk _ f.toPath
  map_id X := Quot.sound (Quotient.CompClosure.of _ _ _ (by simp))
  map_comp f g := Quot.sound (Quotient.CompClosure.of _ _ _ (by simp))
#align category_theory.to_quotient_paths CategoryTheory.toQuotientPaths

/-- The functor from the canonical quotient of a path category of a category
to the original category. -/
@[simps!]
def quotientPathsTo : Quotient (pathsHomRel C) ⥤ C :=
  Quotient.lift _ (pathComposition C) fun _ _ _ _ w => w
#align category_theory.quotient_paths_to CategoryTheory.quotientPathsTo

/-- The canonical quotient of the path category of a category
is equivalent to the original category. -/
def quotientPathsEquiv : Quotient (pathsHomRel C) ≌ C where
  functor := quotientPathsTo C
  inverse := toQuotientPaths C
  unitIso :=
    NatIso.ofComponents
      (fun X => by cases X; rfl)
      (Quot.ind fun f => by
        apply Quot.sound
        apply Quotient.CompClosure.of
        simp [Category.comp_id, Category.id_comp, pathsHomRel])
  counitIso := NatIso.ofComponents (fun X => Iso.refl _) (fun f => by simp [Quot.liftOn_mk])
  functor_unitIso_comp X := by
    cases X
    simp only [pathsHomRel, pathComposition_obj, pathComposition_map, Functor.id_obj,
               quotientPathsTo_obj, Functor.comp_obj, toQuotientPaths_obj_as,
               NatIso.ofComponents_hom_app, Iso.refl_hom, quotientPathsTo_map, Category.comp_id]
    rfl
#align category_theory.quotient_paths_equiv CategoryTheory.quotientPathsEquiv

end

end CategoryTheory
