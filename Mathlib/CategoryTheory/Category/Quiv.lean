/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# The category of quivers

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `Quiv`.
-/

universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
/-- Category of quivers. -/
@[nolint checkUnivs]
def Quiv :=
  Bundled Quiver.{v + 1, u}

namespace Quiv

instance : CoeSort Quiv (Type u) where coe := Bundled.α

instance str' (C : Quiv.{v, u}) : Quiver.{v + 1, u} C :=
  C.str

/-- Construct a bundled `Quiv` from the underlying type and the typeclass. -/
def of (C : Type u) [Quiver.{v + 1} C] : Quiv.{v, u} :=
  Bundled.of C

instance : Inhabited Quiv :=
  ⟨Quiv.of (Quiver.Empty PEmpty)⟩

/-- Category structure on `Quiv` -/
instance category : LargeCategory.{max v u} Quiv.{v, u} where
  Hom C D := Prefunctor C D
  id C := Prefunctor.id C
  comp F G := Prefunctor.comp F G

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ Quiv.{v, u} where
  obj C := Quiv.of C
  map F := F.toPrefunctor

/-- The identity in the category of quivers equals the identity prefunctor. -/
theorem id_eq_id (X : Quiv) : 𝟙 X = 𝟭q X := rfl

/-- Composition in the category of quivers equals prefunctor composition. -/
theorem comp_eq_comp {X Y Z : Quiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙q G := rfl

end Quiv

namespace Cat

/-- The functor sending each quiver to its path category. -/
@[simps]
def free : Quiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (Paths V)
  map F :=
    { obj := fun X => F.obj X
      map := fun f => F.mapPath f
      map_comp := fun f g => F.mapPath_comp f g }
  map_id V := by
    change (show Paths V ⥤ _ from _) = _
    ext
    · rfl
    · exact eq_conj_eqToHom _
  map_comp {U _ _} F G := by
    change (show Paths U ⥤ _ from _) = _
    ext
    · rfl
    · exact eq_conj_eqToHom _

end Cat

namespace Quiv

section
variable {V W : Quiv} (e : V ≅ W)

/-- An isomorphism of quivers defines an equivalence on carrier types. -/
@[simps]
def equivOfIso : V ≃ W where
  toFun := e.hom.obj
  invFun := e.inv.obj
  left_inv := Prefunctor.congr_obj e.hom_inv_id
  right_inv := Prefunctor.congr_obj e.inv_hom_id

@[simp]
lemma inv_obj_hom_obj_of_iso (X : V) : e.inv.obj (e.hom.obj X) = X := (equivOfIso e).left_inv X

@[simp]
lemma hom_obj_inv_obj_of_iso (Y : W) : e.hom.obj (e.inv.obj Y) = Y := (equivOfIso e).right_inv Y

lemma hom_map_inv_map_of_iso {V W : Quiv} (e : V ≅ W) {X Y : W} (f : X ⟶ Y) :
    e.hom.map (e.inv.map f) = Quiver.homOfEq f (by simp) (by simp) := by
  rw [← Prefunctor.comp_map]
  exact (Prefunctor.congr_hom e.inv_hom_id.symm f).symm

lemma inv_map_hom_map_of_iso {V W : Quiv} (e : V ≅ W) {X Y : V} (f : X ⟶ Y) :
    e.inv.map (e.hom.map f) = Quiver.homOfEq f (by simp) (by simp) :=
  hom_map_inv_map_of_iso e.symm f

/-- An isomorphism of quivers defines an equivalence on hom types. -/
@[simps]
def homEquivOfIso {V W : Quiv} (e : V ≅ W) {X Y : V} :
    (X ⟶ Y) ≃ (e.hom.obj X ⟶ e.hom.obj Y) where
  toFun f := e.hom.map f
  invFun g := Quiver.homOfEq (e.inv.map g) (by simp) (by simp)
  left_inv f := by simp [inv_map_hom_map_of_iso]
  right_inv g := by simp [hom_map_inv_map_of_iso]

end

section
variable {V W : Type u} [Quiver V] [Quiver W]
  (e : V ≃ W) (he : ∀ X Y : V, (X ⟶ Y) ≃ (e X ⟶ e Y))

include he in
@[simp]
lemma homOfEq_map_homOfEq {X Y : V} (f : X ⟶ Y) {X' Y' : V} (hX : X = X') (hY : Y = Y')
    {X'' Y'' : W} (hX' : e X' = X'') (hY' : e Y' = Y'') :
    Quiver.homOfEq (he _ _ (Quiver.homOfEq f hX hY)) hX' hY' =
      Quiver.homOfEq (he _ _ f) (by rw [hX, hX']) (by rw [hY, hY']) := by
  subst hX hY hX' hY'
  rfl

/-- Compatible equivalences of types and hom-types induce an isomorphism of quivers. -/
def isoOfEquiv : Quiv.of V ≅ Quiv.of W where
  hom := Prefunctor.mk e (he _ _)
  inv :=
    { obj := e.symm
      map {X Y} f := (he _ _).symm (Quiver.homOfEq f (by simp) (by simp)) }
  hom_inv_id := Prefunctor.ext' e.left_inv (fun X Y f ↦ by
    dsimp [Quiv.id_eq_id, Quiv.comp_eq_comp]
    apply (he _ _).injective
    apply Quiver.homOfEq_injective (X' := e X) (Y' := e Y) (by simp) (by simp)
    simp)
  inv_hom_id := Prefunctor.ext' e.right_inv (by simp [Quiv.id_eq_id, Quiv.comp_eq_comp])

end

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
def lift {V : Type u} [Quiver.{v + 1} V] {C : Type*} [Category C] (F : Prefunctor V C) :
    Paths V ⥤ C where
  obj X := F.obj X
  map f := composePath (F.mapPath f)

-- We might construct `of_lift_iso_self : Paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!
/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
def adj : Cat.free ⊣ Quiv.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun V C =>
        { toFun := fun F => Paths.of.comp F.toPrefunctor
          invFun := fun F => @lift V _ C _ F
          left_inv := fun F => Paths.ext_functor rfl (by simp)
          right_inv := by
            rintro ⟨obj, map⟩
            dsimp only [Prefunctor.comp]
            congr
            funext X Y f
            exact Category.id_comp _ }
      homEquiv_naturality_left_symm := fun {V _ _} f g => by
        change (show Paths V ⥤ _ from _) = _
        ext
        · rfl
        · apply eq_conj_eqToHom }

end Quiv

end CategoryTheory
