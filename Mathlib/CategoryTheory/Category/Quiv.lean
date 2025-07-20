/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Emily Riehl, Joël Riou
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# The category of quivers

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `Quiv`.
-/

universe v u v₁ v₂ v₃ u₁ u₂ u₃ w

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

namespace Prefunctor

/-- Prefunctors between quivers define arrows in `Quiv`. -/
def toQuivHom {C D : Type u} [Quiver.{v + 1} C] [Quiver.{v + 1} D] (F : C ⥤q D) :
    Quiv.of C ⟶ Quiv.of D := F

/-- Arrows in `Quiv` define prefunctors. -/
def ofQuivHom {C D : Quiv} (F : C ⟶ D) : C ⥤q D := F

@[simp] theorem to_ofQuivHom {C D : Quiv} (F : C ⟶ D) : toQuivHom (ofQuivHom F) = F := rfl

@[simp] theorem of_toQuivHom {C D : Type} [Quiver C] [Quiver D] (F : C ⥤q D) :
    ofQuivHom (toQuivHom F) = F := rfl

end Prefunctor
namespace Cat

/-- A prefunctor `V ⥤q W` induces a functor between the path categories defined by `F.mapPath`. -/
@[simps]
def freeMap {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W) : Paths V ⥤ Paths W where
  obj := F.obj
  map := F.mapPath
  map_comp f g := F.mapPath_comp f g

/-- The functor `free : Quiv ⥤ Cat` preserves identities up to natural isomorphism and in fact up
to equality. -/
@[simps!]
def freeMapIdIso (V : Type*) [Quiver V] : freeMap (𝟭q V) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

theorem freeMap_id (V : Type*) [Quiver V] :
    freeMap (𝟭q V) = 𝟭 _ :=
  Functor.ext_of_iso (freeMapIdIso V) (fun _ ↦ rfl)

/-- The functor `free : Quiv ⥤ Cat` preserves composition up to natural isomorphism and in fact up
to equality. -/
@[simps!]
def freeMapCompIso {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
    [Quiver.{v₁ + 1} V₁] [Quiver.{v₂ + 1} V₂] [Quiver.{v₃ + 1} V₃] (F : V₁ ⥤q V₂) (G : V₂ ⥤q V₃) :
    freeMap (F ⋙q G) ≅ freeMap F ⋙ freeMap G :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    dsimp
    simp only [Category.comp_id, Category.id_comp, Prefunctor.mapPath_comp_apply])

theorem freeMap_comp {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
    [Quiver.{v₁ + 1} V₁] [Quiver.{v₂ + 1} V₂] [Quiver.{v₃ + 1} V₃]
    (F : V₁ ⥤q V₂) (G : V₂ ⥤q V₃) :
    freeMap (F ⋙q G) = freeMap F ⋙ freeMap G :=
  Functor.ext_of_iso (freeMapCompIso F G) (fun _ ↦ rfl)

/-- The functor sending each quiver to its path category. -/
@[simps]
def free : Quiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (Paths V)
  map F := Functor.toCatHom (freeMap (Prefunctor.ofQuivHom F))
  map_id _ := freeMap_id _
  map_comp _ _ := freeMap_comp _ _

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
def lift {V : Type u} [Quiver.{v + 1} V] {C : Type u₁} [Category.{v₁} C]
    (F : Prefunctor V C) : Paths V ⥤ C where
  obj X := F.obj X
  map f := composePath (F.mapPath f)

/-- Naturality of `pathComposition`. -/
def pathCompositionNaturality {C : Type u} {D : Type u₁}
    [Category.{v} C] [Category.{v₁} D] (F : C ⥤ D) :
    Cat.freeMap (F.toPrefunctor) ⋙ pathComposition D ≅ pathComposition C ⋙ F :=
  Paths.liftNatIso (fun _ ↦ Iso.refl _) (by simp)

/-- Naturality of `pathComposition`, which defines a natural transformation
`Quiv.forget ⋙ Cat.free ⟶ 𝟭 _`. -/
theorem pathComposition_naturality {C : Type u} {D : Type u₁}
    [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D) : Cat.freeMap (F.toPrefunctor) ⋙ pathComposition D = pathComposition C ⋙ F :=
  Paths.ext_functor rfl (by simp)

/-- Naturality of `Paths.of`, which defines a natural transformation
` 𝟭 _⟶ Cat.free ⋙ Quiv.forget`. -/
lemma pathsOf_freeMap_toPrefunctor
    {V : Type u} {W : Type u₁} [Quiver.{v + 1} V] [Quiver.{v₁ + 1} W] (F : V ⥤q W) :
  Paths.of V ⋙q (Cat.freeMap F).toPrefunctor = F ⋙q Paths.of W := rfl

/-- The left triangle identity of `Cat.free ⊣ Quiv.forget` as a natural isomorphism -/
def freeMapPathsOfCompPathCompositionIso (V : Type u) [Quiver.{v + 1} V] :
    Cat.freeMap (Paths.of V) ⋙ pathComposition (Paths V) ≅ 𝟭 (Paths V) :=
  Paths.liftNatIso (fun v ↦ Iso.refl _) (by simp)

lemma freeMap_pathsOf_pathComposition (V : Type u) [Quiver.{v + 1} V] :
    Cat.freeMap (Paths.of (V := V)) ⋙ pathComposition (Paths V) = 𝟭 (Paths V) :=
  Paths.ext_functor rfl (by simp)

/-- An unbundled version of the right triangle equality. -/
lemma pathsOf_pathComposition_toPrefunctor (C : Type u) [Category.{v} C] :
    Paths.of C ⋙q (pathComposition C).toPrefunctor = 𝟭q C := by
  dsimp only [Prefunctor.comp]
  congr
  funext X Y f
  exact Category.id_comp _

/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
def adj : Cat.free ⊣ Quiv.forget :=
  Adjunction.mkOfUnitCounit {
    unit := { app _ := Paths.of _}
    counit := {
      app C := pathComposition C
      naturality _ _ F := pathComposition_naturality F
    }
    left_triangle := by
      ext V
      exact freeMap_pathsOf_pathComposition V
    right_triangle := by
      ext C
      exact pathsOf_pathComposition_toPrefunctor C
  }

/-- The universal property of the path category of a quiver. -/
def pathsEquiv {V : Type u} {C : Type u₁} [Quiver.{v + 1} V] [Category.{v₁} C] :
    (Paths V ⥤ C) ≃ V ⥤q C where
  toFun F := (Paths.of V).comp F.toPrefunctor
  invFun G := Cat.freeMap G ⋙ pathComposition C
  left_inv F := by
    dsimp
    rw [Cat.freeMap_comp, Functor.assoc, pathComposition_naturality, ← Functor.assoc,
      freeMap_pathsOf_pathComposition, Functor.id_comp]
  right_inv G := by
    dsimp
    rw [← Functor.toPrefunctor_comp, ← Prefunctor.comp_assoc,
      pathsOf_freeMap_toPrefunctor, Prefunctor.comp_assoc,
      pathsOf_pathComposition_toPrefunctor, Prefunctor.comp_id]

@[simp]
lemma adj_homEquiv {V C : Type u} [Quiver.{max u v + 1} V] [Category.{max u v} C] :
    adj.homEquiv (Quiv.of V) (Cat.of C) = pathsEquiv (V := V) (C := C) := rfl

end Quiv

end CategoryTheory
