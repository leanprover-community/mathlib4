/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Geometry.RingedSpace.Stalks

#align_import algebraic_geometry.locally_ringed_space from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# The category of locally ringed spaces

We define (bundled) locally ringed spaces (as `SheafedSpace CommRing` along with the fact that the
stalks are local rings), and morphisms between these (morphisms in `SheafedSpace` with
`is_local_ring_hom` on the stalk maps).
-/

-- Explicit universe annotations were used in this file to improve perfomance #12737

universe u

open CategoryTheory

open TopCat

open TopologicalSpace

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

namespace AlgebraicGeometry

/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphisms induced on stalks are local ring homomorphisms. -/
structure LocallyRingedSpace extends SheafedSpace CommRingCat.{u} where
  /-- Stalks of a locally ringed space are local rings. -/
  localRing : ∀ x, LocalRing (presheaf.stalk x)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace AlgebraicGeometry.LocallyRingedSpace

attribute [instance] LocallyRingedSpace.localRing

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- An alias for `to_SheafedSpace`, where the result type is a `RingedSpace`.
This allows us to use dot-notation for the `RingedSpace` namespace.
 -/
def toRingedSpace : RingedSpace :=
  X.toSheafedSpace
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.to_RingedSpace AlgebraicGeometry.LocallyRingedSpace.toRingedSpace

/-- The underlying topological space of a locally ringed space. -/
def toTopCat : TopCat :=
  X.1.carrier
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.to_Top AlgebraicGeometry.LocallyRingedSpace.toTopCat

instance : CoeSort LocallyRingedSpace (Type u) :=
  ⟨fun X : LocallyRingedSpace => (X.toTopCat : Type _)⟩

instance (x : X) : LocalRing (X.stalk x) :=
  X.localRing x

-- PROJECT: how about a typeclass "has_structure_sheaf" to mediate the 𝒪 notation, rather
-- than defining it over and over for PresheafedSpace, LRS, Scheme, etc.
/-- The structure sheaf of a locally ringed space. -/
def 𝒪 : Sheaf CommRingCat X.toTopCat :=
  X.sheaf
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.𝒪 AlgebraicGeometry.LocallyRingedSpace.𝒪

/-- A morphism of locally ringed spaces is a morphism of ringed spaces
 such that the morphisms induced on stalks are local ring homomorphisms. -/
@[ext]
structure Hom (X Y : LocallyRingedSpace.{u}) : Type _ where
  /-- the underlying morphism between ringed spaces -/
  val : X.toSheafedSpace ⟶ Y.toSheafedSpace
  /-- the underlying morphism induces a local ring homomorphism on stalks -/
  prop : ∀ x, IsLocalRingHom (PresheafedSpace.stalkMap val x)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.hom AlgebraicGeometry.LocallyRingedSpace.Hom

instance : Quiver LocallyRingedSpace :=
  ⟨Hom⟩

@[ext] lemma Hom.ext' (X Y : LocallyRingedSpace.{u}) {f g : X ⟶ Y} (h : f.val = g.val) : f = g :=
  Hom.ext _ _ h

-- TODO perhaps we should make a bundled `LocalRing` and return one here?
-- TODO define `sheaf.stalk` so we can write `X.𝒪.stalk` here?
/-- The stalk of a locally ringed space, just as a `CommRing`.
-/
noncomputable def stalk (X : LocallyRingedSpace.{u}) (x : X) : CommRingCat :=
  X.presheaf.stalk x
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.stalk AlgebraicGeometry.LocallyRingedSpace.stalk

-- Porting note (#10754): added this instance to help Lean realize stalks are local
-- (so that `0 ≠ 1` works below)
instance stalkLocal (x : X) : LocalRing <| X.stalk x := X.localRing x

/-- A morphism of locally ringed spaces `f : X ⟶ Y` induces
a local ring homomorphism from `Y.stalk (f x)` to `X.stalk x` for any `x : X`.
-/
noncomputable def stalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    Y.stalk (f.1.1 x) ⟶ X.stalk x :=
  PresheafedSpace.stalkMap f.1 x
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.stalk_map AlgebraicGeometry.LocallyRingedSpace.stalkMap

instance {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) : IsLocalRingHom (stalkMap f x) :=
  f.2 x

instance {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalRingHom (PresheafedSpace.stalkMap f.1 x) :=
  f.2 x

/-- The identity morphism on a locally ringed space. -/
@[simps]
def id (X : LocallyRingedSpace.{u}) : Hom X X :=
  ⟨𝟙 _, fun x => by erw [PresheafedSpace.stalkMap.id]; apply isLocalRingHom_id⟩
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.id AlgebraicGeometry.LocallyRingedSpace.id

instance (X : LocallyRingedSpace.{u}) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of locally ringed spaces. -/
def comp {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨f.val ≫ g.val, fun x => by
    erw [PresheafedSpace.stalkMap.comp]
    exact @isLocalRingHom_comp _ _ _ _ _ _ _ _ (f.2 _) (g.2 _)⟩
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.comp AlgebraicGeometry.LocallyRingedSpace.comp

/-- The category of locally ringed spaces. -/
instance : Category LocallyRingedSpace.{u} where
  Hom := Hom
  id := id
  comp {X Y Z} f g := comp f g
  comp_id {X Y} f := Hom.ext _ _ <| by simp [comp]
  id_comp {X Y} f := Hom.ext _ _ <| by simp [comp]
  assoc {_ _ _ _} f g h := Hom.ext _ _ <| by simp [comp]

/-- The forgetful functor from `LocallyRingedSpace` to `SheafedSpace CommRing`. -/
@[simps]
def forgetToSheafedSpace : LocallyRingedSpace.{u} ⥤ SheafedSpace CommRingCat.{u} where
  obj X := X.toSheafedSpace
  map {X Y} f := f.1
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.forget_to_SheafedSpace AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace

instance : forgetToSheafedSpace.Faithful where
  map_injective {_ _} _ _ h := Hom.ext _ _ h

/-- The forgetful functor from `LocallyRingedSpace` to `Top`. -/
@[simps!]
def forgetToTop : LocallyRingedSpace.{u} ⥤ TopCat.{u} :=
  forgetToSheafedSpace ⋙ SheafedSpace.forget _
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.forget_to_Top AlgebraicGeometry.LocallyRingedSpace.forgetToTop

@[simp]
theorem comp_val {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.comp_val AlgebraicGeometry.LocallyRingedSpace.comp_val

@[simp] theorem id_val' (X : LocallyRingedSpace.{u}) : Hom.val (𝟙 X) = 𝟙 X.toSheafedSpace :=
  rfl

-- Porting note: complains that `(f ≫ g).val.c` can be further simplified
-- so changed to its simp normal form `(f.val ≫ g.val).c`
@[simp]
theorem comp_val_c {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f.1 ≫ g.1).c = g.val.c ≫ (Presheaf.pushforward _ g.val.base).map f.val.c :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.comp_val_c AlgebraicGeometry.LocallyRingedSpace.comp_val_c

theorem comp_val_c_app {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : (Opens Z)ᵒᵖ) :
    (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app (op <| (Opens.map g.val.base).obj U.unop) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.comp_val_c_app AlgebraicGeometry.LocallyRingedSpace.comp_val_c_app

/-- Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to a morphism `X ⟶ Y` as locally ringed spaces.

See also `iso_of_SheafedSpace_iso`.
-/
@[simps]
def homOfSheafedSpaceHomOfIsIso {X Y : LocallyRingedSpace.{u}}
    (f : X.toSheafedSpace ⟶ Y.toSheafedSpace) [IsIso f] : X ⟶ Y :=
  Hom.mk f fun x =>
    -- Here we need to see that the stalk maps are really local ring homomorphisms.
    -- This can be solved by type class inference, because stalk maps of isomorphisms
    -- are isomorphisms and isomorphisms are local ring homomorphisms.
    show IsLocalRingHom (PresheafedSpace.stalkMap (SheafedSpace.forgetToPresheafedSpace.map f) x) by
      infer_instance
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.hom_of_SheafedSpace_hom_of_is_iso AlgebraicGeometry.LocallyRingedSpace.homOfSheafedSpaceHomOfIsIso

/-- Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to an isomorphism `X ⟶ Y` as locally ringed spaces.

This is related to the property that the functor `forget_to_SheafedSpace` reflects isomorphisms.
In fact, it is slightly stronger as we do not require `f` to come from a morphism between
_locally_ ringed spaces.
-/
def isoOfSheafedSpaceIso {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ≅ Y.toSheafedSpace) :
    X ≅ Y where
  hom := homOfSheafedSpaceHomOfIsIso f.hom
  inv := homOfSheafedSpaceHomOfIsIso f.inv
  hom_inv_id := Hom.ext _ _ f.hom_inv_id
  inv_hom_id := Hom.ext _ _ f.inv_hom_id
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.iso_of_SheafedSpace_iso AlgebraicGeometry.LocallyRingedSpace.isoOfSheafedSpaceIso

instance : forgetToSheafedSpace.ReflectsIsomorphisms where reflects {_ _} f i :=
  { out :=
      ⟨homOfSheafedSpaceHomOfIsIso (CategoryTheory.inv (forgetToSheafedSpace.map f)),
        Hom.ext _ _ (IsIso.hom_inv_id (I := i)), Hom.ext _ _ (IsIso.inv_hom_id (I := i))⟩ }

instance is_sheafedSpace_iso {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f] : IsIso f.1 :=
  LocallyRingedSpace.forgetToSheafedSpace.map_isIso f
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.is_SheafedSpace_iso AlgebraicGeometry.LocallyRingedSpace.is_sheafedSpace_iso

/-- The restriction of a locally ringed space along an open embedding.
-/
@[simps!]
def restrict {U : TopCat} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat} (h : OpenEmbedding f) :
    LocallyRingedSpace where
  localRing := by
    intro x
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    apply @RingEquiv.localRing _ _ _ (X.localRing (f x))
    exact (X.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
  toSheafedSpace := X.toSheafedSpace.restrict h
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.restrict AlgebraicGeometry.LocallyRingedSpace.restrict

/-- The canonical map from the restriction to the subspace. -/
def ofRestrict {U : TopCat} (X : LocallyRingedSpace.{u})
    {f : U ⟶ X.toTopCat} (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  ⟨X.toPresheafedSpace.ofRestrict h, fun _ => inferInstance⟩
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.of_restrict AlgebraicGeometry.LocallyRingedSpace.ofRestrict

/-- The restriction of a locally ringed space `X` to the top subspace is isomorphic to `X` itself.
-/
def restrictTopIso (X : LocallyRingedSpace.{u}) :
    X.restrict (Opens.openEmbedding ⊤) ≅ X :=
  isoOfSheafedSpaceIso X.toSheafedSpace.restrictTopIso
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.restrict_top_iso AlgebraicGeometry.LocallyRingedSpace.restrictTopIso

/-- The global sections, notated Gamma.
-/
def Γ : LocallyRingedSpace.{u}ᵒᵖ ⥤ CommRingCat.{u} :=
  forgetToSheafedSpace.op ⋙ SheafedSpace.Γ
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.Γ AlgebraicGeometry.LocallyRingedSpace.Γ

theorem Γ_def : Γ = forgetToSheafedSpace.op ⋙ SheafedSpace.Γ :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.Γ_def AlgebraicGeometry.LocallyRingedSpace.Γ_def

@[simp]
theorem Γ_obj (X : LocallyRingedSpace.{u}ᵒᵖ) : Γ.obj X = X.unop.presheaf.obj (op ⊤) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.Γ_obj AlgebraicGeometry.LocallyRingedSpace.Γ_obj

theorem Γ_obj_op (X : LocallyRingedSpace.{u}) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.Γ_obj_op AlgebraicGeometry.LocallyRingedSpace.Γ_obj_op

@[simp]
theorem Γ_map {X Y : LocallyRingedSpace.{u}ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.1.c.app (op ⊤) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.Γ_map AlgebraicGeometry.LocallyRingedSpace.Γ_map

theorem Γ_map_op {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) : Γ.map f.op = f.1.c.app (op ⊤) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.Γ_map_op AlgebraicGeometry.LocallyRingedSpace.Γ_map_op

theorem preimage_basicOpen {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {U : Opens Y}
    (s : Y.presheaf.obj (op U)) :
    (Opens.map f.1.base).obj (Y.toRingedSpace.basicOpen s) =
      @RingedSpace.basicOpen X.toRingedSpace ((Opens.map f.1.base).obj U) (f.1.c.app _ s) := by
  ext x
  constructor
  · rintro ⟨⟨y, hyU⟩, hy : IsUnit _, rfl : y = _⟩
    erw [RingedSpace.mem_basicOpen _ _ ⟨x, show x ∈ (Opens.map f.1.base).obj U from hyU⟩,
      ← PresheafedSpace.stalkMap_germ_apply]
    exact (PresheafedSpace.stalkMap f.1 _).isUnit_map hy
  · rintro ⟨y, hy : IsUnit _, rfl⟩
    erw [RingedSpace.mem_basicOpen _ _ ⟨f.1.base y.1, y.2⟩]
    erw [← PresheafedSpace.stalkMap_germ_apply] at hy
    exact (isUnit_map_iff (PresheafedSpace.stalkMap f.1 _) _).mp hy
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.preimage_basic_open AlgebraicGeometry.LocallyRingedSpace.preimage_basicOpen

-- This actually holds for all ringed spaces with nontrivial stalks.
@[simp]
theorem basicOpen_zero (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) :
    X.toRingedSpace.basicOpen (0 : X.presheaf.obj <| op U) = ⊥ := by
  ext x
  simp only [RingedSpace.basicOpen, Opens.coe_mk, Set.mem_image, Set.mem_setOf_eq, Subtype.exists,
    exists_and_right, exists_eq_right, Opens.coe_bot, Set.mem_empty_iff_false,
    iff_false, not_exists]
  intros hx
  rw [map_zero, isUnit_zero_iff]
  change (0 : X.stalk x) ≠ (1 : X.stalk x)
  exact zero_ne_one
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.basic_open_zero AlgebraicGeometry.LocallyRingedSpace.basicOpen_zero

instance component_nontrivial (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) [hU : Nonempty U] :
    Nontrivial (X.presheaf.obj <| op U) :=
  (X.presheaf.germ hU.some).domain_nontrivial
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.LocallyRingedSpace.component_nontrivial AlgebraicGeometry.LocallyRingedSpace.component_nontrivial

end LocallyRingedSpace

end AlgebraicGeometry
