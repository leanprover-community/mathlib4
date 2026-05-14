/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Category instances for Group, AddGroup, CommGroup, and AddCommGroup.

We introduce the bundled categories:
* `GrpCat`
* `AddGrpCat`
* `CommGrpCat`
* `AddCommGrpCat`

along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

@[expose] public section

universe u v

open CategoryTheory

/-- The category of additive groups and group morphisms. -/
structure AddGrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddGroup carrier]

/-- The category of groups and group morphisms. -/
@[to_additive]
structure GrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : Group carrier]

attribute [instance] AddGrpCat.str GrpCat.str

initialize_simps_projections AddGrpCat (carrier → coe, -str)
initialize_simps_projections GrpCat (carrier → coe, -str)

namespace GrpCat

@[to_additive]
instance : CoeSort GrpCat (Type u) :=
  ⟨GrpCat.carrier⟩

attribute [coe] AddGrpCat.carrier GrpCat.carrier

/-- Construct a bundled `GrpCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddGrpCat` from the underlying type and typeclass. -/]
abbrev of (M : Type u) [Group M] : GrpCat := ⟨M⟩

end GrpCat

/-- The type of morphisms in `AddGrpCat R`. -/
@[ext]
structure AddGrpCat.Hom (A B : AddGrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →+ B

set_option backward.privateInPublic true in
/-- The type of morphisms in `GrpCat R`. -/
@[to_additive, ext]
structure GrpCat.Hom (A B : GrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →* B

namespace GrpCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
instance : Category GrpCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
instance : ConcreteCategory GrpCat (· →* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `GrpCat` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddGrpCat` back into an `AddMonoidHom`. -/]
abbrev Hom.hom {X Y : GrpCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := GrpCat) f

/-- Typecheck a `MonoidHom` as a morphism in `GrpCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddGrpCat`. -/]
abbrev ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := GrpCat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : GrpCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddGrpCat.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
lemma coe_id {X : GrpCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : GrpCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
lemma ext {X Y : GrpCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (R : Type u) [Group R] : ↑(GrpCat.of R) = R :=
  rfl

@[to_additive (attr := simp)]
lemma hom_id {X : GrpCat} : (𝟙 X : X ⟶ X).hom = MonoidHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma id_apply (X : GrpCat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
lemma hom_comp {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma comp_apply {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
lemma hom_ext {X Y : GrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
lemma hom_ofHom {R S : Type u} [Group R] [Group S] (f : R →* S) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_hom {X Y : GrpCat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_id {X : Type u} [Group X] : ofHom (MonoidHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
lemma ofHom_comp {X Y Z : Type u} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Y →* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
lemma ofHom_apply {X Y : Type u} [Group X] [Group Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

-- This is essentially an alias for `Iso.hom_inv_id_apply`; consider deprecation?
@[to_additive]
lemma inv_hom_apply {X Y : GrpCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

-- This is essentially an alias for `Iso.inv_hom_id_apply`; consider deprecation?
@[to_additive]
lemma hom_inv_apply {X Y : GrpCat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
instance : Inhabited GrpCat :=
  ⟨GrpCat.of PUnit⟩

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ GrpCat MonCat where
  forget₂.obj X := MonCat.of X
  forget₂.map f := MonCat.ofHom f.hom

@[to_additive (attr := simp)] lemma forget₂_map_ofHom {X Y : Type u} [Group X] [Group Y]
    (f : X →* Y) :
    (forget₂ GrpCat MonCat).map (ofHom f) = MonCat.ofHom f := rfl

@[to_additive (attr := simp)] lemma forget₂_map {R S : GrpCat} (f : R ⟶ S) (x) :
    (forget₂ GrpCat MonCat).map f x = f x := rfl

@[to_additive]
instance : Coe GrpCat.{u} MonCat.{u} where coe := (forget₂ GrpCat MonCat).obj

@[to_additive]
instance (G H : GrpCat) : One (G ⟶ H) where
  one := ofHom 1

@[to_additive (attr := simp)]
theorem one_apply (G H : GrpCat) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

@[to_additive]
lemma ofHom_injective {X Y : Type u} [Group X] [Group Y] :
    Function.Injective (fun (f : X →* Y) ↦ ofHom f) := by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

/-- The forgetful functor from groups to monoids is fully faithful. -/
@[to_additive fullyFaihtfulForget₂ToAddMonCat
  /-- The forgetful functor from additive groups to additive monoids is fully faithful. -/]
def fullyFaithfulForget₂ToMonCat : (forget₂ GrpCat.{u} MonCat).FullyFaithful where
  preimage f := ofHom f.hom

@[to_additive]
instance : (forget₂ GrpCat.{u} MonCat).Full :=
  fullyFaithfulForget₂ToMonCat.full

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : GrpCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for groups. -/
@[to_additive (attr := simps obj map)
  /-- Universe lift functor for additive groups. -/]
def uliftFunctor : GrpCat.{v} ⥤ GrpCat.{max v u} where
  obj X := GrpCat.of (ULift.{u, v} X)
  map {_ _} f := GrpCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end GrpCat

/-- The category of additive groups and group morphisms. -/
structure AddCommGrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddCommGroup carrier]

/-- The category of groups and group morphisms. -/
@[to_additive]
structure CommGrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : CommGroup carrier]

attribute [instance] AddCommGrpCat.str CommGrpCat.str

initialize_simps_projections AddCommGrpCat (carrier → coe, -str)
initialize_simps_projections CommGrpCat (carrier → coe, -str)

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbrev Ab := AddCommGrpCat

namespace CommGrpCat

@[to_additive]
instance : CoeSort CommGrpCat (Type u) :=
  ⟨CommGrpCat.carrier⟩

attribute [coe] AddCommGrpCat.carrier CommGrpCat.carrier

/-- Construct a bundled `CommGrpCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddCommGrpCat` from the underlying type and typeclass. -/]
abbrev of (M : Type u) [CommGroup M] : CommGrpCat := ⟨M⟩

end CommGrpCat

/-- The type of morphisms in `AddCommGrpCat R`. -/
@[ext]
structure AddCommGrpCat.Hom (A B : AddCommGrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →+ B

set_option backward.privateInPublic true in
/-- The type of morphisms in `CommGrpCat R`. -/
@[to_additive, ext]
structure CommGrpCat.Hom (A B : CommGrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →* B

namespace CommGrpCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
instance : Category CommGrpCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
instance : ConcreteCategory CommGrpCat (· →* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommGrpCat` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddCommGrpCat` back into an `AddMonoidHom`. -/]
abbrev Hom.hom {X Y : CommGrpCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := CommGrpCat) f

/-- Typecheck a `MonoidHom` as a morphism in `CommGrpCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddCommGrpCat`. -/]
abbrev ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := CommGrpCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
@[to_additive /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/]
def Hom.Simps.hom (X Y : CommGrpCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddCommGrpCat.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
lemma coe_id {X : CommGrpCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommGrpCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
lemma ext {X Y : CommGrpCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
instance : Inhabited CommGrpCat :=
  ⟨CommGrpCat.of PUnit⟩

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (R : Type u) [CommGroup R] : ↑(CommGrpCat.of R) = R :=
  rfl

@[to_additive (attr := simp)]
lemma hom_id {X : CommGrpCat} : (𝟙 X : X ⟶ X).hom = MonoidHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma id_apply (X : CommGrpCat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
lemma hom_comp {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma comp_apply {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
lemma hom_ext {X Y : CommGrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
lemma hom_ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_hom {X Y : CommGrpCat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_id {X : Type u} [CommGroup X] : ofHom (MonoidHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
lemma ofHom_comp {X Y Z : Type u} [CommGroup X] [CommGroup Y] [CommGroup Z]
    (f : X →* Y) (g : Y →* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
lemma ofHom_apply {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

-- This is essentially an alias for `Iso.hom_inv_id_apply`; consider deprecation?
@[to_additive]
lemma inv_hom_apply {X Y : CommGrpCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

-- This is essentially an alias for `Iso.inv_hom_id_apply`; consider deprecation?
@[to_additive]
lemma hom_inv_apply {X Y : CommGrpCat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
instance hasForgetToGroup : HasForget₂ CommGrpCat GrpCat where
  forget₂.obj X := GrpCat.of X
  forget₂.map f := GrpCat.ofHom f.hom

@[to_additive (attr := simp)] lemma forget₂_grp_map_ofHom {X Y : Type u} [CommGroup X] [CommGroup Y]
    (f : X →* Y) :
    (forget₂ CommGrpCat GrpCat).map (ofHom f) = GrpCat.ofHom f := rfl

@[to_additive (attr := simp)] lemma forget₂_map {R S : CommGrpCat} (f : R ⟶ S) (x) :
    (forget₂ CommGrpCat GrpCat).map f x = f x := rfl

@[to_additive]
instance : Coe CommGrpCat.{u} GrpCat.{u} where coe := (forget₂ CommGrpCat GrpCat).obj

/-- The forgetful functor from commutative groups to groups is fully faithful. -/
@[to_additive fullyFaihtfulForget₂ToAddGrp
/-- The forgetful functor from additive commutative groups to additive groups is fully faithful. -/]
def fullyFaithfulForget₂ToGrp : (forget₂ CommGrpCat.{u} GrpCat).FullyFaithful where
  preimage f := ofHom f.hom

@[to_additive]
instance : (forget₂ CommGrpCat.{u} GrpCat).Full :=
  fullyFaithfulForget₂ToGrp.full

@[to_additive hasForgetToAddCommMonCat]
instance hasForgetToCommMonCat : HasForget₂ CommGrpCat CommMonCat where
  forget₂.obj X := CommMonCat.of X
  forget₂.map f := CommMonCat.ofHom f.hom

@[to_additive (attr := simp)] lemma forget₂_commMonCat_map_ofHom {X Y : Type u}
    [CommGroup X] [CommGroup Y] (f : X →* Y) :
    (forget₂ CommGrpCat CommMonCat).map (ofHom f) = CommMonCat.ofHom f := rfl

@[to_additive]
instance : Coe CommGrpCat.{u} CommMonCat.{u} where coe := (forget₂ CommGrpCat CommMonCat).obj

@[to_additive]
instance (G H : CommGrpCat) : One (G ⟶ H) where
  one := ofHom 1

@[to_additive (attr := simp)]
theorem one_apply (G H : CommGrpCat) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

@[to_additive]
lemma ofHom_injective {X Y : Type u} [CommGroup X] [CommGroup Y] :
    Function.Injective (fun (f : X →* Y) ↦ ofHom f) := by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : CommGrpCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for commutative groups. -/
@[to_additive (attr := simps obj map)
  /-- Universe lift functor for additive commutative groups. -/]
def uliftFunctor : CommGrpCat.{v} ⥤ CommGrpCat.{max v u} where
  obj X := CommGrpCat.of (ULift.{u, v} X)
  map {_ _} f := CommGrpCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommGrpCat

namespace AddCommGrpCat

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ULiftInstances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
@[simps!]
def asHom {G : AddCommGrpCat.{0}} (g : G) : AddCommGrpCat.of ℤ ⟶ G :=
  ofHom (zmultiplesHom G g)

theorem asHom_injective {G : AddCommGrpCat.{0}} : Function.Injective (@asHom G) := fun h k w => by
  simpa using CategoryTheory.congr_fun w 1

@[ext]
theorem int_hom_ext {G : AddCommGrpCat.{0}} (f g : AddCommGrpCat.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  hom_ext (AddMonoidHom.ext_int w)

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
theorem injective_of_mono {G H : AddCommGrpCat.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by cat_disch
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1

end AddCommGrpCat

/-- Build an isomorphism in the category `GrpCat` from a `MulEquiv` between `Group`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toGrpIso {X Y : GrpCat} (e : X ≃* Y) : X ≅ Y where
  hom := GrpCat.ofHom e.toMonoidHom
  inv := GrpCat.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddGroup` from an `AddEquiv` between `AddGroup`s. -/
add_decl_doc AddEquiv.toAddGrpIso

/-- Build an isomorphism in the category `CommGrpCat` from a `MulEquiv`
between `CommGroup`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toCommGrpIso {X Y : CommGrpCat} (e : X ≃* Y) : X ≅ Y where
  hom := CommGrpCat.ofHom e.toMonoidHom
  inv := CommGrpCat.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddCommGrpCat` from an `AddEquiv`
between `AddCommGroup`s. -/
add_decl_doc AddEquiv.toAddCommGrpIso

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `GrpCat`. -/
@[to_additive (attr := simp)]
def groupIsoToMulEquiv {X Y : GrpCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build an `addEquiv` from an isomorphism in the category `AddGroup` -/
add_decl_doc addGroupIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive (attr := simps!)]
def commGroupIsoToMulEquiv {X Y : CommGrpCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build an `AddEquiv` from an isomorphism in the category `AddCommGroup`. -/
add_decl_doc addCommGroupIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Group`s are the same as (isomorphic to) isomorphisms
in `GrpCat` -/
@[to_additive]
def mulEquivIsoGroupIso {X Y : GrpCat.{u}} : (X ≃* Y) ≅ (X ≅ Y) where
  hom := ↾fun e ↦ e.toGrpIso
  inv := ↾fun i ↦ i.groupIsoToMulEquiv

/-- Additive equivalences between `AddGroup`s are the same
as (isomorphic to) isomorphisms in `AddGrpCat`. -/
add_decl_doc addEquivIsoAddGroupIso

/-- Multiplicative equivalences between `CommGroup`s are the same as (isomorphic to) isomorphisms
in `CommGrpCat`. -/
@[to_additive]
def mulEquivIsoCommGroupIso {X Y : CommGrpCat.{u}} : (X ≃* Y) ≅ (X ≅ Y) where
  hom := ↾fun e ↦ e.toCommGrpIso
  inv := ↾fun i ↦ i.commGroupIsoToMulEquiv

/-- Additive equivalences between `AddCommGroup`s are
the same as (isomorphic to) isomorphisms in `AddCommGrpCat`. -/
add_decl_doc addEquivIsoAddCommGroupIso

namespace CategoryTheory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def isoPerm {α : Type u} : GrpCat.of (Aut α) ≅ GrpCat.of (Equiv.Perm α) where
  hom := GrpCat.ofHom
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv := GrpCat.ofHom
    { toFun := fun g => g.toIso
      map_one' := by aesop
      map_mul' := by aesop }

/-- The (unbundled) group of automorphisms of a type is `MulEquiv` to the (unbundled) group
of permutations. -/
def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv

end CategoryTheory.Aut

@[to_additive]
instance GrpCat.forget_reflects_isos : (forget GrpCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget GrpCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by simp [Iso.toEquiv, i] }
    exact e.toGrpIso.isIso_hom

@[to_additive]
instance CommGrpCat.forget_reflects_isos : (forget CommGrpCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommGrpCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by simp [Iso.toEquiv, i] }
    exact e.toCommGrpIso.isIso_hom

-- note: in the following definitions, there is a problem with `@[to_additive]`
-- as the `Category` instance is not found on the additive variant
-- this variant is then renamed with an `Aux` suffix

/-- An alias for `GrpCat.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) GrpMaxAux
  /-- An alias for `AddGrpCat.{max u v}`, to deal around unification issues. -/]
abbrev GrpMax.{u1, u2} := GrpCat.{max u1 u2}
/-- An alias for `AddGrpCat.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddGrpMax.{u1, u2} := AddGrpCat.{max u1 u2}

/-- An alias for `CommGrpCat.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) AddCommGrpMaxAux
  /-- An alias for `AddCommGrpCat.{max u v}`, to deal around unification issues. -/]
abbrev CommGrpMax.{u1, u2} := CommGrpCat.{max u1 u2}
/-- An alias for `AddCommGrpCat.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddCommGrpMax.{u1, u2} := AddCommGrpCat.{max u1 u2}
