/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.End
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Category instances for Group, AddGroup, CommGroup, and AddCommGroup.

We introduce the bundled categories:
* `Grp`
* `AddGrp`
* `CommGrp`
* `AddCommGrp`

along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

universe u v

open CategoryTheory

/-- The category of additive groups and group morphisms. -/
structure AddGrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddGroup carrier]

/-- The category of groups and group morphisms. -/
@[to_additive]
structure Grp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : Group carrier]

attribute [instance] AddGrp.str Grp.str
attribute [to_additive existing] Grp.carrier Grp.str

initialize_simps_projections AddGrp (carrier → coe, -str)
initialize_simps_projections Grp (carrier → coe, -str)

namespace Grp

@[to_additive]
instance : CoeSort Grp (Type u) :=
  ⟨Grp.carrier⟩

attribute [coe] AddGrp.carrier Grp.carrier

/-- Construct a bundled `Grp` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddGrp` from the underlying type and typeclass. -/]
abbrev of (M : Type u) [Group M] : Grp := ⟨M⟩

end Grp

/-- The type of morphisms in `AddGrp R`. -/
@[ext]
structure AddGrp.Hom (A B : AddGrp.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →+ B

/-- The type of morphisms in `Grp R`. -/
@[to_additive, ext]
structure Grp.Hom (A B : Grp.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →* B

attribute [to_additive existing AddGrp.Hom.mk] Grp.Hom.mk

namespace Grp

@[to_additive]
instance : Category Grp.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

@[to_additive]
instance : ConcreteCategory Grp (· →* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Grp` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddGrp` back into an `AddMonoidHom`. -/]
abbrev Hom.hom {X Y : Grp.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Grp) f

/-- Typecheck a `MonoidHom` as a morphism in `Grp`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddGrp`. -/]
abbrev ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Grp) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : Grp.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddGrp.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
lemma coe_id {X : Grp} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : Grp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp] lemma forget_map {X Y : Grp} (f : X ⟶ Y) : (forget Grp).map f = (f : X → Y) := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : Grp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (R : Type u) [Group R] : ↑(Grp.of R) = R :=
  rfl

@[to_additive (attr := simp)]
lemma hom_id {X : Grp} : (𝟙 X : X ⟶ X).hom = MonoidHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma id_apply (X : Grp) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
lemma hom_comp {X Y T : Grp} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma comp_apply {X Y T : Grp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
lemma hom_ext {X Y : Grp} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
lemma hom_ofHom {R S : Type u} [Group R] [Group S] (f : R →* S) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_hom {X Y : Grp} (f : X ⟶ Y) :
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
lemma inv_hom_apply {X Y : Grp} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

-- This is essentially an alias for `Iso.inv_hom_id_apply`; consider deprecation?
@[to_additive]
lemma hom_inv_apply {X Y : Grp} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
instance : Inhabited Grp :=
  ⟨Grp.of PUnit⟩

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ Grp MonCat where
  forget₂.obj X := MonCat.of X
  forget₂.map f := MonCat.ofHom f.hom

@[to_additive (attr := simp)] lemma forget₂_map_ofHom {X Y : Type u} [Group X] [Group Y]
    (f : X →* Y) :
    (forget₂ Grp MonCat).map (ofHom f) = MonCat.ofHom f := rfl

@[to_additive]
instance : Coe Grp.{u} MonCat.{u} where coe := (forget₂ Grp MonCat).obj

@[to_additive]
instance (G H : Grp) : One (G ⟶ H) where
  one := ofHom 1

@[to_additive (attr := simp)]
theorem one_apply (G H : Grp) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
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
def fullyFaithfulForget₂ToMonCat : (forget₂ Grp.{u} MonCat).FullyFaithful where
  preimage f := ofHom f.hom

@[to_additive]
instance : (forget₂ Grp.{u} MonCat).Full :=
  fullyFaithfulForget₂ToMonCat.full

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : Grp} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for groups. -/
@[to_additive (attr := simps obj map)
  /-- Universe lift functor for additive groups. -/]
def uliftFunctor : Grp.{v} ⥤ Grp.{max v u} where
  obj X := Grp.of (ULift.{u, v} X)
  map {_ _} f := Grp.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end Grp

/-- The category of additive groups and group morphisms. -/
structure AddCommGrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddCommGroup carrier]

/-- The category of groups and group morphisms. -/
@[to_additive]
structure CommGrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : CommGroup carrier]

attribute [instance] AddCommGrp.str CommGrp.str
attribute [to_additive existing] CommGrp.carrier CommGrp.str

initialize_simps_projections AddCommGrp (carrier → coe, -str)
initialize_simps_projections CommGrp (carrier → coe, -str)

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbrev Ab := AddCommGrp

namespace CommGrp

@[to_additive]
instance : CoeSort CommGrp (Type u) :=
  ⟨CommGrp.carrier⟩

attribute [coe] AddCommGrp.carrier CommGrp.carrier

/-- Construct a bundled `CommGrp` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddCommGrp` from the underlying type and typeclass. -/]
abbrev of (M : Type u) [CommGroup M] : CommGrp := ⟨M⟩

end CommGrp

/-- The type of morphisms in `AddCommGrp R`. -/
@[ext]
structure AddCommGrp.Hom (A B : AddCommGrp.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →+ B

/-- The type of morphisms in `CommGrp R`. -/
@[to_additive, ext]
structure CommGrp.Hom (A B : CommGrp.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →* B

attribute [to_additive existing AddCommGrp.Hom.mk] CommGrp.Hom.mk

namespace CommGrp

@[to_additive]
instance : Category CommGrp.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

@[to_additive]
instance : ConcreteCategory CommGrp (· →* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommGrp` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddCommGrp` back into an `AddMonoidHom`. -/]
abbrev Hom.hom {X Y : CommGrp.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := CommGrp) f

/-- Typecheck a `MonoidHom` as a morphism in `CommGrp`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddCommGrp`. -/]
abbrev ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := CommGrp) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
@[to_additive /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/]
def Hom.Simps.hom (X Y : CommGrp.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddCommGrp.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
lemma coe_id {X : CommGrp} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommGrp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive (attr := simp)]
lemma forget_map {X Y : CommGrp} (f : X ⟶ Y) :
    (forget CommGrp).map f = (f : X → Y) :=
  rfl

@[to_additive (attr := ext)]
lemma ext {X Y : CommGrp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
instance : Inhabited CommGrp :=
  ⟨CommGrp.of PUnit⟩

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (R : Type u) [CommGroup R] : ↑(CommGrp.of R) = R :=
  rfl

@[to_additive (attr := simp)]
lemma hom_id {X : CommGrp} : (𝟙 X : X ⟶ X).hom = MonoidHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma id_apply (X : CommGrp) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
lemma hom_comp {X Y T : CommGrp} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma comp_apply {X Y T : CommGrp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
lemma hom_ext {X Y : CommGrp} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
lemma hom_ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_hom {X Y : CommGrp} (f : X ⟶ Y) :
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
lemma inv_hom_apply {X Y : CommGrp} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

-- This is essentially an alias for `Iso.inv_hom_id_apply`; consider deprecation?
@[to_additive]
lemma hom_inv_apply {X Y : CommGrp} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
instance hasForgetToGroup : HasForget₂ CommGrp Grp where
  forget₂.obj X := Grp.of X
  forget₂.map f := Grp.ofHom f.hom

@[to_additive (attr := simp)] lemma forget₂_grp_map_ofHom {X Y : Type u} [CommGroup X] [CommGroup Y]
    (f : X →* Y) :
    (forget₂ CommGrp Grp).map (ofHom f) = Grp.ofHom f := rfl

@[to_additive]
instance : Coe CommGrp.{u} Grp.{u} where coe := (forget₂ CommGrp Grp).obj

/-- The forgetful functor from commutative groups to groups is fully faithful. -/
@[to_additive fullyFaihtfulForget₂ToAddGrp
/-- The forgetful functor from additive commutative groups to additive groups is fully faithful. -/]
def fullyFaithfulForget₂ToGrp : (forget₂ CommGrp.{u} Grp).FullyFaithful where
  preimage f := ofHom f.hom

@[to_additive]
instance : (forget₂ CommGrp.{u} Grp).Full :=
  fullyFaithfulForget₂ToGrp.full

@[to_additive hasForgetToAddCommMonCat]
instance hasForgetToCommMonCat : HasForget₂ CommGrp CommMonCat where
  forget₂.obj X := CommMonCat.of X
  forget₂.map f := CommMonCat.ofHom f.hom

@[to_additive (attr := simp)] lemma forget₂_commMonCat_map_ofHom {X Y : Type u}
    [CommGroup X] [CommGroup Y] (f : X →* Y) :
    (forget₂ CommGrp CommMonCat).map (ofHom f) = CommMonCat.ofHom f := rfl

@[to_additive]
instance : Coe CommGrp.{u} CommMonCat.{u} where coe := (forget₂ CommGrp CommMonCat).obj

@[to_additive]
instance (G H : CommGrp) : One (G ⟶ H) where
  one := ofHom 1

@[to_additive (attr := simp)]
theorem one_apply (G H : CommGrp) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

@[to_additive]
lemma ofHom_injective {X Y : Type u} [CommGroup X] [CommGroup Y] :
    Function.Injective (fun (f : X →* Y) ↦ ofHom f) := by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : CommGrp} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for commutative groups. -/
@[to_additive (attr := simps obj map)
  /-- Universe lift functor for additive commutative groups. -/]
def uliftFunctor : CommGrp.{v} ⥤ CommGrp.{max v u} where
  obj X := CommGrp.of (ULift.{u, v} X)
  map {_ _} f := CommGrp.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommGrp

namespace AddCommGrp

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ULiftInstances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
@[simps!]
def asHom {G : AddCommGrp.{0}} (g : G) : AddCommGrp.of ℤ ⟶ G :=
  ofHom (zmultiplesHom G g)

theorem asHom_injective {G : AddCommGrp.{0}} : Function.Injective (@asHom G) := fun h k w => by
  simpa using CategoryTheory.congr_fun w 1

@[ext]
theorem int_hom_ext {G : AddCommGrp.{0}} (f g : AddCommGrp.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  hom_ext (AddMonoidHom.ext_int w)

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
theorem injective_of_mono {G H : AddCommGrp.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by cat_disch
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1

end AddCommGrp

/-- Build an isomorphism in the category `Grp` from a `MulEquiv` between `Group`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toGrpIso {X Y : Grp} (e : X ≃* Y) : X ≅ Y where
  hom := Grp.ofHom e.toMonoidHom
  inv := Grp.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddGroup` from an `AddEquiv` between `AddGroup`s. -/
add_decl_doc AddEquiv.toAddGrpIso

/-- Build an isomorphism in the category `CommGrp` from a `MulEquiv`
between `CommGroup`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toCommGrpIso {X Y : CommGrp} (e : X ≃* Y) : X ≅ Y where
  hom := CommGrp.ofHom e.toMonoidHom
  inv := CommGrp.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddCommGrp` from an `AddEquiv`
between `AddCommGroup`s. -/
add_decl_doc AddEquiv.toAddCommGrpIso

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `Grp`. -/
@[to_additive (attr := simp)]
def groupIsoToMulEquiv {X Y : Grp} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build an `addEquiv` from an isomorphism in the category `AddGroup` -/
add_decl_doc addGroupIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive (attr := simps!)]
def commGroupIsoToMulEquiv {X Y : CommGrp} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build an `AddEquiv` from an isomorphism in the category `AddCommGroup`. -/
add_decl_doc addCommGroupIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Group`s are the same as (isomorphic to) isomorphisms
in `Grp` -/
@[to_additive]
def mulEquivIsoGroupIso {X Y : Grp.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toGrpIso
  inv i := i.groupIsoToMulEquiv

/-- Additive equivalences between `AddGroup`s are the same
as (isomorphic to) isomorphisms in `AddGrp`. -/
add_decl_doc addEquivIsoAddGroupIso

/-- Multiplicative equivalences between `CommGroup`s are the same as (isomorphic to) isomorphisms
in `CommGrp`. -/
@[to_additive]
def mulEquivIsoCommGroupIso {X Y : CommGrp.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toCommGrpIso
  inv i := i.commGroupIsoToMulEquiv

/-- Additive equivalences between `AddCommGroup`s are
the same as (isomorphic to) isomorphisms in `AddCommGrp`. -/
add_decl_doc addEquivIsoAddCommGroupIso

namespace CategoryTheory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def isoPerm {α : Type u} : Grp.of (Aut α) ≅ Grp.of (Equiv.Perm α) where
  hom := Grp.ofHom
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv := Grp.ofHom
    { toFun := fun g => g.toIso
      map_one' := by aesop
      map_mul' := by aesop }

/-- The (unbundled) group of automorphisms of a type is `MulEquiv` to the (unbundled) group
of permutations. -/
def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv

end CategoryTheory.Aut

@[to_additive]
instance Grp.forget_reflects_isos : (forget Grp.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget Grp).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := map_mul _ }
    exact e.toGrpIso.isIso_hom

@[to_additive]
instance CommGrp.forget_reflects_isos : (forget CommGrp.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommGrp).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := map_mul _}
    exact e.toCommGrpIso.isIso_hom

-- note: in the following definitions, there is a problem with `@[to_additive]`
-- as the `Category` instance is not found on the additive variant
-- this variant is then renamed with a `Aux` suffix

/-- An alias for `Grp.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) GrpMaxAux
  /-- An alias for `AddGrp.{max u v}`, to deal around unification issues. -/]
abbrev GrpMax.{u1, u2} := Grp.{max u1 u2}
/-- An alias for `AddGrp.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddGrpMax.{u1, u2} := AddGrp.{max u1 u2}

/-- An alias for `CommGrp.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) AddCommGrpMaxAux
  /-- An alias for `AddCommGrp.{max u v}`, to deal around unification issues. -/]
abbrev CommGrpMax.{u1, u2} := CommGrp.{max u1 u2}
/-- An alias for `AddCommGrp.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddCommGrpMax.{u1, u2} := AddCommGrp.{max u1 u2}

/-!
Deprecated lemmas for `MonoidHom.comp` and categorical identities.
-/

@[to_additive (attr := deprecated
  "Proven by `simp only [Grp.hom_id, comp_id]`"
  (since := "2025-01-28"))]
theorem MonoidHom.comp_id_grp {G : Grp.{u}} {H : Type u} [Monoid H] (f : G →* H) :
    f.comp (Grp.Hom.hom (𝟙 G)) = f := by simp
@[to_additive (attr := deprecated
  "Proven by `simp only [Grp.hom_id, id_comp]`"
  (since := "2025-01-28"))]
theorem MonoidHom.id_grp_comp {G : Type u} [Monoid G] {H : Grp.{u}} (f : G →* H) :
    MonoidHom.comp (Grp.Hom.hom (𝟙 H)) f = f := by simp

@[to_additive (attr := deprecated
  "Proven by `simp only [CommGrp.hom_id, comp_id]`"
  (since := "2025-01-28"))]
theorem MonoidHom.comp_id_commGrp {G : CommGrp.{u}} {H : Type u} [Monoid H] (f : G →* H) :
    f.comp (CommGrp.Hom.hom (𝟙 G)) = f := by
  simp
@[to_additive (attr := deprecated
  "Proven by `simp only [CommGrp.hom_id, id_comp]`"
  (since := "2025-01-28"))]
theorem MonoidHom.id_commGrp_comp {G : Type u} [Monoid G] {H : CommGrp.{u}} (f : G →* H) :
    MonoidHom.comp (CommGrp.Hom.hom (𝟙 H)) f = f := by
  simp
