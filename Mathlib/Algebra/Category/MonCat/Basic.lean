/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.PUnitInstances.Algebra
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.Algebra.Ring.Action.Group

/-!
# Category instances for `Monoid`, `AddMonoid`, `CommMonoid`, and `AddCommMmonoid`.

We introduce the bundled categories:
* `MonCat`
* `AddMonCat`
* `CommMonCat`
* `AddCommMonCat`
along with the relevant forgetful functors between them.
-/

universe u v

open CategoryTheory

/-- The category of monoids and monoid morphisms. -/
@[to_additive AddMonCat]
def MonCat : Type (u + 1) :=
  Bundled Monoid

/-- The category of additive monoids and monoid morphisms. -/
add_decl_doc AddMonCat

namespace MonCat

@[to_additive]
instance : CoeSort MonCat Type* where
  coe X := X.α

@[to_additive]
instance (X : MonCat) : Monoid X := X.str

/-- Construct a bundled `MonCat` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Monoid M] : MonCat :=
  Bundled.of M

/-- Construct a bundled `AddMonCat` from the underlying type and typeclass. -/
add_decl_doc AddMonCat.of

end MonCat

/-- The type of morphisms in `AddMonCat R`. -/
@[ext]
structure AddMonCat.Hom (A B : AddMonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →+ B

/-- The type of morphisms in `MonCat R`. -/
@[to_additive, ext]
structure MonCat.Hom (A B : MonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →* B

attribute [to_additive existing AddMonCat.Hom.mk] MonCat.Hom.mk

namespace MonCat

@[to_additive]
instance : Category MonCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

@[to_additive]
instance : ConcreteCategory MonCat (· →* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `MonCat` back into a `MonoidHom`. -/
@[to_additive]
abbrev Hom.hom {X Y : MonCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := MonCat) f

/-- Turn a morphism in `AddMonCat` back into an `AddMonoidHom`. -/
add_decl_doc AddMonCat.Hom.hom

/-- Typecheck a `MonoidHom` as a morphism in `MonCat`. -/
@[to_additive]
abbrev ofHom {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := MonCat) f

/-- Typecheck an `AddMonoidHom` as a morphism in `AddMonCat`. -/
add_decl_doc AddMonCat.ofHom

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : MonCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
lemma coe_id {X : MonCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : MonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive (attr := simp)]
lemma forget_map {X Y : MonCat} (f : X ⟶ Y) :
    (forget MonCat).map f = f := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : MonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
theorem coe_of (M : Type u) [Monoid M] : (MonCat.of M : Type u) = M := rfl

@[to_additive (attr := simp)]
lemma hom_id {M : MonCat} : (𝟙 M : M ⟶ M).hom = MonoidHom.id M := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma id_apply (M : MonCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[to_additive (attr := simp)]
lemma hom_comp {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma comp_apply {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
lemma hom_ext {M N : MonCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
lemma hom_ofHom {M N : Type u} [Monoid M] [Monoid N] (f : M →* N) :
  (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_hom {M N : MonCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_id {M : Type u} [Monoid M] : ofHom (MonoidHom.id M) = 𝟙 (of M) := rfl

@[to_additive (attr := simp)]
lemma ofHom_comp {M N P : Type u} [Monoid M] [Monoid N] [Monoid P]
    (f : M →* N) (g : N →* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
lemma ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive (attr := simp)]
lemma inv_hom_apply {M N : MonCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  rw [← comp_apply]
  simp

@[to_additive (attr := simp)]
lemma hom_inv_apply {M N : MonCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  rw [← comp_apply]
  simp

@[to_additive]
instance : Inhabited MonCat :=
  -- The default instance for `Monoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _
    (@CommGroup.toGroup _ PUnit.commGroup)))⟩

@[to_additive]
instance (X Y : MonCat.{u}) : One (X ⟶ Y) := ⟨ofHom 1⟩

@[to_additive (attr := simp)]
lemma oneHom_apply (X Y : MonCat.{u}) (x : X) : (1 : X ⟶ Y) x = 1 := rfl

@[to_additive (attr := simp)]
lemma one_of {A : Type*} [Monoid A] : (1 : MonCat.of A) = (1 : A) := rfl

@[to_additive (attr := simp)]
lemma mul_of {A : Type*} [Monoid A] (a b : A) :
    @HMul.hMul (MonCat.of A) (MonCat.of A) (MonCat.of A) _ a b = a * b := rfl

@[to_additive]
instance {G : Type*} [Group G] : Group (MonCat.of G) := by assumption

/-- Universe lift functor for monoids. -/
@[to_additive (attr := simps)
  "Universe lift functor for additive monoids."]
def uliftFunctor : MonCat.{v} ⥤ MonCat.{max v u} where
  obj X := MonCat.of (ULift.{u, v} X)
  map {_ _} f := MonCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end MonCat

/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMonCat]
def CommMonCat : Type (u + 1) :=
  Bundled CommMonoid

/-- The category of additive commutative monoids and monoid morphisms. -/
add_decl_doc AddCommMonCat

namespace CommMonCat

@[to_additive]
instance : CoeSort CommMonCat Type* where
  coe X := X.α

@[to_additive]
instance (X : CommMonCat) : CommMonoid X := X.str

/-- Construct a bundled `CommMonCat` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [CommMonoid M] : CommMonCat :=
  Bundled.of M

/-- Construct a bundled `AddCommMonCat` from the underlying type and typeclass. -/
add_decl_doc AddCommMonCat.of

end CommMonCat

/-- The type of morphisms in `AddCommMonCat R`. -/
@[ext]
structure AddCommMonCat.Hom (A B : AddCommMonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →+ B

/-- The type of morphisms in `CommMonCat R`. -/
@[to_additive, ext]
structure CommMonCat.Hom (A B : CommMonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →* B

attribute [to_additive existing AddCommMonCat.Hom.mk] CommMonCat.Hom.mk

namespace CommMonCat

@[to_additive]
instance : Category CommMonCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

@[to_additive]
instance : ConcreteCategory CommMonCat (· →* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommMonCat` back into a `MonoidHom`. -/
@[to_additive]
abbrev Hom.hom {X Y : CommMonCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := CommMonCat) f

/-- Turn a morphism in `AddCommMonCat` back into an `AddMonoidHom`. -/
add_decl_doc AddMonCat.Hom.hom

/-- Typecheck a `MonoidHom` as a morphism in `CommMonCat`. -/
@[to_additive]
abbrev ofHom {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := CommMonCat) f

/-- Typecheck an `AddMonoidHom` as a morphism in `AddMonCat`. -/
add_decl_doc AddMonCat.ofHom

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : CommMonCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
lemma coe_id {X : CommMonCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommMonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive (attr := simp)]
lemma forget_map {X Y : CommMonCat} (f : X ⟶ Y) :
    (forget CommMonCat).map f = (f : X → Y) :=
  rfl

@[to_additive (attr := ext)]
lemma ext {X Y : CommMonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive (attr := simp)]
lemma hom_id {M : CommMonCat} : (𝟙 M : M ⟶ M).hom = MonoidHom.id M := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma id_apply (M : CommMonCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[to_additive (attr := simp)]
lemma hom_comp {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma comp_apply {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
lemma hom_ext {M N : CommMonCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
lemma hom_ofHom {M N : Type u} [CommMonoid M] [CommMonoid N] (f : M →* N) :
  (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_hom {M N : CommMonCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_id {M : Type u} [CommMonoid M] : ofHom (MonoidHom.id M) = 𝟙 (of M) := rfl

@[to_additive (attr := simp)]
lemma ofHom_comp {M N P : Type u} [CommMonoid M] [CommMonoid N] [CommMonoid P]
    (f : M →* N) (g : N →* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
lemma ofHom_apply {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive (attr := simp)]
lemma inv_hom_apply {M N : CommMonCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  rw [← comp_apply]
  simp

@[to_additive (attr := simp)]
lemma hom_inv_apply {M N : CommMonCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  rw [← comp_apply]
  simp

@[to_additive]
instance : Inhabited CommMonCat :=
  -- The default instance for `CommMonoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@CommGroup.toCommMonoid _ PUnit.commGroup)⟩

@[to_additive]
theorem coe_of (R : Type u) [CommMonoid R] : (CommMonCat.of R : Type u) = R :=
  rfl

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ CommMonCat MonCat where
  forget₂ :=
    { obj := fun R ↦ MonCat.of R
      map := fun f ↦ MonCat.ofHom f.hom }

@[to_additive]
instance : Coe CommMonCat.{u} MonCat.{u} where coe := (forget₂ CommMonCat MonCat).obj

/-- Universe lift functor for commutative monoids. -/
@[to_additive (attr := simps)
  "Universe lift functor for additive commutative monoids."]
def uliftFunctor : CommMonCat.{v} ⥤ CommMonCat.{max v u} where
  obj X := CommMonCat.of (ULift.{u, v} X)
  map {_ _} f := CommMonCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommMonCat

variable {X Y : Type u}

section

variable [Monoid X] [Monoid Y]

/-- Build an isomorphism in the category `MonCat` from a `MulEquiv` between `Monoid`s. -/
@[to_additive (attr := simps) AddEquiv.toAddMonCatIso
      "Build an isomorphism in the category `AddMonCat` from\nan `AddEquiv` between `AddMonoid`s."]
def MulEquiv.toMonCatIso (e : X ≃* Y) : MonCat.of X ≅ MonCat.of Y where
  hom := MonCat.ofHom e.toMonoidHom
  inv := MonCat.ofHom e.symm.toMonoidHom

end

section

variable [CommMonoid X] [CommMonoid Y]

/-- Build an isomorphism in the category `CommMonCat` from a `MulEquiv` between `CommMonoid`s. -/
@[to_additive (attr := simps) AddEquiv.toAddCommMonCatIso]
def MulEquiv.toCommMonCatIso (e : X ≃* Y) : CommMonCat.of X ≅ CommMonCat.of Y where
  hom := CommMonCat.ofHom e.toMonoidHom
  inv := CommMonCat.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddCommMonCat`
from an `AddEquiv` between `AddCommMonoid`s. -/
add_decl_doc AddEquiv.toAddCommMonCatIso

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `MonCat`. -/
@[to_additive addMonCatIsoToAddEquiv
      "Build an `AddEquiv` from an isomorphism in the category\n`AddMonCat`."]
def monCatIsoToMulEquiv {X Y : MonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `MulEquiv` from an isomorphism in the category `CommMonCat`. -/
@[to_additive "Build an `AddEquiv` from an isomorphism in the category\n`AddCommMonCat`."]
def commMonCatIsoToMulEquiv {X Y : CommMonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

end CategoryTheory.Iso

/-- multiplicative equivalences between `Monoid`s are the same as (isomorphic to) isomorphisms
in `MonCat` -/
@[to_additive addEquivIsoAddMonCatIso]
def mulEquivIsoMonCatIso {X Y : Type u} [Monoid X] [Monoid Y] :
    X ≃* Y ≅ MonCat.of X ≅ MonCat.of Y where
  hom e := e.toMonCatIso
  inv i := i.monCatIsoToMulEquiv

/-- additive equivalences between `AddMonoid`s are the same
as (isomorphic to) isomorphisms in `AddMonCat` -/
add_decl_doc addEquivIsoAddMonCatIso

/-- multiplicative equivalences between `CommMonoid`s are the same as (isomorphic to) isomorphisms
in `CommMonCat` -/
@[to_additive addEquivIsoAddCommMonCatIso]
def mulEquivIsoCommMonCatIso {X Y : Type u} [CommMonoid X] [CommMonoid Y] :
    X ≃* Y ≅ CommMonCat.of X ≅ CommMonCat.of Y where
  hom e := e.toCommMonCatIso
  inv i := i.commMonCatIsoToMulEquiv

/-- additive equivalences between `AddCommMonoid`s are
the same as (isomorphic to) isomorphisms in `AddCommMonCat` -/
add_decl_doc addEquivIsoAddCommMonCatIso

@[to_additive]
instance MonCat.forget_reflects_isos : (forget MonCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget MonCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMonCatIso.isIso_hom

@[to_additive]
instance CommMonCat.forget_reflects_isos : (forget CommMonCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommMonCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toCommMonCatIso.isIso_hom

-- Porting note: this was added in order to ensure that `forget₂ CommMonCat MonCat`
-- automatically reflects isomorphisms
-- we could have used `CategoryTheory.HasForget.ReflectsIso` alternatively
@[to_additive]
instance CommMonCat.forget₂_full : (forget₂ CommMonCat MonCat).Full where
  map_surjective f := ⟨ofHom f.hom, rfl⟩

example : (forget₂ CommMonCat MonCat).ReflectsIsomorphisms := inferInstance

/-!
`@[simp]` lemmas for `MonoidHom.comp` and categorical identities.
-/

@[to_additive (attr := deprecated
  "Proven by `simp only [MonCat.hom_id, comp_id]`"
  (since := "2025-01-28"))]
theorem MonoidHom.comp_id_monCat {G : MonCat.{u}} {H : Type u} [Monoid H] (f : G →* H) :
    f.comp (MonCat.Hom.hom (𝟙 G)) = f := by simp
@[to_additive (attr := deprecated
  "Proven by `simp only [MonCat.hom_id, id_comp]`"
  (since := "2025-01-28"))]
theorem MonoidHom.id_monCat_comp {G : Type u} [Monoid G] {H : MonCat.{u}} (f : G →* H) :
    MonoidHom.comp (MonCat.Hom.hom (𝟙 H)) f = f := by simp

@[to_additive (attr := deprecated
  "Proven by `simp only [CommMonCat.hom_id, comp_id]`"
  (since := "2025-01-28"))]
theorem MonoidHom.comp_id_commMonCat {G : CommMonCat.{u}} {H : Type u} [CommMonoid H] (f : G →* H) :
    f.comp (CommMonCat.Hom.hom (𝟙 G)) = f := by
  simp
@[to_additive (attr := deprecated
  "Proven by `simp only [CommMonCat.hom_id, id_comp]`"
  (since := "2025-01-28"))]
theorem MonoidHom.id_commMonCat_comp {G : Type u} [CommMonoid G] {H : CommMonCat.{u}} (f : G →* H) :
    MonoidHom.comp (CommMonCat.Hom.hom (𝟙 H)) f = f := by
  simp
