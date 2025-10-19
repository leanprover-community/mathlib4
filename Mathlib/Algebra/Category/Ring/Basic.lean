/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.PUnit
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso

/-!
# Category instances for `Semiring`, `Ring`, `CommSemiring`, and `CommRing`.

We introduce the bundled categories:
* `SemiRingCat`
* `RingCat`
* `CommSemiRingCat`
* `CommRingCat`

along with the relevant forgetful functors between them.
-/

universe u v

open CategoryTheory

/-- The category of semirings. -/
structure SemiRingCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type u
  [semiring : Semiring carrier]

attribute [instance] SemiRingCat.semiring

initialize_simps_projections SemiRingCat (-semiring)

namespace SemiRingCat

instance : CoeSort (SemiRingCat) (Type u) :=
  ⟨SemiRingCat.carrier⟩

attribute [coe] SemiRingCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `SemiRingCat`. -/
abbrev of (R : Type u) [Semiring R] : SemiRingCat :=
  ⟨R⟩

lemma coe_of (R : Type u) [Semiring R] : (of R : Type u) = R :=
  rfl

lemma of_carrier (R : SemiRingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `SemiRingCat`. -/
@[ext]
structure Hom (R S : SemiRingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R →+* S

instance : Category SemiRingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} SemiRingCat (fun R S => R →+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `SemiRingCat` back into a `RingHom`. -/
abbrev Hom.hom {R S : SemiRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := SemiRingCat) f

/-- Typecheck a `RingHom` as a morphism in `SemiRingCat`. -/
abbrev ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := SemiRingCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (R S : SemiRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {R : SemiRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/
lemma id_apply (R : SemiRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
lemma hom_comp {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : SemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {R S : SemiRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {R : Type u} [Semiring R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
lemma ofHom_comp {R S T : Type u} [Semiring R] [Semiring S] [Semiring T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl

lemma inv_hom_apply {R S : SemiRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp

lemma hom_inv_apply {R S : SemiRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp

instance : Inhabited SemiRingCat :=
  ⟨of PUnit⟩

set_option linter.style.commandStart false in -- TODO fix linter/pretty-printing!
/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`. -/
unif_hint forget_obj_eq_coe (R R' : SemiRingCat) where
  R ≟ R' ⊢
  (forget SemiRingCat).obj R ≟ SemiRingCat.carrier R'

lemma forget_obj {R : SemiRingCat} : (forget SemiRingCat).obj R = R := rfl

lemma forget_map {R S : SemiRingCat} (f : R ⟶ S) :
    (forget SemiRingCat).map f = f :=
  rfl

instance {R : SemiRingCat} : Semiring ((forget SemiRingCat).obj R) :=
  (inferInstance : Semiring R.carrier)

instance hasForgetToMonCat : HasForget₂ SemiRingCat MonCat where
  forget₂ :=
    { obj := fun R ↦ MonCat.of R
      map := fun f ↦ MonCat.ofHom f.hom.toMonoidHom }

instance hasForgetToAddCommMonCat : HasForget₂ SemiRingCat AddCommMonCat where
  forget₂ :=
    { obj := fun R ↦ AddCommMonCat.of R
      map := fun f ↦ AddCommMonCat.ofHom f.hom.toAddMonoidHom }

/-- Ring equivalences are isomorphisms in category of semirings -/
@[simps]
def _root_.RingEquiv.toSemiRingCatIso {R S : Type u} [Semiring R] [Semiring S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm

instance forgetReflectIsos : (forget SemiRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget SemiRingCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toSemiRingCatIso.isIso_hom

end SemiRingCat

/-- The category of rings. -/
structure RingCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type u
  [ring : Ring carrier]

attribute [instance] RingCat.ring

initialize_simps_projections RingCat (-ring)

namespace RingCat

instance : CoeSort (RingCat) (Type u) :=
  ⟨RingCat.carrier⟩

attribute [coe] RingCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `RingCat`. -/
abbrev of (R : Type u) [Ring R] : RingCat :=
  ⟨R⟩

lemma coe_of (R : Type u) [Ring R] : (of R : Type u) = R :=
  rfl

lemma of_carrier (R : RingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `RingCat`. -/
@[ext]
structure Hom (R S : RingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R →+* S

instance : Category RingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} RingCat (fun R S => R →+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `RingCat` back into a `RingHom`. -/
abbrev Hom.hom {R S : RingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := RingCat) f

/-- Typecheck a `RingHom` as a morphism in `RingCat`. -/
abbrev ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := RingCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (R S : RingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {R : RingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/
lemma id_apply (R : RingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
lemma hom_comp {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : RingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {R S : RingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {R : Type u} [Ring R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
lemma ofHom_comp {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl

lemma inv_hom_apply {R S : RingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp

lemma hom_inv_apply {R S : RingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp

instance : Inhabited RingCat :=
  ⟨of PUnit⟩

set_option linter.style.commandStart false in -- TODO investigate and fix!
/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying
`PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective`.
-/
unif_hint forget_obj_eq_coe (R R' : RingCat) where
  R ≟ R' ⊢
  (forget RingCat).obj R ≟ RingCat.carrier R'

lemma forget_obj {R : RingCat} : (forget RingCat).obj R = R := rfl

lemma forget_map {R S : RingCat} (f : R ⟶ S) :
    (forget RingCat).map f = f :=
  rfl

instance {R : RingCat} : Ring ((forget RingCat).obj R) :=
  (inferInstance : Ring R.carrier)

instance hasForgetToSemiRingCat : HasForget₂ RingCat SemiRingCat where
  forget₂ :=
    { obj := fun R ↦ SemiRingCat.of R
      map := fun f ↦ SemiRingCat.ofHom f.hom }

/-- The forgetful functor from `RingCat` to `SemiRingCat` is fully faithful. -/
def fullyFaithfulForget₂ToSemiRingCat :
    (forget₂ RingCat SemiRingCat).FullyFaithful where
  preimage f := ofHom f.hom

instance : (forget₂ RingCat SemiRingCat).Full :=
  fullyFaithfulForget₂ToSemiRingCat.full

instance hasForgetToAddCommGrp : HasForget₂ RingCat AddCommGrpCat where
  forget₂ :=
    { obj := fun R ↦ AddCommGrpCat.of R
      map := fun f ↦ AddCommGrpCat.ofHom f.hom.toAddMonoidHom }

/-- Ring equivalences are isomorphisms in category of rings -/
@[simps]
def _root_.RingEquiv.toRingCatIso {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm

instance forgetReflectIsos : (forget RingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget RingCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toRingCatIso.isIso_hom

end RingCat

/-- The category of commutative semirings. -/
structure CommSemiRingCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type u
  [commSemiring : CommSemiring carrier]

attribute [instance] CommSemiRingCat.commSemiring

initialize_simps_projections CommSemiRingCat (-commSemiring)

namespace CommSemiRingCat

instance : CoeSort (CommSemiRingCat) (Type u) :=
  ⟨CommSemiRingCat.carrier⟩

attribute [coe] CommSemiRingCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommSemiRingCat`. -/
abbrev of (R : Type u) [CommSemiring R] : CommSemiRingCat :=
  ⟨R⟩

lemma coe_of (R : Type u) [CommSemiring R] : (of R : Type u) = R :=
  rfl

lemma of_carrier (R : CommSemiRingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `CommSemiRingCat`. -/
@[ext]
structure Hom (R S : CommSemiRingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R →+* S

instance : Category CommSemiRingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} CommSemiRingCat (fun R S => R →+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `CommSemiRingCat` back into a `RingHom`. -/
abbrev Hom.hom {R S : CommSemiRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := CommSemiRingCat) f

/-- Typecheck a `RingHom` as a morphism in `CommSemiRingCat`. -/
abbrev ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := CommSemiRingCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (R S : CommSemiRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {R : CommSemiRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/
lemma id_apply (R : CommSemiRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
lemma hom_comp {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : CommSemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {R S : CommSemiRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {R : Type u} [CommSemiring R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
lemma ofHom_comp {R S T : Type u} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R S : Type u} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl

lemma inv_hom_apply {R S : CommSemiRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp

lemma hom_inv_apply {R S : CommSemiRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp

instance : Inhabited CommSemiRingCat :=
  ⟨of PUnit⟩

set_option linter.style.commandStart false in -- TODO investigate and fix!
/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`. -/
unif_hint forget_obj_eq_coe (R R' : CommSemiRingCat) where
  R ≟ R' ⊢
  (forget CommSemiRingCat).obj R ≟ CommSemiRingCat.carrier R'

lemma forget_obj {R : CommSemiRingCat} : (forget CommSemiRingCat).obj R = R := rfl

lemma forget_map {R S : CommSemiRingCat} (f : R ⟶ S) :
    (forget CommSemiRingCat).map f = f :=
  rfl

instance {R : CommSemiRingCat} : CommSemiring ((forget CommSemiRingCat).obj R) :=
  (inferInstance : CommSemiring R.carrier)

instance hasForgetToSemiRingCat : HasForget₂ CommSemiRingCat SemiRingCat where
  forget₂ :=
    { obj := fun R ↦ ⟨R⟩
      map := fun f ↦ ⟨f.hom⟩ }

/-- The forgetful functor from `CommSemiRingCat` to `SemiRingCat` is fully faithful. -/
def fullyFaithfulForget₂ToSemiRingCat :
    (forget₂ CommSemiRingCat SemiRingCat).FullyFaithful where
  preimage f := ofHom f.hom

instance : (forget₂ CommSemiRingCat SemiRingCat).Full :=
  fullyFaithfulForget₂ToSemiRingCat.full

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommMonCat : HasForget₂ CommSemiRingCat CommMonCat where
  forget₂ :=
    { obj := fun R ↦ CommMonCat.of R
      map := fun f ↦ CommMonCat.ofHom f.hom.toMonoidHom }

/-- Ring equivalences are isomorphisms in category of commutative semirings -/
@[simps]
def _root_.RingEquiv.toCommSemiRingCatIso
    {R S : Type u} [CommSemiring R] [CommSemiring S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm

instance forgetReflectIsos : (forget CommSemiRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommSemiRingCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommSemiRingCatIso.isIso_hom

end CommSemiRingCat

/-- The category of commutative rings. -/
structure CommRingCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type u
  [commRing : CommRing carrier]

attribute [instance] CommRingCat.commRing

initialize_simps_projections CommRingCat (-commRing)

namespace CommRingCat

instance : CoeSort (CommRingCat) (Type u) :=
  ⟨CommRingCat.carrier⟩

attribute [coe] CommRingCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommRingCat`. -/
abbrev of (R : Type u) [CommRing R] : CommRingCat :=
  ⟨R⟩

lemma coe_of (R : Type u) [CommRing R] : (of R : Type u) = R :=
  rfl

lemma of_carrier (R : CommRingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `CommRingCat`. -/
@[ext]
structure Hom (R S : CommRingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R →+* S

instance : Category CommRingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} CommRingCat (fun R S => R →+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- The underlying ring hom. -/
abbrev Hom.hom {R S : CommRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := CommRingCat) f

/-- Typecheck a `RingHom` as a morphism in `CommRingCat`. -/
abbrev ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := CommRingCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (R S : CommRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {R : CommRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/
lemma id_apply (R : CommRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
lemma hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {R S : CommRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {R : Type u} [CommRing R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
lemma ofHom_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl

lemma inv_hom_apply {R S : CommRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp

lemma hom_inv_apply {R S : CommRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp

instance : Inhabited CommRingCat :=
  ⟨of PUnit⟩

lemma forget_obj {R : CommRingCat} : (forget CommRingCat).obj R = R := rfl

set_option linter.style.commandStart false in -- TODO fix linter/pretty-printing!
/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying `TopCat.Presheaf.restrictOpen` to commutative rings.
-/
unif_hint forget_obj_eq_coe (R R' : CommRingCat) where
  R ≟ R' ⊢
  (forget CommRingCat).obj R ≟ CommRingCat.carrier R'

lemma forget_map {R S : CommRingCat} (f : R ⟶ S) :
    (forget CommRingCat).map f = f :=
  rfl

instance {R : CommRingCat} : CommRing ((forget CommRingCat).obj R) :=
  (inferInstance : CommRing R.carrier)

instance hasForgetToRingCat : HasForget₂ CommRingCat RingCat where
  forget₂ :=
    { obj := fun R ↦ RingCat.of R
      map := fun f ↦ RingCat.ofHom f.hom }

/-- The forgetful functor from `CommRingCat` to `RingCat` is fully faithful. -/
def fullyFaithfulForget₂ToRingCat :
    (forget₂ CommRingCat RingCat).FullyFaithful where
  preimage f := ofHom f.hom

instance : (forget₂ CommRingCat RingCat).Full :=
  fullyFaithfulForget₂ToRingCat.full

@[simp] lemma forgetToRingCat_map_hom {R S : CommRingCat} (f : R ⟶ S) :
    ((forget₂ CommRingCat RingCat).map f).hom = f.hom :=
  rfl

@[simp] lemma forgetToRingCat_obj {R : CommRingCat} :
    (((forget₂ CommRingCat RingCat).obj R) : Type u) = R :=
  rfl

instance hasForgetToAddCommMonCat : HasForget₂ CommRingCat CommSemiRingCat where
  forget₂ :=
    { obj := fun R ↦ CommSemiRingCat.of R
      map := fun f ↦ CommSemiRingCat.ofHom f.hom }

@[simps]
instance : HasForget₂ CommRingCat CommMonCat where
  forget₂ := { obj M := .of M, map f := CommMonCat.ofHom f.hom }
  forget_comp := rfl

/-- Ring equivalences are isomorphisms in category of commutative rings -/
@[simps]
def _root_.RingEquiv.toCommRingCatIso
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm

instance forgetReflectIsos : (forget CommRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommRingCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommRingCatIso.isIso_hom

end CommRingCat

namespace CategoryTheory.Iso

/-- Build a `RingEquiv` from an isomorphism in the category `SemiRingCat`. -/
def semiRingCatIsoToRingEquiv {R S : SemiRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofHomInv e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `RingEquiv` from an isomorphism in the category `RingCat`. -/
def ringCatIsoToRingEquiv {R S : RingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofHomInv e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `RingEquiv` from an isomorphism in the category `CommSemiRingCat`. -/
def commSemiRingCatIsoToRingEquiv {R S : CommSemiRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofHomInv e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `RingEquiv` from an isomorphism in the category `CommRingCat`. -/
def commRingCatIsoToRingEquiv {R S : CommRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofHomInv e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

@[simp] lemma semiRingCatIsoToRingEquiv_toRingHom {R S : SemiRingCat.{u}} (e : R ≅ S) :
    (e.semiRingCatIsoToRingEquiv : R →+* S) = e.hom.hom := rfl

@[simp] lemma ringCatIsoToRingEquiv_toRingHom {R S : RingCat.{u}} (e : R ≅ S) :
    (e.ringCatIsoToRingEquiv : R →+* S) = e.hom.hom := rfl

@[simp] lemma commSemiRingCatIsoToRingEquiv_toRingHom {R S : CommSemiRingCat.{u}} (e : R ≅ S) :
    (e.commSemiRingCatIsoToRingEquiv : R →+* S) = e.hom.hom := rfl

@[simp] lemma commRingCatIsoToRingEquiv_toRingHom {R S : CommRingCat.{u}} (e : R ≅ S) :
    (e.commRingCatIsoToRingEquiv : R →+* S) = e.hom.hom := rfl

end CategoryTheory.Iso

lemma RingCat.forget_map_apply {R S : RingCat} (f : R ⟶ S)
    (x : (CategoryTheory.forget RingCat).obj R) :
    (forget _).map f x = f x :=
  rfl

lemma CommRingCat.forget_map_apply {R S : CommRingCat} (f : R ⟶ S)
    (x : (CategoryTheory.forget CommRingCat).obj R) :
    (forget _).map f x = f x :=
  rfl
