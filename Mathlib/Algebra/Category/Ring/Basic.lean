/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.PUnit

/-!
# Category instances for `Semiring`, `Ring`, `CommSemiring`, and `CommRing`.

We introduce the bundled categories:
* `SemiRingCat`
* `RingCat`
* `CommSemiRingCat`
* `CommRingCat`

along with the relevant forgetful functors between them.
-/

@[expose] public section

universe u v

open CategoryTheory

/-- The category of semirings. -/
structure SemiRingCat where
  /-- The object in the category of semirings associated to a type equipped with the appropriate
  typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [semiring : Semiring carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `SemiRingCat.of R` being printed as `{ carrier := R, semiring := ... }` by
`delabStructureInstance`. -/
@[app_delab SemiRingCat.of]
meta def SemiRingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] SemiRingCat.semiring

initialize_simps_projections SemiRingCat (-semiring)

namespace SemiRingCat

instance : CoeSort SemiRingCat (Type u) :=
  ⟨SemiRingCat.carrier⟩

attribute [coe] SemiRingCat.carrier

lemma coe_of (R : Type u) [Semiring R] : (of R : Type u) = R :=
  rfl

lemma of_carrier (R : SemiRingCat.{u}) : of R = R := rfl

mk_concrete_category SemiRingCat (· →+* ·) RingHom.id RingHom.comp
  with_of_hom {R S : Type u} [Semiring R] [Semiring S]
  hom_type (R →+* S) from (SemiRingCat.of R) to (SemiRingCat.of S)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/- Provided for rewriting. -/
lemma id_apply (R : SemiRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

/- Provided for rewriting. -/
lemma comp_apply {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : SemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

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

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`. -/
unif_hint forget_obj_eq_coe (R R' : SemiRingCat) where
  R ≟ R' ⊢
  (forget SemiRingCat).obj R ≟ SemiRingCat.carrier R'

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

instance {R : SemiRingCat} : Semiring ((forget SemiRingCat).obj R) :=
  inferInstanceAs <| Semiring R.carrier

instance hasForgetToMonCat : HasForget₂ SemiRingCat MonCat where
  forget₂ :=
    { obj := fun R ↦ MonCat.of R
      map := fun f ↦ MonCat.ofHom f.hom.toMonoidHom }

instance hasForgetToAddCommMonCat : HasForget₂ SemiRingCat AddCommMonCat where
  forget₂ :=
    { obj := fun R ↦ AddCommMonCat.of R
      map := fun f ↦ AddCommMonCat.ofHom f.hom.toAddMonoidHom }

@[simp] lemma forget₂_monCat_map {R S : SemiRingCat} (f : R ⟶ S) (x) :
    (forget₂ SemiRingCat MonCat).map f x = f x := rfl

@[simp] lemma forget₂_addCommMonCat_map {R S : SemiRingCat} (f : R ⟶ S) (x) :
    (forget₂ SemiRingCat AddCommMonCat).map f x = f x := rfl

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
  /-- The object in the category of rings associated to a type equipped with the appropriate
  typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [ring : Ring carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `RingCat.of R` being printed as `{ carrier := R, ring := ... }` by
`delabStructureInstance`. -/
@[app_delab RingCat.of]
meta def RingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] RingCat.ring

initialize_simps_projections RingCat (-ring)

namespace RingCat

instance : CoeSort RingCat (Type u) :=
  ⟨RingCat.carrier⟩

attribute [coe] RingCat.carrier

lemma coe_of (R : Type u) [Ring R] : (of R : Type u) = R :=
  rfl

lemma of_carrier (R : RingCat.{u}) : of R = R := rfl

mk_concrete_category RingCat (· →+* ·) RingHom.id RingHom.comp
  with_of_hom {R S : Type u} [Ring R] [Ring S]
  hom_type (R →+* S) from (RingCat.of R) to (RingCat.of S)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/- Provided for rewriting. -/
lemma id_apply (R : RingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

/- Provided for rewriting. -/
lemma comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : RingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

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

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying
`PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective`.
-/
unif_hint forget_obj_eq_coe (R R' : RingCat) where
  R ≟ R' ⊢
  (forget RingCat).obj R ≟ RingCat.carrier R'

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

instance {R : RingCat} : Ring ((forget RingCat).obj R) :=
  inferInstanceAs <| Ring R.carrier

instance hasForgetToSemiRingCat : HasForget₂ RingCat SemiRingCat where
  forget₂ :=
    { obj := fun R ↦ SemiRingCat.of R
      map := fun f ↦ SemiRingCat.ofHom f.hom }

@[simp] lemma forget₂_map {R S : RingCat} (f : R ⟶ S) (x) :
    (forget₂ RingCat SemiRingCat).map f x = f x := rfl

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
  /-- The object in the category of commutative semirings associated to a type equipped with the
  appropriate typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [commSemiring : CommSemiring carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `CommSemiRingCat.of R` being printed as `{ carrier := R, commSemiring := ... }` by
`delabStructureInstance`. -/
@[app_delab CommSemiRingCat.of]
meta def CommSemiRingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] CommSemiRingCat.commSemiring

initialize_simps_projections CommSemiRingCat (-commSemiring)

namespace CommSemiRingCat

instance : CoeSort (CommSemiRingCat) (Type u) :=
  ⟨CommSemiRingCat.carrier⟩

attribute [coe] CommSemiRingCat.carrier

lemma coe_of (R : Type u) [CommSemiring R] : (of R : Type u) = R :=
  rfl

lemma of_carrier (R : CommSemiRingCat.{u}) : of R = R := rfl

mk_concrete_category CommSemiRingCat (· →+* ·) RingHom.id RingHom.comp
  with_of_hom {R S : Type u} [CommSemiring R] [CommSemiring S]
  hom_type (R →+* S) from (CommSemiRingCat.of R) to (CommSemiRingCat.of S)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/- Provided for rewriting. -/
lemma id_apply (R : CommSemiRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

/- Provided for rewriting. -/
lemma comp_apply {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : CommSemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

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

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`. -/
unif_hint forget_obj_eq_coe (R R' : CommSemiRingCat) where
  R ≟ R' ⊢
  (forget CommSemiRingCat).obj R ≟ CommSemiRingCat.carrier R'

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

instance {R : CommSemiRingCat} : CommSemiring ((forget CommSemiRingCat).obj R) :=
  inferInstanceAs <| CommSemiring R.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
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
  /-- The object in the category of commutative rings associated to a type equipped with the
  appropriate typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [commRing : CommRing carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `CommRingCat.of R` being printed as `{ carrier := R, commRing := ... }` by
`delabStructureInstance`. -/
@[app_delab CommRingCat.of]
meta def CommRingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] CommRingCat.commRing

initialize_simps_projections CommRingCat (-commRing)

namespace CommRingCat

instance : CoeSort CommRingCat (Type u) :=
  ⟨CommRingCat.carrier⟩

attribute [coe] CommRingCat.carrier

lemma coe_of (R : Type u) [CommRing R] : (of R : Type u) = R :=
  rfl

lemma of_carrier (R : CommRingCat.{u}) : of R = R := rfl

mk_concrete_category CommRingCat (· →+* ·) RingHom.id RingHom.comp
  with_of_hom {R S : Type u} [CommRing R] [CommRing S]
  hom_type (R →+* S) from (CommRingCat.of R) to (CommRingCat.of S)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/- Provided for rewriting. -/
lemma id_apply (R : CommRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

/- Provided for rewriting. -/
lemma comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

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

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying `TopCat.Presheaf.restrictOpen` to commutative rings.
-/
unif_hint forget_obj_eq_coe (R R' : CommRingCat) where
  R ≟ R' ⊢
  (forget CommRingCat).obj R ≟ CommRingCat.carrier R'

instance {R : CommRingCat} : CommRing ((forget CommRingCat).obj R) :=
  inferInstanceAs <| CommRing R.carrier

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

@[simps (nameStem := "commMon")]
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
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `RingEquiv` from an isomorphism in the category `RingCat`. -/
def ringCatIsoToRingEquiv {R S : RingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `RingEquiv` from an isomorphism in the category `CommSemiRingCat`. -/
def commSemiRingCatIsoToRingEquiv {R S : CommSemiRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `RingEquiv` from an isomorphism in the category `CommRingCat`. -/
def commRingCatIsoToRingEquiv {R S : CommRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

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
