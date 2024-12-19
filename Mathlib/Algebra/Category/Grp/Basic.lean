/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.GroupTheory.Perm.Basic

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

/-- The category of groups and group morphisms. -/
@[to_additive]
def Grp : Type (u + 1) :=
  Bundled Group

/-- The category of additive groups and group morphisms -/
add_decl_doc AddGrp

namespace Grp

@[to_additive]
instance : BundledHom.ParentProjection
  (fun {α : Type*} (h : Group α) => h.toDivInvMonoid.toMonoid) := ⟨⟩

deriving instance LargeCategory for Grp
attribute [to_additive] instGrpLargeCategory

@[to_additive]
instance concreteCategory : ConcreteCategory Grp := by
  dsimp only [Grp]
  infer_instance

@[to_additive]
instance : CoeSort Grp Type* where
  coe X := X.α

@[to_additive]
instance (X : Grp) : Group X := X.str

-- Porting note (https://github.com/leanprover-community/mathlib4/pull/10670): this instance was not necessary in mathlib
@[to_additive]
instance {X Y : Grp} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance instFunLike (X Y : Grp) : FunLike (X ⟶ Y) X Y :=
  show FunLike (X →* Y) X Y from inferInstance

@[to_additive (attr := simp)]
lemma coe_id {X : Grp} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : Grp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive]
lemma comp_def {X Y Z : Grp} {f : X ⟶ Y} {g : Y ⟶ Z} : f ≫ g = g.comp f := rfl

@[simp] lemma forget_map {X Y : Grp} (f : X ⟶ Y) : (forget Grp).map f = (f : X → Y) := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : Grp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

/-- Construct a bundled `Group` from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [Group X] : Grp :=
  Bundled.of X

/-- Construct a bundled `AddGroup` from the underlying type and typeclass. -/
add_decl_doc AddGrp.of

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Group R] : ↑(Grp.of R) = R :=
  rfl

@[to_additive (attr := simp)]
theorem coe_comp' {G H K : Type _} [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) :
    @DFunLike.coe (G →* K) G (fun _ ↦ K) MonoidHom.instFunLike (CategoryStruct.comp
      (X := Grp.of G) (Y := Grp.of H) (Z := Grp.of K) f g) = g ∘ f :=
  rfl

@[to_additive (attr := simp)]
theorem coe_id' {G : Type _} [Group G] :
    @DFunLike.coe (G →* G) G (fun _ ↦ G) MonoidHom.instFunLike
      (CategoryStruct.id (X := Grp.of G)) = id :=
  rfl

@[to_additive]
instance : Inhabited Grp :=
  ⟨Grp.of PUnit⟩

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ Grp MonCat :=
  BundledHom.forget₂ _ _

@[to_additive]
instance : Coe Grp.{u} MonCat.{u} where coe := (forget₂ Grp MonCat).obj

@[to_additive]
instance (G H : Grp) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : Grp) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

/-- Typecheck a `MonoidHom` as a morphism in `Grp`. -/
@[to_additive]
def ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  f

/-- Typecheck an `AddMonoidHom` as a morphism in `AddGroup`. -/
add_decl_doc AddGrp.ofHom

@[to_additive]
theorem ofHom_apply {X Y : Type _} [Group X] [Group Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl

@[to_additive]
instance ofUnique (G : Type*) [Group G] [i : Unique G] : Unique (Grp.of G) := i

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : Grp} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for groups. -/
@[to_additive (attr := simps)
  "Universe lift functor for additive groups."]
def uliftFunctor : Grp.{v} ⥤ Grp.{max v u} where
  obj X := Grp.of (ULift.{u, v} X)
  map {_ _} f := Grp.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end Grp

/-- The category of commutative groups and group morphisms. -/
@[to_additive]
def CommGrp : Type (u + 1) :=
  Bundled CommGroup

/-- The category of additive commutative groups and group morphisms. -/
add_decl_doc AddCommGrp

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbrev Ab := AddCommGrp

namespace CommGrp

@[to_additive]
instance : BundledHom.ParentProjection @CommGroup.toGroup := ⟨⟩

deriving instance LargeCategory for CommGrp
attribute [to_additive] instCommGrpLargeCategory

@[to_additive]
instance concreteCategory : ConcreteCategory CommGrp := by
  dsimp only [CommGrp]
  infer_instance

@[to_additive]
instance : CoeSort CommGrp Type* where
  coe X := X.α

@[to_additive]
instance commGroupInstance (X : CommGrp) : CommGroup X := X.str

-- Porting note (https://github.com/leanprover-community/mathlib4/pull/10670): this instance was not necessary in mathlib
@[to_additive]
instance {X Y : CommGrp} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance instFunLike (X Y : CommGrp) : FunLike (X ⟶ Y) X Y :=
  show FunLike (X →* Y) X Y from inferInstance

@[to_additive (attr := simp)]
lemma coe_id {X : CommGrp} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommGrp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive]
lemma comp_def {X Y Z : CommGrp} {f : X ⟶ Y} {g : Y ⟶ Z} : f ≫ g = g.comp f := rfl

@[to_additive (attr := simp)]
lemma forget_map {X Y : CommGrp} (f : X ⟶ Y) :
    (forget CommGrp).map f = (f : X → Y) :=
  rfl

@[to_additive (attr := ext)]
lemma ext {X Y : CommGrp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

/-- Construct a bundled `CommGroup` from the underlying type and typeclass. -/
@[to_additive]
def of (G : Type u) [CommGroup G] : CommGrp :=
  Bundled.of G

/-- Construct a bundled `AddCommGroup` from the underlying type and typeclass. -/
add_decl_doc AddCommGrp.of

@[to_additive]
instance : Inhabited CommGrp :=
  ⟨CommGrp.of PUnit⟩

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [CommGroup R] : (CommGrp.of R : Type u) = R :=
  rfl

@[to_additive (attr := simp)]
theorem coe_comp' {G H K : Type _} [CommGroup G] [CommGroup H] [CommGroup K]
    (f : G →* H) (g : H →* K) :
    @DFunLike.coe (G →* K) G (fun _ ↦ K) MonoidHom.instFunLike (CategoryStruct.comp
      (X := CommGrp.of G) (Y := CommGrp.of H) (Z := CommGrp.of K) f g) = g ∘ f :=
  rfl

@[to_additive (attr := simp)]
theorem coe_id' {G : Type _} [CommGroup G] :
    @DFunLike.coe (G →* G) G (fun _ ↦ G) MonoidHom.instFunLike
      (CategoryStruct.id (X := CommGrp.of G)) = id :=
  rfl

@[to_additive]
instance ofUnique (G : Type*) [CommGroup G] [i : Unique G] : Unique (CommGrp.of G) :=
  i

@[to_additive]
instance hasForgetToGroup : HasForget₂ CommGrp Grp :=
  BundledHom.forget₂ _ _

@[to_additive]
instance : Coe CommGrp.{u} Grp.{u} where coe := (forget₂ CommGrp Grp).obj

@[to_additive hasForgetToAddCommMonCat]
instance hasForgetToCommMonCat : HasForget₂ CommGrp CommMonCat :=
  InducedCategory.hasForget₂ fun G : CommGrp => CommMonCat.of G

@[to_additive]
instance : Coe CommGrp.{u} CommMonCat.{u} where coe := (forget₂ CommGrp CommMonCat).obj

@[to_additive]
instance (G H : CommGrp) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : CommGrp) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

/-- Typecheck a `MonoidHom` as a morphism in `CommGroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  f

/-- Typecheck an `AddMonoidHom` as a morphism in `AddCommGroup`. -/
add_decl_doc AddCommGrp.ofHom

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type _} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    @DFunLike.coe (X →* Y) X (fun _ ↦ Y) _ (ofHom f) x = f x :=
  rfl

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : CommGrp} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for commutative groups. -/
@[to_additive (attr := simps)
  "Universe lift functor for additive commutative groups."]
def uliftFunctor : CommGrp.{v} ⥤ CommGrp.{max v u} where
  obj X := CommGrp.of (ULift.{u, v} X)
  map {_ _} f := CommGrp.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommGrp

namespace AddCommGrp

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ULiftInstances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
def asHom {G : AddCommGrp.{0}} (g : G) : AddCommGrp.of ℤ ⟶ G :=
  zmultiplesHom G g

@[simp]
theorem asHom_apply {G : AddCommGrp.{0}} (g : G) (i : ℤ) :
    @DFunLike.coe (ℤ →+ ↑G) ℤ (fun _ ↦ ↑G) _ (asHom g) i = i • g :=
  rfl

theorem asHom_injective {G : AddCommGrp.{0}} : Function.Injective (@asHom G) := fun h k w => by
  convert congr_arg (fun k : AddCommGrp.of ℤ ⟶ G => (k : ℤ → G) (1 : ℤ)) w <;> simp

@[ext]
theorem int_hom_ext {G : AddCommGrp.{0}} (f g : AddCommGrp.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  @AddMonoidHom.ext_int G _ f g w

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
theorem injective_of_mono {G H : AddCommGrp.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by aesop_cat
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1

end AddCommGrp

/-- Build an isomorphism in the category `Grp` from a `MulEquiv` between `Group`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toGrpIso {X Y : Grp} (e : X ≃* Y) : X ≅ Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddGroup` from an `AddEquiv` between `AddGroup`s. -/
add_decl_doc AddEquiv.toAddGrpIso

/-- Build an isomorphism in the category `CommGrp` from a `MulEquiv`
between `CommGroup`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toCommGrpIso {X Y : CommGrp} (e : X ≃* Y) : X ≅ Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddCommGrp` from an `AddEquiv`
between `AddCommGroup`s. -/
add_decl_doc AddEquiv.toAddCommGrpIso

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `Grp`. -/
@[to_additive (attr := simp)]
def groupIsoToMulEquiv {X Y : Grp} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id

/-- Build an `addEquiv` from an isomorphism in the category `AddGroup` -/
add_decl_doc addGroupIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive (attr := simps!)]
def commGroupIsoToMulEquiv {X Y : CommGrp} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id

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
  hom :=
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv :=
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
  "An alias for `AddGrp.{max u v}`, to deal around unification issues."]
abbrev GrpMax.{u1, u2} := Grp.{max u1 u2}
/-- An alias for `AddGrp.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddGrpMax.{u1, u2} := AddGrp.{max u1 u2}

/-- An alias for `CommGrp.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) AddCommGrpMaxAux
  "An alias for `AddCommGrp.{max u v}`, to deal around unification issues."]
abbrev CommGrpMax.{u1, u2} := CommGrp.{max u1 u2}
/-- An alias for `AddCommGrp.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddCommGrpMax.{u1, u2} := AddCommGrp.{max u1 u2}

/-!
`@[simp]` lemmas for `MonoidHom.comp` and categorical identities.
-/

@[to_additive (attr := simp)] theorem MonoidHom.comp_id_grp
    {G : Grp.{u}} {H : Type u} [Group H] (f : G →* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (Grp.ofHom f)
@[to_additive (attr := simp)] theorem MonoidHom.id_grp_comp
    {G : Type u} [Group G] {H : Grp.{u}} (f : G →* H) : MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (Grp.ofHom f)

@[to_additive (attr := simp)] theorem MonoidHom.comp_id_commGrp
    {G : CommGrp.{u}} {H : Type u} [CommGroup H] (f : G →* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (CommGrp.ofHom f)
@[to_additive (attr := simp)] theorem MonoidHom.id_commGrp_comp
    {G : Type u} [CommGroup G] {H : CommGrp.{u}} (f : G →* H) : MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (CommGrp.ofHom f)
