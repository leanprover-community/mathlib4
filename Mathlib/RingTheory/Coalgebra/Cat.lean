import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Coalgebra.Equiv
import Mathlib.Algebra.Category.ModuleCat.Basic

universe v u

variable (R : Type u) [CommRing R]

structure CoalgCat where
  /-- the underlying type of an object in `CoalgCat R` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]
  [isCoalgebra : Coalgebra R carrier]

attribute [instance] CoalgCat.isAddCommGroup CoalgCat.isModule CoalgCat.isCoalgebra

/-- An alias for `CoalgCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev CoalgCatMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := CoalgCat.{max v₁ v₂, u₁} R

namespace CoalgCat
open CategoryTheory

instance : CoeSort (CoalgCat.{v} R) (Type v) :=
  ⟨CoalgCat.carrier⟩

attribute [coe] CoalgCat.carrier

instance CoalgCategory : Category.{v, max (v+1) u} (CoalgCat.{v} R) where
  Hom M N := M →c[R] N
  id _ := CoalgHom.id R _
  comp f g := g.comp f
  id_comp _ := CoalgHom.id_comp _
  comp_id _ := CoalgHom.comp_id _
  assoc f g h := CoalgHom.comp_assoc h g f

instance {M N : CoalgCat.{v} R} : FunLike (M ⟶ N) M N :=
  inferInstanceAs (FunLike (M →c[R] N) M N)

instance {M N : CoalgCat.{v} R} : CoalgHomClass (M ⟶ N) R M N :=
  CoalgHom.coalgHomClass

instance coalgConcreteCategory : ConcreteCategory.{v} (CoalgCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => CoalgHom.ext (fun x => by
    dsimp at h
    rw [h])⟩

-- Porting note:
-- One might hope these two instances would not be needed,
-- as we already have `AddCommGroup M` and `Module R M`,
-- but sometimes we seem to need these when rewriting by lemmas about generic concrete categories.
instance {M : CoalgCat.{v} R} : AddCommGroup ((forget (CoalgCat R)).obj M) :=
  (inferInstance : AddCommGroup M)
instance {M : CoalgCat.{v} R} : Module R ((forget (CoalgCat R)).obj M) :=
  (inferInstance : Module R M)
instance {M : CoalgCat.{v} R} : Coalgebra R ((forget (CoalgCat R)).obj M) :=
  (inferInstance : Coalgebra R M)

@[ext]
lemma ext {M N : CoalgCat.{v} R} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ h

instance hasForgetToModule : HasForget₂ (CoalgCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toLinearMap }

instance {M : CoalgCat.{v} R} : AddCommGroup ((forget₂ (CoalgCat R) (ModuleCat R)).obj M) :=
  (inferInstance : AddCommGroup M)
instance {M : CoalgCat.{v} R} : Module R ((forget₂ (CoalgCat R) (ModuleCat R)).obj M) :=
  (inferInstance : Module R M)
instance {M : CoalgCat.{v} R} : Coalgebra R ((forget₂ (CoalgCat R) (ModuleCat R)).obj M) :=
  (inferInstance : Coalgebra R M)

instance hasForgetToAddCommGroup : HasForget₂ (CoalgCat R) AddCommGroupCat where
  forget₂ :=
    { obj := fun M => AddCommGroupCat.of M
      map := fun f => AddCommGroupCat.ofHom f.toLinearMap }

/-- The object in the category of R-modules associated to an R-module -/
def of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] : CoalgCat R :=
  ⟨X⟩

@[simp]
theorem forget₂_obj (X : CoalgCat R) :
    (forget₂ (CoalgCat R) AddCommGroupCat).obj X = AddCommGroupCat.of X :=
  rfl

theorem forget₂_obj_CoalgCat_of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] :
    (forget₂ (CoalgCat R) (ModuleCat R)).obj (of R X) = ModuleCat.of R X :=
  rfl
/-
-- Porting note: the simpNF linter correctly doesn't like this.
-- I'm not sure what this is for, actually.
-- If it is really needed, better might be a simp lemma that says
-- `AddCommGroupCat.of (CoalgCat.of R X) = AddCommGroupCat.of X`.
-- @[simp 900]
theorem forget₂_obj_CoalgCat_of (X : Type v) [AddCommGroup X] [Module R X] :
    (forget₂ (CoalgCat R) AddCommGroupCat).obj (of R X) = AddCommGroupCat.of X :=
  rfl
#align Module.forget₂_obj_Module_of CoalgCat.forget₂_obj_CoalgCat_of
-/
@[simp]
theorem forget₂_map (X Y : CoalgCat R) (f : X ⟶ Y) :
    (forget₂ (CoalgCat R) (ModuleCat R)).map f = CoalgHom.toLinearMap f :=
  rfl

-- Porting note: TODO: `ofHom` and `asHom` are duplicates!

/-- Typecheck a `CoalgHom` as a morphism in `Module R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X]
    [AddCommGroup Y] [Module R Y] [Coalgebra R Y] (f : X →c[R] Y) : of R X ⟶ of R Y :=
  f

@[simp 1100]
theorem ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X]
    [AddCommGroup Y] [Module R Y] [Coalgebra R Y] (f : X →c[R] Y) (x : X) : ofHom f x = f x :=
  rfl

/-instance : Inhabited (CoalgCat R) :=
  ⟨of R PUnit⟩-/

instance ofUnique {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] [i : Unique X] : Unique (of R X) :=
  i

-- Porting note: the simpNF linter complains, but we really need this?!
-- @[simp, nolint simpNF]
theorem coe_of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] : (of R X : Type v) = X :=
  rfl

-- bad? idfk
instance (X : CoalgCat R) : Coalgebra R (ModuleCat.of R X) :=
  (inferInstance : Coalgebra R X)

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[simps]
def ofSelfIso (M : CoalgCat R) : CoalgCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

/-theorem isZero_of_subsingleton (M : CoalgCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨(0 : M →c[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    dsimp
    simp⟩⟩
  unique_from X := ⟨⟨⟨(0 : X →c[R] M)⟩, fun f => by
    ext x
    apply Subsingleton.elim⟩⟩-/

/-instance : HasZeroObject (CoalgCat.{v} R) :=
  ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩-/

variable {M N U : CoalgCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl

-- porting note: added
@[simp] lemma forget_map (f : M ⟶ N) : (forget (CoalgCat R)).map f = (f : M → N) := rfl

end CoalgCat

variable {R}

variable {X₁ X₂ : Type v}

/-
/-- Reinterpreting a linear map in the category of `R`-modules. -/
def CoalgCat.asHom [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂] :
    (X₁ →c[R] X₂) → (CoalgCat.of R X₁ ⟶ CoalgCat.of R X₂) :=
  id

/-- Reinterpreting a linear map in the category of `R`-modules -/
scoped[CoalgCat] notation "↟" f:1024 => CoalgCat.asHom f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def CoalgCat.asHomRight [AddCommGroup X₁] [Module R X₁] {X₂ : CoalgCat.{v} R} :
    (X₁ →c[R] X₂) → (CoalgCat.of R X₁ ⟶ X₂) :=
  id
#align Module.as_hom_right CoalgCat.asHomRight

/-- Reinterpreting a linear map in the category of `R`-modules. -/
scoped[CoalgCat] notation "↾" f:1024 => CoalgCat.asHomRight f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def CoalgCat.asHomLeft {X₁ : CoalgCat.{v} R} [AddCommGroup X₂] [Module R X₂] :
    (X₁ →c[R] X₂) → (X₁ ⟶ CoalgCat.of R X₂) :=
  id
#align Module.as_hom_left CoalgCat.asHomLeft

/-- Reinterpreting a linear map in the category of `R`-modules. -/
scoped[CoalgCat] notation "↿" f:1024 => CoalgCat.asHomLeft f
-/
section

/-- Build an isomorphism in the category `Module R` from a `CoalgEquiv` between `Module`s. -/
@[simps]
def CoalgEquiv.toCoalgIso {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : Module R X₁}
      {c₁ : Coalgebra R X₁} {m₂ : Module R X₂} {c₂ : Coalgebra R X₂} (e : X₁ ≃c[R] X₂) :
      CoalgCat.of R X₁ ≅ CoalgCat.of R X₂ where
  hom := (e : X₁ →c[R] X₂)
  inv := (e.symm : X₂ →c[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

/-- Build an isomorphism in the category `Module R` from a `CoalgEquiv` between `Module`s. -/
abbrev CoalgEquiv.toCoalgIso' {M N : CoalgCat.{v} R} (i : M ≃c[R] N) : M ≅ N :=
  i.toCoalgIso

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
abbrev CoalgEquiv.toCoalgIso'Left {X₁ : CoalgCat.{v} R} [AddCommGroup X₂] [Module R X₂] [Coalgebra R X₂]
    (e : X₁ ≃c[R] X₂) : X₁ ≅ CoalgCat.of R X₂ :=
  e.toCoalgIso

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
abbrev CoalgEquiv.toCoalgIso'Right [AddCommGroup X₁] [Module R X₁] [Coalgebra R X₁] {X₂ : CoalgCat.{v} R}
    (e : X₁ ≃c[R] X₂) : CoalgCat.of R X₁ ≅ X₂ :=
  e.toCoalgIso

namespace CategoryTheory.Iso

/-- Build a `linear_equiv` from an isomorphism in the category `Module R`. -/
def toCoalgEquiv {X Y : CoalgCat R} (i : X ≅ Y) : X ≃c[R] Y :=
  { i.hom with
    invFun := i.inv
    left_inv := sorry
    right_inv := sorry }
end CategoryTheory.Iso

/-- linear equivalences between `module`s are the same as (isomorphic to) isomorphisms
in `Module` -/
@[simps]
def coalgEquivIsoCoalgIso {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module R X] [Coalgebra R X]
    [Module R Y] [Coalgebra R Y] : (X ≃c[R] Y) ≅ CoalgCat.of R X ≅ CoalgCat.of R Y where
  hom e := e.toCoalgIso
  inv i := i.toCoalgEquiv

end
