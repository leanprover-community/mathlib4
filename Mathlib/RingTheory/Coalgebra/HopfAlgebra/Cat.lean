import Mathlib.RingTheory.Coalgebra.Bialgebra.Cat
import Mathlib.RingTheory.Coalgebra.HopfAlgebra.Basic
open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe v u

variable (R : Type u) [CommRing R]

structure HopfAlgCat where
  /-- the underlying type of an object in `HopfAlgCat R` -/
  carrier : Type v
  [isRing : Ring carrier]
  [isHopfAlgebra : HopfAlgebra R carrier]

attribute [instance] HopfAlgCat.isRing HopfAlgCat.isHopfAlgebra

/-- An alias for `HopfAlgCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev HopfAlgCatMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := HopfAlgCat.{max v₁ v₂, u₁} R

namespace HopfAlgCat

instance : CoeSort (HopfAlgCat.{v} R) (Type v) :=
  ⟨HopfAlgCat.carrier⟩

attribute [coe] HopfAlgCat.carrier

instance HopfAlgCategory : Category.{v, max (v+1) u} (HopfAlgCat.{v} R) where
  Hom M N := M →b[R] N
  id _ := BialgHom.id R _
  comp f g := g.comp f
  id_comp _ := BialgHom.id_comp _
  comp_id _ := BialgHom.comp_id _
  assoc f g h := BialgHom.comp_assoc h g f

instance {M N : HopfAlgCat.{v} R} : FunLike (M ⟶ N) M N :=
  inferInstanceAs (FunLike (M →b[R] N) M N)

instance {M N : HopfAlgCat.{v} R} : BialgHomClass (M ⟶ N) R M N :=
  BialgHom.coalgHomClass

instance coalgConcreteCategory : ConcreteCategory.{v} (HopfAlgCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => BialgHom.ext (fun x => by
    dsimp at h
    rw [h])⟩

-- Porting note:
-- One might hope these two instances would not be needed,
-- as we already have `Ring M` and `Module R M`,
-- but sometimes we seem to need these when rewriting by lemmas about generic concrete categories.
instance {M : HopfAlgCat.{v} R} : Ring ((forget (HopfAlgCat R)).obj M) :=
  (inferInstance : Ring M)
instance {M : HopfAlgCat.{v} R} : HopfAlgebra R ((forget (HopfAlgCat R)).obj M) :=
  (inferInstance : HopfAlgebra R M)

@[ext]
lemma ext {M N : HopfAlgCat.{v} R} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ h

instance hasForgetToBialgebra : HasForget₂ (HopfAlgCat R) (BialgCat R) where
  forget₂ :=
    { obj := fun M => BialgCat.of R M
      map := fun f => BialgCat.ofHom f }

instance hasForgetToCoalgebra : HasForget₂ (HopfAlgCat R) (CoalgCat R) where
  forget₂ :=
    { obj := fun M => CoalgCat.of R M
      map := fun f => CoalgCat.ofHom f.toCoalgHom }

instance hasForgetToAlgebra : HasForget₂ (HopfAlgCat R) (AlgebraCat R) where
  forget₂ :=
    { obj := fun M => AlgebraCat.of R M
      map := fun f => AlgebraCat.ofHom f.toAlgHom }

instance {M : HopfAlgCat.{v} R} : Ring ((forget₂ (HopfAlgCat R) (AlgebraCat R)).obj M) :=
  (inferInstance : Ring M)
instance {M : HopfAlgCat.{v} R} : HopfAlgebra R ((forget₂ (HopfAlgCat R) (AlgebraCat R)).obj M) :=
  (inferInstance : HopfAlgebra R M)

instance {M : HopfAlgCat.{v} R} : Ring ((forget₂ (HopfAlgCat R) (CoalgCat R)).obj M) :=
  (inferInstance : Ring M)
instance {M : HopfAlgCat.{v} R} : HopfAlgebra R ((forget₂ (HopfAlgCat R) (CoalgCat R)).obj M) :=
  (inferInstance : HopfAlgebra R M)

/-- The object in the category of R-modules associated to an R-module -/
def of (X : Type v) [Ring X] [HopfAlgebra R X] : HopfAlgCat R :=
  ⟨X⟩

@[simp]
theorem forget₂_obj (X : HopfAlgCat R) :
    (forget₂ (HopfAlgCat R) (AlgebraCat R)).obj X = AlgebraCat.of R X :=
  rfl

/-theorem forget₂_obj_HopfAlgCat_of (X : Type v) [Ring X] [HopfAlgebra R X] :
    (forget₂ (HopfAlgCat R) (AlgebraCat R)).obj (of R X) = AlgebraCat.of R X :=
  rfl-/
/-
-- Porting note: the simpNF linter correctly doesn't like this.
-- I'm not sure what this is for, actually.
-- If it is really needed, better might be a simp lemma that says
-- `AlgebraCat.of (HopfAlgCat.of R X) = AlgebraCat.of X`.
-- @[simp 900]
theorem forget₂_obj_HopfAlgCat_of (X : Type v) [Ring X] :
    (forget₂ (HopfAlgCat R) AlgebraCat).obj (of R X) = AlgebraCat.of X :=
  rfl
#align Module.forget₂_obj_Module_of HopfAlgCat.forget₂_obj_HopfAlgCat_of
-/
@[simp]
theorem forget₂_map (X Y : HopfAlgCat R) (f : X ⟶ Y) :
    (forget₂ (HopfAlgCat R) (AlgebraCat R)).map f = BialgHom.toAlgHom f :=
  rfl

-- Porting note: TODO: `ofHom` and `asHom` are duplicates!

/-- Typecheck a `BialgHom` as a morphism in `Module R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [HopfAlgebra R X]
    [Ring Y] [HopfAlgebra R Y] (f : X →b[R] Y) : of R X ⟶ of R Y :=
  f

@[simp 1100]
theorem ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [HopfAlgebra R X]
    [Ring Y] [HopfAlgebra R Y] (f : X →b[R] Y) (x : X) : ofHom f x = f x :=
  rfl

/-instance : Inhabited (HopfAlgCat R) :=
  ⟨of R PUnit⟩-/

instance ofUnique {X : Type v} [Ring X] [HopfAlgebra R X] [i : Unique X] : Unique (of R X) :=
  i

-- Porting note: the simpNF linter complains, but we really need this?!
-- @[simp, nolint simpNF]
theorem coe_of (X : Type v) [Ring X] [HopfAlgebra R X] : (of R X : Type v) = X :=
  rfl

-- bad? idfk
instance (X : HopfAlgCat R) : HopfAlgebra R (AlgebraCat.of R X) :=
  (inferInstance : HopfAlgebra R X)

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[simps]
def ofSelfIso (M : HopfAlgCat R) : HopfAlgCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

/-theorem isZero_of_subsingleton (M : HopfAlgCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨(0 : M →b[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    dsimp
    simp⟩⟩
  unique_from X := ⟨⟨⟨(0 : X →b[R] M)⟩, fun f => by
    ext x
    apply Subsingleton.elim⟩⟩-/

/-instance : HasZeroObject (HopfAlgCat.{v} R) :=
  ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩-/

variable {M N U : HopfAlgCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl

-- porting note: added
@[simp] lemma forget_map (f : M ⟶ N) : (forget (HopfAlgCat R)).map f = (f : M → N) := rfl

end HopfAlgCat

variable {R}

variable {X₁ X₂ : Type v}
/-
/-- Reinterpreting a linear map in the category of `R`-modules. -/
def HopfAlgCat.asHom [Ring X₁] [Module R X₁] [Ring X₂] [Module R X₂] :
    (X₁ →b[R] X₂) → (HopfAlgCat.of R X₁ ⟶ HopfAlgCat.of R X₂) :=
  id

/-- Reinterpreting a linear map in the category of `R`-modules -/
scoped[HopfAlgCat] notation "↟" f:1024 => HopfAlgCat.asHom f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def HopfAlgCat.asHomRight [Ring X₁] [Module R X₁] {X₂ : HopfAlgCat.{v} R} :
    (X₁ →b[R] X₂) → (HopfAlgCat.of R X₁ ⟶ X₂) :=
  id
#align Module.as_hom_right HopfAlgCat.asHomRight

/-- Reinterpreting a linear map in the category of `R`-modules. -/
scoped[HopfAlgCat] notation "↾" f:1024 => HopfAlgCat.asHomRight f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def HopfAlgCat.asHomLeft {X₁ : HopfAlgCat.{v} R} [Ring X₂] [Module R X₂] :
    (X₁ →b[R] X₂) → (X₁ ⟶ HopfAlgCat.of R X₂) :=
  id
#align Module.as_hom_left HopfAlgCat.asHomLeft

/-- Reinterpreting a linear map in the category of `R`-modules. -/
scoped[HopfAlgCat] notation "↿" f:1024 => HopfAlgCat.asHomLeft f
-/
section

/-- Build an isomorphism in the category `Module R` from a `BialgEquiv` between `Module`s. -/
@[simps]
def BialgEquiv.toHopfAlgIso {g₁ : Ring X₁} {g₂ : Ring X₂}
      {c₁ : HopfAlgebra R X₁} {c₂ : HopfAlgebra R X₂} (e : X₁ ≃b[R] X₂) :
      HopfAlgCat.of R X₁ ≅ HopfAlgCat.of R X₂ where
  hom := (e : X₁ →b[R] X₂)
  inv := (e.symm : X₂ →b[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

/-- Build an isomorphism in the category `Module R` from a `BialgEquiv` between `Module`s. -/
abbrev BialgEquiv.toHopfAlgIso' {M N : HopfAlgCat.{v} R} (i : M ≃b[R] N) : M ≅ N :=
  i.toHopfAlgIso

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
abbrev BialgEquiv.toHopfAlgIso'Left {X₁ : HopfAlgCat.{v} R} [Ring X₂] [Module R X₂] [HopfAlgebra R X₂]
    (e : X₁ ≃b[R] X₂) : X₁ ≅ HopfAlgCat.of R X₂ :=
  e.toHopfAlgIso

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
abbrev BialgEquiv.toHopfAlgIso'Right [Ring X₁] [Module R X₁] [HopfAlgebra R X₁] {X₂ : HopfAlgCat.{v} R}
    (e : X₁ ≃b[R] X₂) : HopfAlgCat.of R X₁ ≅ X₂ :=
  e.toHopfAlgIso

namespace CategoryTheory.Iso

/-- Build a `linear_equiv` from an isomorphism in the category `Module R`. -/
def toBialgEquiv' {X Y : HopfAlgCat R} (i : X ≅ Y) : X ≃b[R] Y :=
  { i.hom with
    invFun := i.inv
    left_inv := sorry
    right_inv := sorry }
end CategoryTheory.Iso

/-- linear equivalences between `module`s are the same as (isomorphic to) isomorphisms
in `Module` -/
@[simps]
def bialgEquivIsoHopfAlgIso {X Y : Type u} [Ring X] [Ring Y] [HopfAlgebra R X]
    [HopfAlgebra R Y] : (X ≃b[R] Y) ≅ HopfAlgCat.of R X ≅ HopfAlgCat.of R Y where
  hom e := e.toHopfAlgIso
  inv i := i.toBialgEquiv'

end
