import Mathlib.Algebra.Category.AlgebraCat.Monoidal
import Mathlib.RingTheory.BialgEquiv
import Mathlib.RingTheory.CoalgCat
open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe v u

variable (R : Type u) [CommRing R]

namespace AlgebraCat

@[simps] noncomputable instance : BraidedCategory (AlgebraCat R) where
  braiding := fun X Y => (Algebra.TensorProduct.comm _ _ _).toAlgebraIso
  braiding_naturality_right := sorry
  braiding_naturality_left := sorry
  hexagon_forward := sorry
  hexagon_reverse := sorry

end AlgebraCat

structure BialgCat where
  /-- the underlying type of an object in `BialgCat R` -/
  carrier : Type v
  [isRing : Ring carrier]
  [isBialgebra : Bialgebra R carrier]

attribute [instance] BialgCat.isRing BialgCat.isBialgebra

/-- An alias for `BialgCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev BialgCatMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := BialgCat.{max v₁ v₂, u₁} R

namespace BialgCat

instance : CoeSort (BialgCat.{v} R) (Type v) :=
  ⟨BialgCat.carrier⟩

attribute [coe] BialgCat.carrier

instance BialgCategory : Category.{v, max (v+1) u} (BialgCat.{v} R) where
  Hom M N := M →b[R] N
  id _ := BialgHom.id R _
  comp f g := g.comp f
  id_comp _ := BialgHom.id_comp _
  comp_id _ := BialgHom.comp_id _
  assoc f g h := BialgHom.comp_assoc h g f

instance {M N : BialgCat.{v} R} : FunLike (M ⟶ N) M N :=
  inferInstanceAs (FunLike (M →b[R] N) M N)

instance {M N : BialgCat.{v} R} : BialgHomClass (M ⟶ N) R M N :=
  BialgHom.coalgHomClass

instance coalgConcreteCategory : ConcreteCategory.{v} (BialgCat.{v} R) where
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
instance {M : BialgCat.{v} R} : Ring ((forget (BialgCat R)).obj M) :=
  (inferInstance : Ring M)
instance {M : BialgCat.{v} R} : Module R ((forget (BialgCat R)).obj M) :=
  (inferInstance : Module R M)
instance {M : BialgCat.{v} R} : Bialgebra R ((forget (BialgCat R)).obj M) :=
  (inferInstance : Bialgebra R M)

@[ext]
lemma ext {M N : BialgCat.{v} R} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ h

instance hasForgetToCoalgebra : HasForget₂ (BialgCat R) (CoalgCat R) where
  forget₂ :=
    { obj := fun M => CoalgCat.of R M
      map := fun f => CoalgCat.ofHom f.toCoalgHom }

instance hasForgetToAlgebra : HasForget₂ (BialgCat R) (AlgebraCat R) where
  forget₂ :=
    { obj := fun M => AlgebraCat.of R M
      map := fun f => AlgebraCat.ofHom f.toAlgHom }

instance {M : BialgCat.{v} R} : Ring ((forget₂ (BialgCat R) (AlgebraCat R)).obj M) :=
  (inferInstance : Ring M)
instance {M : BialgCat.{v} R} : Algebra R ((forget₂ (BialgCat R) (AlgebraCat R)).obj M) :=
  (inferInstance : Algebra R M)
instance {M : BialgCat.{v} R} : Bialgebra R ((forget₂ (BialgCat R) (AlgebraCat R)).obj M) :=
  (inferInstance : Bialgebra R M)

instance {M : BialgCat.{v} R} : Ring ((forget₂ (BialgCat R) (CoalgCat R)).obj M) :=
  (inferInstance : Ring M)
instance {M : BialgCat.{v} R} : Algebra R ((forget₂ (BialgCat R) (CoalgCat R)).obj M) :=
  (inferInstance : Algebra R M)
instance {M : BialgCat.{v} R} : Bialgebra R ((forget₂ (BialgCat R) (CoalgCat R)).obj M) :=
  (inferInstance : Bialgebra R M)

/-- The object in the category of R-modules associated to an R-module -/
def of (X : Type v) [Ring X] [Bialgebra R X] : BialgCat R :=
  ⟨X⟩

@[simp]
theorem forget₂_obj (X : BialgCat R) :
    (forget₂ (BialgCat R) (AlgebraCat R)).obj X = AlgebraCat.of R X :=
  rfl

/-theorem forget₂_obj_BialgCat_of (X : Type v) [Ring X] [Bialgebra R X] :
    (forget₂ (BialgCat R) (AlgebraCat R)).obj (of R X) = AlgebraCat.of R X :=
  rfl-/
/-
-- Porting note: the simpNF linter correctly doesn't like this.
-- I'm not sure what this is for, actually.
-- If it is really needed, better might be a simp lemma that says
-- `AlgebraCat.of (BialgCat.of R X) = AlgebraCat.of X`.
-- @[simp 900]
theorem forget₂_obj_BialgCat_of (X : Type v) [Ring X] :
    (forget₂ (BialgCat R) AlgebraCat).obj (of R X) = AlgebraCat.of X :=
  rfl
#align Module.forget₂_obj_Module_of BialgCat.forget₂_obj_BialgCat_of
-/
@[simp]
theorem forget₂_map (X Y : BialgCat R) (f : X ⟶ Y) :
    (forget₂ (BialgCat R) (AlgebraCat R)).map f = BialgHom.toAlgHom f :=
  rfl

-- Porting note: TODO: `ofHom` and `asHom` are duplicates!

/-- Typecheck a `BialgHom` as a morphism in `Module R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Bialgebra R X]
    [Ring Y] [Bialgebra R Y] (f : X →b[R] Y) : of R X ⟶ of R Y :=
  f

@[simp 1100]
theorem ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Bialgebra R X]
    [Ring Y] [Bialgebra R Y] (f : X →b[R] Y) (x : X) : ofHom f x = f x :=
  rfl

/-instance : Inhabited (BialgCat R) :=
  ⟨of R PUnit⟩-/

instance ofUnique {X : Type v} [Ring X] [Bialgebra R X] [i : Unique X] : Unique (of R X) :=
  i

-- Porting note: the simpNF linter complains, but we really need this?!
-- @[simp, nolint simpNF]
theorem coe_of (X : Type v) [Ring X] [Bialgebra R X] : (of R X : Type v) = X :=
  rfl

-- bad? idfk
instance (X : BialgCat R) : Bialgebra R (AlgebraCat.of R X) :=
  (inferInstance : Bialgebra R X)

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[simps]
def ofSelfIso (M : BialgCat R) : BialgCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

/-theorem isZero_of_subsingleton (M : BialgCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨(0 : M →b[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    dsimp
    simp⟩⟩
  unique_from X := ⟨⟨⟨(0 : X →b[R] M)⟩, fun f => by
    ext x
    apply Subsingleton.elim⟩⟩-/

/-instance : HasZeroObject (BialgCat.{v} R) :=
  ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩-/

variable {M N U : BialgCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl

-- porting note: added
@[simp] lemma forget_map (f : M ⟶ N) : (forget (BialgCat R)).map f = (f : M → N) := rfl

end BialgCat

variable {R}

variable {X₁ X₂ : Type v}
/-
/-- Reinterpreting a linear map in the category of `R`-modules. -/
def BialgCat.asHom [Ring X₁] [Module R X₁] [Ring X₂] [Module R X₂] :
    (X₁ →b[R] X₂) → (BialgCat.of R X₁ ⟶ BialgCat.of R X₂) :=
  id

/-- Reinterpreting a linear map in the category of `R`-modules -/
scoped[BialgCat] notation "↟" f:1024 => BialgCat.asHom f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def BialgCat.asHomRight [Ring X₁] [Module R X₁] {X₂ : BialgCat.{v} R} :
    (X₁ →b[R] X₂) → (BialgCat.of R X₁ ⟶ X₂) :=
  id
#align Module.as_hom_right BialgCat.asHomRight

/-- Reinterpreting a linear map in the category of `R`-modules. -/
scoped[BialgCat] notation "↾" f:1024 => BialgCat.asHomRight f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def BialgCat.asHomLeft {X₁ : BialgCat.{v} R} [Ring X₂] [Module R X₂] :
    (X₁ →b[R] X₂) → (X₁ ⟶ BialgCat.of R X₂) :=
  id
#align Module.as_hom_left BialgCat.asHomLeft

/-- Reinterpreting a linear map in the category of `R`-modules. -/
scoped[BialgCat] notation "↿" f:1024 => BialgCat.asHomLeft f
-/
section

/-- Build an isomorphism in the category `Module R` from a `BialgEquiv` between `Module`s. -/
@[simps]
def BialgEquiv.toBialgIso {g₁ : Ring X₁} {g₂ : Ring X₂}
      {c₁ : Bialgebra R X₁} {c₂ : Bialgebra R X₂} (e : X₁ ≃b[R] X₂) :
      BialgCat.of R X₁ ≅ BialgCat.of R X₂ where
  hom := (e : X₁ →b[R] X₂)
  inv := (e.symm : X₂ →b[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

/-- Build an isomorphism in the category `Module R` from a `BialgEquiv` between `Module`s. -/
abbrev BialgEquiv.toBialgIso' {M N : BialgCat.{v} R} (i : M ≃b[R] N) : M ≅ N :=
  i.toBialgIso

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
abbrev BialgEquiv.toBialgIso'Left {X₁ : BialgCat.{v} R} [Ring X₂] [Module R X₂] [Bialgebra R X₂]
    (e : X₁ ≃b[R] X₂) : X₁ ≅ BialgCat.of R X₂ :=
  e.toBialgIso

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
abbrev BialgEquiv.toBialgIso'Right [Ring X₁] [Module R X₁] [Bialgebra R X₁] {X₂ : BialgCat.{v} R}
    (e : X₁ ≃b[R] X₂) : BialgCat.of R X₁ ≅ X₂ :=
  e.toBialgIso

namespace CategoryTheory.Iso

/-- Build a `linear_equiv` from an isomorphism in the category `Module R`. -/
def toBialgEquiv {X Y : BialgCat R} (i : X ≅ Y) : X ≃b[R] Y :=
  { i.hom with
    invFun := i.inv
    left_inv := sorry
    right_inv := sorry }
end CategoryTheory.Iso

/-- linear equivalences between `module`s are the same as (isomorphic to) isomorphisms
in `Module` -/
@[simps]
def coalgEquivIsoBialgIso {X Y : Type u} [Ring X] [Ring Y] [Bialgebra R X]
    [Bialgebra R Y] : (X ≃b[R] Y) ≅ BialgCat.of R X ≅ BialgCat.of R Y where
  hom e := e.toBialgIso
  inv i := i.toBialgEquiv

end

namespace Bialgebra
open scoped TensorProduct
/-  refine' Bialgebra.mk' R (A ⊗[R] B) _ _ _ _
  have : Coalgebra.comul = Algebra.TensorProduct.tensorTensorTensorComm R A A B B
    ∘ₗ Algebra.TensorProduct.map (Bialgebra.comulAlgHom R A) (Bialgebra.comulAlgHom R B) := rfl
-/

variable {A B C D : Type u} [Ring A] [Ring B] [Ring C] [Ring D]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]

instance hmmmmmm {A B : Type u} [Ring A] [Ring B]
    [Bialgebra R A] [Bialgebra R B] : Bialgebra R (A ⊗[R] B) :=
    { counit_one := by
        simp only [Coalgebra.tensorProductCoalgebraStruct_counit, LinearMap.coe_comp,
          Function.comp_apply, Algebra.TensorProduct.one_def, TensorProduct.map_tmul, counit_one,
          LinearMap.mul'_apply, mul_one]
      mul_compr₂_counit := by
        ext w x y z
        simp only [Coalgebra.tensorProductCoalgebraStruct_counit, TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
          LinearMap.coe_restrictScalars, LinearMap.compr₂_apply, LinearMap.mul_apply',
          Algebra.TensorProduct.tmul_mul_tmul, LinearMap.coe_comp, Function.comp_apply,
          TensorProduct.map_tmul, counit_mul, LinearMap.mul'_apply, LinearMap.compl₁₂_apply,
          mul_mul_mul_comm]
      comul_one := by
        simp only [Coalgebra.tensorProductCoalgebraStruct_comul, LinearMap.coe_comp,
          LinearEquiv.coe_coe, Function.comp_apply, Algebra.TensorProduct.one_def,
          TensorProduct.map_tmul, comul_one, TensorProduct.tensorTensorTensorComm_tmul]
      mul_compr₂_comul := by
        simp only [Coalgebra.tensorProductCoalgebraStruct_comul]
        ext w x y z
        simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
          LinearMap.coe_restrictScalars, LinearMap.compr₂_apply, LinearMap.mul_apply',
          Algebra.TensorProduct.tmul_mul_tmul, LinearMap.coe_comp, LinearEquiv.coe_coe,
          Function.comp_apply, TensorProduct.map_tmul, comul_mul, LinearMap.compl₁₂_apply]
        sorry
         }

def tensorMap (f : A →b[R] B) (g : C →b[R] D) :
    A ⊗[R] C →b[R] B ⊗[R] D := _


end Bialgebra

@[simps] noncomputable def toMonObj (X : BialgCat R) : Mon_ (AlgebraCat R)ᵒᵖ where
  X := Opposite.op (AlgebraCat.of R X)
  one := (AlgebraCat.ofHom (Bialgebra.counitAlgHom R X)).op
  mul := (AlgebraCat.ofHom (Bialgebra.comulAlgHom R X)).op
  one_mul := by
    simp only [MonoidalCategory.whiskerRight, ← op_comp]
    congr 1
    exact AlgHom.toLinearMap_injective Coalgebra.rTensor_counit_comp_comul
  mul_one := by
    simp only [MonoidalCategory.whiskerLeft, ← op_comp]
    congr 1
    exact AlgHom.toLinearMap_injective Coalgebra.lTensor_counit_comp_comul
  mul_assoc := by
    simp only [MonoidalCategory.whiskerRight, MonoidalCategory.whiskerLeft, ← op_comp,
      MonoidalCategory.associator, Iso.op_hom, Iso.symm_hom]
    congr 1
    simp only [← Category.assoc, Iso.eq_comp_inv]
    exact AlgHom.toLinearMap_injective Coalgebra.coassoc

@[simps] def toMonMap {X Y : BialgCat R} (f : X ⟶ Y) : toMonObj Y ⟶ toMonObj X where
  hom := (AlgebraCat.ofHom f.toAlgHom).op
  one_hom := by
    simp only [toMonObj_X, toMonObj_one, ← op_comp]
    congr
    exact AlgHom.toLinearMap_injective f.counit_comp
  mul_hom := by
    simp only [toMonObj_X, toMonObj_mul, Opposite.unop_op, ← op_comp]
    congr 1
    exact AlgHom.toLinearMap_injective f.map_comp_comul.symm

@[simps] noncomputable def toMon : (BialgCat R)ᵒᵖ ⥤ Mon_ (AlgebraCat R)ᵒᵖ where
  obj := fun X => toMonObj X.unop
  map := fun f => toMonMap f.unop

@[simps] instance ofMonObjCoalgebraStruct (X : Mon_ (AlgebraCat R)ᵒᵖ) :
    CoalgebraStruct R X.X.unop where
  comul := X.mul.unop.toLinearMap
  counit := X.one.unop.toLinearMap

noncomputable abbrev monAlgebraOpToModule :
    Mon_ (AlgebraCat R)ᵒᵖ ⥤ Mon_ (ModuleCat R)ᵒᵖ :=
  (AlgebraCat.toModuleCatMonoidalFunctor R).mapOpposite.toLaxMonoidalFunctor.mapMon

noncomputable def toMonCompMonAlgebraOpToModule : toMon ⋙ monAlgebraOpToModule
    ≅ Functor.op (forget₂ (BialgCat R) (CoalgCat R)) ⋙ CoalgCat.toMon :=
  NatIso.ofComponents (fun X => sorry) sorry

end Bialgebra
