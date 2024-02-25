import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.RingTheory.Coalgebra
import Mathlib.RingTheory.CoalgHom
import Mathlib.RingTheory.CoalgEquiv
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Transport
open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

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

namespace CoalgCat

@[simps] def toMonObj (X : CoalgCat R) : Mon_ (ModuleCat R)ᵒᵖ where
  X := Opposite.op (ModuleCat.of R X)
  one := (ModuleCat.ofHom Coalgebra.counit).op
  mul := (ModuleCat.ofHom Coalgebra.comul).op
  one_mul := by
    simp only [MonoidalCategory.whiskerRight, ← op_comp]
    congr 1
    exact Coalgebra.rTensor_counit_comp_comul
  mul_one := by
    simp only [MonoidalCategory.whiskerLeft, ← op_comp]
    congr 1
    exact Coalgebra.lTensor_counit_comp_comul
  mul_assoc := by
    simp only [MonoidalCategory.whiskerRight, MonoidalCategory.whiskerLeft, ← op_comp,
      MonoidalCategory.associator, Iso.op_hom, Iso.symm_hom]
    congr 1
    simp only [← Category.assoc, Iso.eq_comp_inv]
    exact Coalgebra.coassoc

@[simps] def toMonMap {X Y : CoalgCat R} (f : X ⟶ Y) : toMonObj Y ⟶ toMonObj X where
  hom := (ModuleCat.ofHom f.toLinearMap).op
  one_hom := by
    simp only [toMonObj_X, toMonObj_one, ← op_comp]
    congr
    exact f.counit_comp
  mul_hom := by
    simp only [toMonObj_X, toMonObj_mul, Opposite.unop_op, ← op_comp]
    congr 1
    exact f.map_comp_comul.symm

@[simps] def toMon : (CoalgCat R)ᵒᵖ ⥤ Mon_ (ModuleCat R)ᵒᵖ where
  obj := fun X => toMonObj X.unop
  map := fun f => toMonMap f.unop

@[simps] instance ofMonObjCoalgebraStruct (X : Mon_ (ModuleCat R)ᵒᵖ) :
    CoalgebraStruct R X.X.unop where
  comul := X.mul.unop
  counit := X.one.unop

@[simps!] def ofMonObj (X : Mon_ (ModuleCat R)ᵒᵖ) : CoalgCat R where
  carrier := X.X.unop
  isAddCommGroup := by infer_instance
  isModule := by infer_instance
  isCoalgebra := { ofMonObjCoalgebraStruct X with
    coassoc := by
      ext
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        ← LinearEquiv.eq_symm_apply]
      exact LinearMap.ext_iff.1 (congr_arg Quiver.Hom.unop X.mul_assoc) _
    rTensor_counit_comp_comul := by exact congr_arg Quiver.Hom.unop X.one_mul
    lTensor_counit_comp_comul := by exact congr_arg Quiver.Hom.unop X.mul_one }

def ofMonMap {X Y : Mon_ (ModuleCat R)ᵒᵖ} (f : X ⟶ Y) : ofMonObj Y ⟶ ofMonObj X :=
{ f.hom.unop with
  counit_comp := by
    show f.hom.unop ≫ X.one.unop = Y.one.unop
    simp only [← unop_comp, Mon_.Hom.one_hom]
  map_comp_comul := by
    show Y.mul.unop ≫ MonoidalCategory.tensorHom f.hom.unop f.hom.unop = f.hom.unop ≫ X.mul.unop
    simp only [← unop_comp, Mon_.Hom.mul_hom]
    rfl }

@[simps] def ofMon : Mon_ (ModuleCat R)ᵒᵖ ⥤ (CoalgCat R)ᵒᵖ where
  obj := fun X => Opposite.op (ofMonObj X)
  map := fun f => (ofMonMap f).op

@[simps] noncomputable def monEquivalence : (CoalgCat R)ᵒᵖ ≌ Mon_ (ModuleCat R)ᵒᵖ where
  functor := toMon
  inverse := ofMon
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/- already in library ?? :/ -/
instance {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] :
  BraidedCategory Cᵒᵖ where
    braiding := fun X Y => Iso.op (BraidedCategory.braiding X.unop Y.unop).symm
    braiding_naturality_right := fun X Y Z f => by
      simp only [Iso.op_hom, MonoidalCategory.whiskerLeft, MonoidalCategory.whiskerRight,
        ← op_comp]
      congr 1
      rw [← Iso.comp_inv_eq, Category.assoc, ← Iso.eq_inv_comp]
      exact BraidedCategory.braiding_naturality_right X.unop f.unop
    braiding_naturality_left := fun f Z => by
      simp only [Iso.op_hom, MonoidalCategory.whiskerLeft, MonoidalCategory.whiskerRight,
        ← op_comp]
      congr 1
      rw [← Iso.comp_inv_eq, Category.assoc, ← Iso.eq_inv_comp]
      simp only [Iso.symm_inv, BraidedCategory.braiding_naturality_left]
    hexagon_forward := fun X Y Z => by
      simp only [Iso.op_hom, Iso.symm_hom, MonoidalCategory.associator,
        MonoidalCategory.whiskerRight, MonoidalCategory.whiskerLeft,
        MonoidalCategory.tensorObj, ← op_comp, Opposite.unop_op,
        BraidedCategory.braiding_inv_tensor_right, Iso.inv_hom_id_assoc,
        Category.assoc, Iso.hom_inv_id, Category.comp_id, Quiver.Hom.unop_op]
    hexagon_reverse := fun X Y Z => by
      simp only [Iso.op_inv, Iso.op_hom, Iso.symm_inv, Iso.symm_hom,
        MonoidalCategory.associator,
        MonoidalCategory.whiskerRight, MonoidalCategory.whiskerLeft,
        MonoidalCategory.tensorObj, ← op_comp, Opposite.unop_op,
        BraidedCategory.braiding_inv_tensor_left, Category.assoc, Quiver.Hom.unop_op,
        Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]

noncomputable instance : MonoidalCategory (CoalgCat R) :=
  Monoidal.transport (monEquivalence.symm.op.trans (opOpEquivalence _))

open MonoidalCategory

variable {K L M N : CoalgCat R}
variable (R)

noncomputable def tensorObj_equiv (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Coalgebra R M] [Coalgebra R N] :
    (CoalgCat.of R M ⊗ CoalgCat.of R N : CoalgCat R) ≃ₗ[R] TensorProduct R M N :=
  LinearEquiv.refl _ _

variable {R}

@[simp]
theorem tensorObj_comul :
    ModuleCat.ofHom (Coalgebra.comul (R := R) (A := (K ⊗ L : CoalgCat R)))
      = (toMonObj K ⊗ toMonObj L).mul.unop := by
    rfl

@[simp]
theorem tensorObj_comul' :
    ModuleCat.ofHom (Coalgebra.comul (R := R) (A := (K ⊗ L : CoalgCat R)))
      = MonoidalCategory.tensorHom (ModuleCat.ofHom (Coalgebra.comul (R := R) (A := K)))
      (ModuleCat.ofHom (Coalgebra.comul (R := R) (A := L)))
      ≫ tensor_μ _ (ModuleCat.of R K, ModuleCat.of R K) (ModuleCat.of R L, ModuleCat.of R L) := by
    rfl

@[simp]
theorem hom_apply (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ g) (k ⊗ₜ m) = f k ⊗ₜ g m :=
  rfl

@[simp]
theorem whiskerLeft_apply (L : CoalgCat.{u} R) {M N : CoalgCat.{u} R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l ⊗ₜ m) = l ⊗ₜ f m :=
  rfl

@[simp]
theorem whiskerRight_apply {L M : CoalgCat.{u} R} (f : L ⟶ M) (N : CoalgCat.{u} R)
    (l : L) (n : N) :
    (f ▷ N) (l ⊗ₜ n) = f l ⊗ₜ n :=
  rfl

@[simp]
theorem leftUnitor_hom_apply {M : CoalgCat.{u} R} (r : R) (m : M) :
    ((λ_ M).hom : 𝟙_ (CoalgCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

@[simp]
theorem leftUnitor_inv_apply {M : CoalgCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (CoalgCat.{u} R) ⊗ M) m = (1 : R) ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m

@[simp]
theorem rightUnitor_hom_apply {M : CoalgCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M ⊗ 𝟙_ (CoalgCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r

@[simp]
theorem rightUnitor_inv_apply {M : CoalgCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (CoalgCat.{u} R)) m = m ⊗ₜ[R] (1 : R) :=
  TensorProduct.rid_symm_apply m

@[simp]
theorem associator_hom_apply {M N K : CoalgCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ N ⊗ K) (m ⊗ₜ n ⊗ₜ k) = m ⊗ₜ (n ⊗ₜ k) :=
  rfl

@[simp]
theorem associator_inv_apply {M N K : CoalgCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ N ⊗ K ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k :=
  rfl

end CoalgCat
namespace Coalgebra
open TensorProduct
variable {R : Type u} [CommRing R] {M N P Q : Type u}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [Module R M] [Module R N]
  [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N] [Coalgebra R P] [Coalgebra R Q]

@[simps] noncomputable instance tensorProductCoalgebraStruct :
    CoalgebraStruct R (M ⊗[R] N) where
  comul := TensorProduct.tensorTensorTensorComm R M M N N ∘ₗ TensorProduct.map comul comul
  counit := LinearMap.mul' R R ∘ₗ TensorProduct.map counit counit

lemma tensor_μ_eq_tensorTensorTensorComm {A B C D : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B] [Module R C] [Module R D] :
    tensor_μ _ (ModuleCat.of R A, ModuleCat.of R B) (ModuleCat.of R C, ModuleCat.of R D)
      = (TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap :=
  TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext₂ fun _ _ =>
    TensorProduct.ext <| LinearMap.ext₂ fun _ _ => rfl

noncomputable instance : Coalgebra R (M ⊗[R] N) :=
  Coalgebra.ofLinearEquiv (CoalgCat.tensorObj_equiv R M N)
  (by
    simp only [Monoidal.transportStruct_tensorObj, Equivalence.trans_functor,
      Equivalence.op_functor, Equivalence.symm_functor, opOpEquivalence_functor,
      Equivalence.trans_inverse, opOpEquivalence_inverse, Equivalence.op_inverse,
      Equivalence.symm_inverse, Functor.comp_obj, opOp_obj, Functor.op_obj, Opposite.unop_op,
      unop_tensorObj, unopUnop_obj]
    rfl)
  (by
    convert LinearMap.id_comp _
    · exact TensorProduct.map_id
    show ((TensorProduct.tensorTensorTensorComm R _ _ _ _).toLinearMap
      ∘ₗ TensorProduct.map comul comul) ∘ₗ _ = _
    rw [← tensor_μ_eq_tensorTensorTensorComm]
    rfl)

@[simps!] noncomputable def tensorMap (f : M →c[R] N) (g : P →c[R] Q) :
    M ⊗[R] P →c[R] N ⊗[R] Q :=
  { TensorProduct.map f.toLinearMap g.toLinearMap with
    counit_comp := TensorProduct.ext' fun x y => by
      simp only [tensorProductCoalgebraStruct_counit, LinearMap.coe_comp, Function.comp_apply,
        TensorProduct.map_tmul, CoalgHom.toLinearMap_apply, CoalgHom.counit_comp_apply,
        LinearMap.mul'_apply]
/- would've been nice to use the monoidal cat structure for this, maybe make some
lemmas about the coalgebra struct
-/
    map_comp_comul := TensorProduct.ext' fun x y => by
      simp only [tensorProductCoalgebraStruct_comul, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, TensorProduct.map_tmul, CoalgHom.toLinearMap_apply,
        ← f.map_comp_comul_apply, ← g.map_comp_comul_apply]
      simp only [← TensorProduct.mk_apply, ← LinearEquiv.coe_toLinearMap]
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
      conv_rhs =>
        rw [← LinearMap.compl₁₂_apply, ← LinearMap.comp_apply]
      congr 1
      refine' TensorProduct.ext' fun c d => _
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, mk_apply,
        LinearMap.compl₁₂_apply, map_tmul, CoalgHom.toLinearMap_apply]
      refine' (comul x).induction_on _ (fun a b => _) (fun _ _ _ _ => _) <;>
      simp_all only [zero_tmul, map_zero, tensorTensorTensorComm_tmul, map_tmul,
        CoalgHom.toLinearMap_apply, add_tmul, map_add] }

end Coalgebra
