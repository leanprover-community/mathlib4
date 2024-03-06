import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.CoalgCat
import Mathlib.RingTheory.CoalgToMove

universe v u
set_option autoImplicit false
namespace CoalgCat
open CategoryTheory
variable {R : Type u} [CommRing R]

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

variable (R)

@[simps] def toMon : (CoalgCat R)ᵒᵖ ⥤ Mon_ (ModuleCat R)ᵒᵖ where
  obj := fun X => toMonObj X.unop
  map := fun f => toMonMap f.unop

variable {R}

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

variable (R)

@[simps] def ofMon : Mon_ (ModuleCat R)ᵒᵖ ⥤ (CoalgCat R)ᵒᵖ where
  obj := fun X => Opposite.op (ofMonObj X)
  map := fun f => (ofMonMap f).op

@[simps] noncomputable def monEquivalence : (CoalgCat R)ᵒᵖ ≌ Mon_ (ModuleCat R)ᵒᵖ where
  functor := toMon R
  inverse := ofMon R
  unitIso := Iso.refl _
  counitIso := Iso.refl _

noncomputable def instMonoidalCategoryAux : MonoidalCategory (CoalgCat R) :=
  Monoidal.transport ((monEquivalence R).symm.op.trans (opOpEquivalence _))

variable {R}

namespace MonoidalCategoryAux

open scoped MonoidalCategory

variable (M N P Q : Type u) [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

variable (R)

attribute [local instance] instMonoidalCategoryAux

noncomputable def tensorObj_equiv :
    (CoalgCat.of R M ⊗ CoalgCat.of R N : CoalgCat R) ≃ₗ[R] TensorProduct R M N :=
  LinearEquiv.refl _ _

variable {R}

theorem tensorObj_comul (K L : CoalgCat R) :
    Coalgebra.comul (R := R) (A := (K ⊗ L : CoalgCat R))
      = (TensorProduct.tensorTensorTensorComm R K K L L).toLinearMap
      ∘ₗ TensorProduct.map Coalgebra.comul Coalgebra.comul := by
  simp only [Monoidal.transportStruct_tensorObj, Equivalence.trans_functor, Equivalence.op_functor,
    Equivalence.symm_functor, monEquivalence_inverse, opOpEquivalence_functor,
    Equivalence.trans_inverse, opOpEquivalence_inverse, Equivalence.op_inverse,
    Equivalence.symm_inverse, monEquivalence_functor, Functor.comp_obj, opOp_obj, Functor.op_obj,
    Opposite.unop_op, toMon_obj, unop_tensorObj, ofMon_obj, unopUnop_obj, ofMonObj_carrier,
    ofMonObj_isAddCommGroup, ofMonObj_isModule, ofMonObjCoalgebraStruct_comul, Mon_.tensorObj_mul,
    toMonObj_X, toMonObj_mul, unop_comp, unop_tensorHom, Quiver.Hom.unop_op,
    BraidedCategory.unop_tensor_μ, ModuleCat.MonoidalCategory.tensor_μ_eq_tensorTensorTensorComm]
  rfl

theorem tensorObj_counit (K L : CoalgCat R) :
    Coalgebra.counit (R := R) (A := (K ⊗ L : CoalgCat R))
      = LinearMap.mul' R R ∘ₗ TensorProduct.map Coalgebra.counit Coalgebra.counit := by
  rfl

theorem tensorHom_toLinearMap (f : M →c[R] N) (g : P →c[R] Q) :
    (CoalgCat.ofHom f ⊗ CoalgCat.ofHom g).toLinearMap
      = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

theorem associator_hom_toLinearMap :
    (α_ (CoalgCat.of R M) (CoalgCat.of R N) (CoalgCat.of R P)).hom.toLinearMap
      = (TensorProduct.assoc R M N P).toLinearMap :=
  TensorProduct.ext <| TensorProduct.ext <| by ext; rfl

theorem leftUnitor_hom_toLinearMap :
    (λ_ (CoalgCat.of R M)).hom.toLinearMap = (TensorProduct.lid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl

theorem rightUnitor_hom_toLinearMap :
    (ρ_ (CoalgCat.of R M)).hom.toLinearMap = (TensorProduct.rid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl

end CoalgCat.MonoidalCategoryAux
namespace Coalgebra
open CategoryTheory
open scoped TensorProduct

variable {R M N P Q : Type u} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [Module R M] [Module R N]
  [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N] [Coalgebra R P] [Coalgebra R Q]

@[simps] noncomputable instance tensorProductCoalgebraStruct :
    CoalgebraStruct R (M ⊗[R] N) where
  comul := TensorProduct.tensorTensorTensorComm R M M N N ∘ₗ TensorProduct.map comul comul
  counit := LinearMap.mul' R R ∘ₗ TensorProduct.map counit counit

open scoped MonoidalCategory in
noncomputable instance instTensorProduct : Coalgebra R (M ⊗[R] N) :=
  Coalgebra.ofLinearEquiv (CoalgCat.MonoidalCategoryAux.tensorObj_equiv R M N)
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
    simp only [Monoidal.transportStruct_tensorObj, Equivalence.trans_functor,
      Equivalence.op_functor, Equivalence.symm_functor, CoalgCat.monEquivalence_inverse,
      opOpEquivalence_functor, Equivalence.trans_inverse, opOpEquivalence_inverse,
      Equivalence.op_inverse, Equivalence.symm_inverse, CoalgCat.monEquivalence_functor,
      Functor.comp_obj, opOp_obj, Functor.op_obj, Opposite.unop_op, CoalgCat.toMon_obj,
      unop_tensorObj, CoalgCat.ofMon_obj, unopUnop_obj, CoalgCat.ofMonObj_carrier,
      CoalgCat.ofMonObj_isAddCommGroup, CoalgCat.ofMonObj_isModule,
      tensorProductCoalgebraStruct_comul, CoalgCat.ofMonObjCoalgebraStruct_comul,
      Mon_.tensorObj_mul, CoalgCat.toMonObj_X, CoalgCat.toMonObj_mul, unop_comp, unop_tensorHom,
      Quiver.Hom.unop_op, BraidedCategory.unop_tensor_μ,
      ModuleCat.MonoidalCategory.tensor_μ_eq_tensorTensorTensorComm]
    rfl)

end Coalgebra
namespace CoalgCat.MonoidalCategoryAux
open CategoryTheory MonoidalCategory Coalgebra
open scoped TensorProduct

variable {R M N P Q : Type u} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [Module R M] [Module R N]
  [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N] [Coalgebra R P] [Coalgebra R Q]

attribute [local instance] CoalgCat.instMonoidalCategoryAux

lemma tensorObj_comul_eq :
    Coalgebra.comul (R := R) (A := (tensorObj (CoalgCat.of R M) (CoalgCat.of R N) : CoalgCat R))
      = Coalgebra.comul (R := R) (A := M ⊗[R] N) := by
  simp only [Monoidal.transportStruct_tensorObj, Equivalence.trans_functor, Equivalence.op_functor,
    Equivalence.symm_functor, CoalgCat.monEquivalence_inverse, opOpEquivalence_functor,
    Equivalence.trans_inverse, opOpEquivalence_inverse, Equivalence.op_inverse,
    Equivalence.symm_inverse, CoalgCat.monEquivalence_functor, Functor.comp_obj, opOp_obj,
    Functor.op_obj, Opposite.unop_op, CoalgCat.toMon_obj, unop_tensorObj, CoalgCat.ofMon_obj,
    unopUnop_obj, CoalgCat.ofMonObj_carrier, CoalgCat.ofMonObj_isAddCommGroup,
    CoalgCat.ofMonObj_isModule, CoalgCat.ofMonObjCoalgebraStruct_comul, Mon_.tensorObj_mul,
    CoalgCat.toMonObj_X, CoalgCat.toMonObj_mul, unop_comp, unop_tensorHom, Quiver.Hom.unop_op,
    BraidedCategory.unop_tensor_μ, ModuleCat.MonoidalCategory.tensor_μ_eq_tensorTensorTensorComm,
    tensorProductCoalgebraStruct_comul]
  rfl

lemma tensorObj_comul_eq' :
    Coalgebra.comul (R := R) (A := (tensorObj (CoalgCat.of R M)
      (tensorObj (CoalgCat.of R N) (CoalgCat.of R P)) : CoalgCat R))
      = Coalgebra.comul (R := R) (A := M ⊗[R] N ⊗[R] P) := by
  simp only [Monoidal.transportStruct_tensorObj, Equivalence.trans_functor, Equivalence.op_functor,
    Equivalence.symm_functor, CoalgCat.monEquivalence_inverse, opOpEquivalence_functor,
    Equivalence.trans_inverse, opOpEquivalence_inverse, Equivalence.op_inverse,
    Equivalence.symm_inverse, CoalgCat.monEquivalence_functor, Functor.comp_obj, opOp_obj,
    Functor.op_obj, Opposite.unop_op, CoalgCat.toMon_obj, unop_tensorObj, CoalgCat.ofMon_obj,
    unopUnop_obj, CoalgCat.ofMonObj_carrier, CoalgCat.ofMonObj_isAddCommGroup,
    CoalgCat.ofMonObj_isModule, CoalgCat.ofMonObjCoalgebraStruct_comul, Mon_.tensorObj_mul,
    CoalgCat.toMonObj_X, CoalgCat.toMonObj_mul, unop_comp, unop_tensorHom, Quiver.Hom.unop_op,
    BraidedCategory.unop_tensor_μ, ModuleCat.MonoidalCategory.tensor_μ_eq_tensorTensorTensorComm,
    tensorProductCoalgebraStruct_comul]
  rfl

lemma tensorObj_comul_eq'' :
    Coalgebra.comul (R := R) (A := (tensorObj (tensorObj (CoalgCat.of R M)
      (CoalgCat.of R N)) (CoalgCat.of R P) : CoalgCat R))
      = Coalgebra.comul (R := R) (A := (M ⊗[R] N) ⊗[R] P) := by
  simp only [Monoidal.transportStruct_tensorObj, Equivalence.trans_functor, Equivalence.op_functor,
    Equivalence.symm_functor, CoalgCat.monEquivalence_inverse, opOpEquivalence_functor,
    Equivalence.trans_inverse, opOpEquivalence_inverse, Equivalence.op_inverse,
    Equivalence.symm_inverse, CoalgCat.monEquivalence_functor, Functor.comp_obj, opOp_obj,
    Functor.op_obj, Opposite.unop_op, CoalgCat.toMon_obj, unop_tensorObj, CoalgCat.ofMon_obj,
    unopUnop_obj, CoalgCat.ofMonObj_carrier, CoalgCat.ofMonObj_isAddCommGroup,
    CoalgCat.ofMonObj_isModule, CoalgCat.ofMonObjCoalgebraStruct_comul, Mon_.tensorObj_mul,
    CoalgCat.toMonObj_X, CoalgCat.toMonObj_mul, unop_comp, unop_tensorHom, Quiver.Hom.unop_op,
    BraidedCategory.unop_tensor_μ, ModuleCat.MonoidalCategory.tensor_μ_eq_tensorTensorTensorComm,
    tensorProductCoalgebraStruct_comul]
  rfl

lemma tensorObj_counit_eq :
    Coalgebra.counit (R := R) (A := (tensorObj (CoalgCat.of R M) (CoalgCat.of R N) : CoalgCat R))
      = Coalgebra.counit (R := R) (A := M ⊗[R] N) := by
  rfl

lemma tensorObj_counit_eq' :
    Coalgebra.counit (R := R) (A := (tensorObj (CoalgCat.of R M)
      (tensorObj (CoalgCat.of R N) (CoalgCat.of R P)) : CoalgCat R))
      = Coalgebra.counit (R := R) (A := M ⊗[R] (N ⊗[R] P)) := by
  ext; rfl

lemma tensorObj_counit_eq'' :
    Coalgebra.counit (R := R) (A := (tensorObj (tensorObj (CoalgCat.of R M)
      (CoalgCat.of R N)) (CoalgCat.of R P) : CoalgCat R))
      = Coalgebra.counit (R := R) (A := (M ⊗[R] N) ⊗[R] P) := by
  ext; rfl

end CoalgCat.MonoidalCategoryAux
namespace Coalgebra

open CategoryTheory CoalgCat.MonoidalCategoryAux
open scoped TensorProduct

variable {R M N P Q : Type u} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [Module R M] [Module R N]
  [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N] [Coalgebra R P] [Coalgebra R Q]

set_option profiler true

open scoped MonoidalCategory in
@[simps! toLinearMap] noncomputable def TensorProduct.map (f : M →c[R] N) (g : P →c[R] Q) :
    M ⊗[R] P →c[R] N ⊗[R] Q :=
  let I := CoalgCat.instMonoidalCategoryAux (R := R)
  { _root_.TensorProduct.map f.toLinearMap g.toLinearMap with
    counit_comp := by
      simp_rw [← tensorHom_toLinearMap, ← tensorObj_counit_eq]
      apply (CoalgCat.ofHom f ⊗ CoalgCat.ofHom g).counit_comp
    map_comp_comul := by
      simp_rw [← tensorHom_toLinearMap, ← tensorObj_comul_eq]
      apply (CoalgCat.ofHom f ⊗ CoalgCat.ofHom g).map_comp_comul }

variable (M)

noncomputable abbrev lTensor (f : N →c[R] P) : M ⊗[R] N →c[R] M ⊗[R] P :=
  TensorProduct.map (CoalgHom.id R M) f

noncomputable abbrev rTensor (f : N →c[R] P) : N ⊗[R] M →c[R] P ⊗[R] M :=
  TensorProduct.map f (CoalgHom.id R M)

variable (R N P)

/- get innnnn -/
open scoped MonoidalCategory in
@[simps! toCoalgHom] noncomputable def TensorProduct.assoc :
    (M ⊗[R] N) ⊗[R] P ≃c[R] M ⊗[R] (N ⊗[R] P) :=
  let I := CoalgCat.instMonoidalCategoryAux (R := R)
  { _root_.TensorProduct.assoc R M N P with
    counit_comp := by
      dsimp only
      rw [← associator_hom_toLinearMap, ← tensorObj_counit_eq', ← tensorObj_counit_eq'']
      apply CoalgHom.counit_comp (α_ (CoalgCat.of R M) (CoalgCat.of R N) (CoalgCat.of R P)).hom
    map_comp_comul := by
      dsimp only
      simp_rw [← associator_hom_toLinearMap, ← tensorObj_comul_eq', ← tensorObj_comul_eq'']
      exact CoalgHom.map_comp_comul (α_ (CoalgCat.of R M) (CoalgCat.of R N) (CoalgCat.of R P)).hom }

open scoped MonoidalCategory in
@[simps! toCoalgHom] noncomputable def TensorProduct.lid : R ⊗[R] M ≃c[R] M :=
  let I := CoalgCat.instMonoidalCategoryAux (R := R)
  { _root_.TensorProduct.lid R M with
    counit_comp := by
      simp only [← leftUnitor_hom_toLinearMap, ← tensorObj_counit_eq]
      apply CoalgHom.counit_comp (λ_ (CoalgCat.of R M)).hom
    map_comp_comul := by
      simp_rw [← leftUnitor_hom_toLinearMap, ← tensorObj_comul_eq]
      apply CoalgHom.map_comp_comul (λ_ (CoalgCat.of R M)).hom }

open scoped MonoidalCategory in
@[simps! toCoalgHom] noncomputable def TensorProduct.rid : M ⊗[R] R ≃c[R] M :=
  let I := CoalgCat.instMonoidalCategoryAux (R := R)
  { _root_.TensorProduct.rid R M with
    counit_comp := by
      simp only [← rightUnitor_hom_toLinearMap, ← tensorObj_counit_eq]
      apply CoalgHom.counit_comp (ρ_ (CoalgCat.of R M)).hom
    map_comp_comul := by
      simp_rw [← rightUnitor_hom_toLinearMap, ← tensorObj_comul_eq]
      apply CoalgHom.map_comp_comul (ρ_ (CoalgCat.of R M)).hom }

end Coalgebra

namespace CoalgCat
variable (R : Type u) [CommRing R]
open CategoryTheory Coalgebra
open scoped TensorProduct MonoidalCategory

@[simps] noncomputable instance : MonoidalCategoryStruct.{u} (CoalgCat R) where
  tensorObj := fun X Y => CoalgCat.of R (X ⊗[R] Y)
  whiskerLeft := fun X _ _ f => CoalgCat.ofHom (lTensor X f)
  whiskerRight := fun f X => CoalgCat.ofHom (rTensor X f)
  tensorHom := fun f g => CoalgCat.ofHom (Coalgebra.TensorProduct.map f g)
  tensorUnit := CoalgCat.of R R
  associator := fun X Y Z => (Coalgebra.TensorProduct.assoc R X Y Z).toCoalgIso
  leftUnitor := fun X => (Coalgebra.TensorProduct.lid R X).toCoalgIso
  rightUnitor := fun X => (Coalgebra.TensorProduct.rid R X).toCoalgIso

set_option profiler true

@[simps] noncomputable def inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (CoalgCat R) (ModuleCat R)) where
  μIso := fun X Y => Iso.refl _
  whiskerLeft_eq := fun X Y Z f => by ext; rfl
  whiskerRight_eq := fun X f => by ext; rfl
  tensorHom_eq := fun f g => by ext; rfl
  εIso := Iso.refl _
  associator_eq := fun X Y Z => TensorProduct.ext <| TensorProduct.ext <| by ext; rfl
  leftUnitor_eq := fun X => TensorProduct.ext <| by ext; rfl
  rightUnitor_eq := fun X => TensorProduct.ext <| by ext; rfl

noncomputable instance : MonoidalCategory (CoalgCat R) :=
  Monoidal.induced (forget₂ _ (ModuleCat R)) (inducingFunctorData R)

end CoalgCat
