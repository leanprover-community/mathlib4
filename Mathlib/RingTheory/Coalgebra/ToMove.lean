import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.RingTheory.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
universe v u
namespace CategoryTheory.MonoidalFunctor
open CategoryTheory.MonoidalCategory

@[simps] noncomputable def op
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : MonoidalFunctor C D) : MonoidalFunctor Cᵒᵖ Dᵒᵖ :=
  { F.toFunctor.op with
    ε := (inv F.ε).op
    μ := fun X Y => (inv (F.μ X.unop Y.unop)).op
    μ_natural_left := fun f Z => by
      dsimp
      simp only [op_inv, op_tensorObj, IsIso.eq_inv_comp,
        ← Category.assoc, IsIso.comp_inv_eq, ← op_id, ← op_tensorHom, ← op_comp,
        F.μ_natural_left]
    μ_natural_right := fun Z f => by
      dsimp
      simp only [op_inv, op_tensorObj, IsIso.eq_inv_comp,
        ← Category.assoc, IsIso.comp_inv_eq, ← op_id, ← op_tensorHom, ← op_comp,
        F.μ_natural_right]
    associativity := fun X Y Z => by
      dsimp
      rw [← IsIso.inv_id]
      simp only [← op_inv_associator, ← op_id, ← op_inv, ← op_tensorHom, ← op_comp,
        ← inv_tensor, ← IsIso.Iso.inv_hom, Functor.map_inv, ← IsIso.inv_comp,
        ← IsIso.inv_comp, Category.assoc, F.1.associativity]
      simp only [IsIso.inv_comp, inv_tensor, IsIso.inv_id, IsIso.Iso.inv_hom, Category.assoc]
    left_unitality := fun X => by
      dsimp
      rw [← IsIso.inv_id]
      simp only [← op_id, ← op_inv, ← op_tensorHom, ← inv_tensor, ← op_comp, ← IsIso.Iso.inv_hom,
        Functor.map_inv, ← IsIso.inv_comp, ← F.1.left_unitality, ← op_inv_leftUnitor]
    right_unitality := fun X => by
      dsimp
      rw [← IsIso.inv_id]
      simp only [← op_id, ← op_inv, ← op_tensorHom, ← inv_tensor, ← op_comp, ← IsIso.Iso.inv_hom,
        Functor.map_inv, ← IsIso.inv_comp, ← F.1.right_unitality, ← op_inv_rightUnitor]
    ε_isIso := by infer_instance
    μ_isIso := by infer_instance }

end CategoryTheory.MonoidalFunctor
namespace CategoryTheory.BraidedCategory

open Opposite

@[simp] lemma unop_tensor_μ {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (X Y W Z : Cᵒᵖ) :
    (tensor_μ Cᵒᵖ (X, W) (Y, Z)).unop = tensor_μ C (X.unop, Y.unop) (W.unop, Z.unop) := by
  simp only [unop_tensorObj, tensor_μ, unop_comp, unop_inv_associator, unop_whiskerLeft,
    unop_hom_associator, unop_whiskerRight, unop_hom_braiding, Category.assoc]

@[simp] lemma op_tensor_μ {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (X Y W Z : C) :
    (tensor_μ C (X, W) (Y, Z)).op = tensor_μ Cᵒᵖ (op X, op Y) (op W, op Z) := by
  simp only [op_tensorObj, tensor_μ, op_comp, op_inv_associator, op_whiskerLeft, op_hom_associator,
    op_whiskerRight, op_hom_braiding, Category.assoc]

end CategoryTheory.BraidedCategory
namespace ModuleCat.MonoidalCategory
open CategoryTheory BraidedCategory

@[simp] lemma tensor_μ_eq_tensorTensorTensorComm {R : Type u} [CommRing R] {A B C D : ModuleCat R} :
    tensor_μ _ (A, B) (C, D) = (TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap :=
  TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext₂ fun _ _ =>
    TensorProduct.ext <| LinearMap.ext₂ fun _ _ => rfl

end ModuleCat.MonoidalCategory
namespace Algebra.TensorProduct
open scoped TensorProduct

variable {R A B C D : Type*}
  [CommSemiring R] [Semiring A] [Algebra R A]
  [Semiring B] [Algebra R B] [Semiring C] [Algebra R C] [Semiring D]
  [Algebra R D]

lemma map_toLinearMap (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    (map f g).toLinearMap = _root_.TensorProduct.map f.toLinearMap g.toLinearMap := rfl

-- need more than just this
lemma tensorTensorTensorComm_toLinearMap :
    (tensorTensorTensorComm R A B C D).toLinearMap
      = (_root_.TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap := rfl

variable (R A)

lemma rid_toLinearMap :
    (Algebra.TensorProduct.rid R R A).toLinearMap
      = (_root_.TensorProduct.rid R A).toLinearMap := by
  ext
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgEquiv.toLinearMap_apply, rid_tmul, one_smul,
    LinearEquiv.coe_coe, _root_.TensorProduct.rid_tmul]

end Algebra.TensorProduct
namespace TensorProduct.AlgebraTensorModule

open CategoryTheory TensorProduct MonoidalCategory
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module R M] [Module R N] [Module R P] [Module R Q]

noncomputable abbrev ε := (AlgebraTensorModule.rid R S S).symm.toLinearMap
variable {R} (M N)

noncomputable abbrev μ := (AlgebraTensorModule.cancelBaseChange R S S (S ⊗[R] M) N
  ≪≫ₗ AlgebraTensorModule.assoc R R S S M N).toLinearMap

noncomputable abbrev μ' [Module S M] [Module S N] [IsScalarTower R S M] [IsScalarTower R S N] :
    M ⊗[R] N →ₗ[R] M ⊗[S] N :=
  TensorProduct.lift (LinearMap.restrictScalars₁₂ R (TensorProduct.mk S M N))

variable {N}

lemma μ_natural_left  (f : N →ₗ[R] P) :
    μ S P M  ∘ₗ TensorProduct.map (LinearMap.baseChange S f)
      (LinearMap.baseChange S (LinearMap.id (M := M)))
      = LinearMap.baseChange S (TensorProduct.map f LinearMap.id)
      ∘ₗ μ S N M := by
  ext
  simp only [curry_apply, TensorProduct.curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.map_tmul,
    LinearMap.baseChange_tmul, LinearMap.id_coe, id_eq, LinearEquiv.trans_apply,
    cancelBaseChange_tmul, one_smul, assoc_tmul]

variable {M}

lemma μ_natural (f : M →ₗ[R] N) (g : P →ₗ[R] Q) :
    μ S N Q ∘ₗ TensorProduct.map (LinearMap.baseChange S f) (LinearMap.baseChange S g)
      = LinearMap.baseChange S (TensorProduct.map f g) ∘ₗ μ S M P := by
  ext
  simp only [curry_apply, TensorProduct.curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.map_tmul,
    LinearMap.baseChange_tmul, LinearEquiv.trans_apply, cancelBaseChange_tmul, one_smul, assoc_tmul]

variable (M N P)

lemma associativity :
  LinearMap.baseChange S (TensorProduct.assoc R M N P).toLinearMap
    ∘ₗ μ S (M ⊗[R] N) P
    ∘ₗ TensorProduct.map (μ S M N) LinearMap.id
    = μ S M (N ⊗[R] P) ∘ₗ TensorProduct.map LinearMap.id (μ S N P)
    ∘ₗ (TensorProduct.assoc S (S ⊗[R] M) (S ⊗[R] N) (S ⊗[R] P)).toLinearMap := by
  ext
  simp only [curry_apply, TensorProduct.curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.trans_apply, cancelBaseChange_tmul, one_smul, assoc_tmul, LinearMap.id_coe, id_eq,
    LinearMap.baseChange_tmul, TensorProduct.assoc_tmul]

variable {N P}

lemma left_unitality :
    (TensorProduct.lid S (S ⊗[R] M)).toLinearMap
      = LinearMap.baseChange S (TensorProduct.lid R M).toLinearMap
      ∘ₗ μ S R M ∘ₗ TensorProduct.map (ε R S) LinearMap.id := by
  ext
  simp only [curry_apply, TensorProduct.curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe, lid_tmul,
    LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul, rid_symm_apply,
    LinearMap.id_coe, id_eq, LinearEquiv.trans_apply, cancelBaseChange_tmul,
    one_smul, assoc_tmul, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, lid_tmul]

lemma right_unitality :
    (TensorProduct.rid S (S ⊗[R] M)).toLinearMap
      = LinearMap.baseChange S (TensorProduct.rid R M).toLinearMap
      ∘ₗ μ S M R ∘ₗ TensorProduct.map LinearMap.id (ε R S) := by
  ext
  simp only [curry_apply, TensorProduct.curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul, LinearMap.coe_comp, Function.comp_apply,
    TensorProduct.map_tmul, LinearMap.id_coe, id_eq, rid_symm_apply, LinearEquiv.trans_apply,
    cancelBaseChange_tmul, one_smul, assoc_tmul, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul]

end TensorProduct.AlgebraTensorModule
namespace ModuleCat

open CategoryTheory MonoidalCategory TensorProduct
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
set_option profiler true

set_option maxHeartbeats 800000

/- woohoo over 40 seconds. what the hell -/
noncomputable def extendScalarsLaxMonoidal : LaxMonoidalFunctor (ModuleCat R) (ModuleCat S) := by
  let I := f.toAlgebra
  refine' LaxMonoidalFunctor.ofTensorHom (extendScalars f)
    (ModuleCat.ofHom (AlgebraTensorModule.rid R S S).symm.toLinearMap)
    (fun X Y => _) _ _ _ _
  · apply ModuleCat.ofHom (AlgebraTensorModule.cancelBaseChange R S S (S ⊗[R] X) Y
      ≪≫ₗ AlgebraTensorModule.assoc R R S S X Y).toLinearMap
  · intros
    apply AlgebraTensorModule.μ_natural S _ _
  · intros
    apply AlgebraTensorModule.associativity S _ _ _
  · intros
    apply AlgebraTensorModule.left_unitality S _
  · intros
    apply AlgebraTensorModule.right_unitality S _

@[simp] lemma extendScalarsLaxMonoidal_toFunctor :
    (extendScalarsLaxMonoidal f).toFunctor = extendScalars f := rfl

@[simps! toLaxMonoidalFunctor] noncomputable def extendScalarsMonoidal :
    MonoidalFunctor (ModuleCat R) (ModuleCat S) :=
  { extendScalarsLaxMonoidal f with
    ε_isIso := IsIso.of_iso (LinearEquiv.toModuleIso _)
    μ_isIso := fun X Y => by convert IsIso.of_iso (LinearEquiv.toModuleIso _) }

end ModuleCat
