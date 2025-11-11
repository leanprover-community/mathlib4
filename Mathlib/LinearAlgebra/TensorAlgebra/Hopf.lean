import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Algebra.Algebra.Bilinear

namespace TensorAlgebra
open scoped TensorProduct

variable (R : Type*) [CommRing R] {M : Type*} [AddCommMonoid M] [Module R M]

local notation "T["M"]" => TensorAlgebra R M

/-- Counit in `TensorAlgebra R M`. -/
abbrev ε := @algebraMapInv R _ M _ _

/-- Linear map inducing the comultiplication in `TensorAlgebra R M`. -/
def comul' : M →ₗ[R] T[M] ⊗[R] T[M] :=
  TensorProduct.map (ι R) (Algebra.linearMap R T[M]) ∘ₗ (TensorProduct.rid R M).symm +
  TensorProduct.map (Algebra.linearMap R T[M]) (ι R) ∘ₗ (TensorProduct.lid R M).symm

/-- Comultiplication in `TensorAlgebra R M` as an algebra map. -/
def comul : T[M] →ₐ[R] T[M] ⊗[R] T[M] := lift R (comul' R)

/-- Antipode in `TensorAlgebra R M` as an algebra map. -/
def antipode : T[M] →ₗ[R] T[M] := (MulOpposite.opLinearEquiv R).symm.comp
  (lift R ((MulOpposite.opLinearEquiv R).comp (-(ι R)))).toLinearMap

@[simp]
lemma comul_apply' (x : M) : comul' R x = ι R x ⊗ₜ[R] ↑1 + ↑1 ⊗ₜ[R] ι R x := by
  unfold comul'
  simp

@[simp]
lemma counit_ι_apply (x : M) : (ε R) ((ι R) x) = 0 := by
  unfold ε 
  rw [algebraMapInv]
  simp

@[simp]
lemma counit_ι_eq_zero : (ε R).toLinearMap ∘ₗ (ι R) = (0 : M →ₗ[R] R) := by
  ext x
  simp

theorem rTensor : (Algebra.TensorProduct.map (ε R) (AlgHom.id R T[M])).comp (comul R) =
    (Algebra.TensorProduct.lid R T[M]).symm.toAlgHom := by
  unfold ε comul comul'
  ext x
  rw [algebraMapInv]
  simp

theorem lTensor : (Algebra.TensorProduct.map (AlgHom.id R T[M]) (ε R)).comp (comul R) =
    ↑(Algebra.TensorProduct.rid R R T[M]).symm := by
  unfold ε comul comul'
  ext x
  rw [algebraMapInv]
  simp

@[simp]
lemma antipode_ι_apply (x : M) : antipode R ((ι R) x) = -(ι R) x := by
  unfold antipode
  simp

@[simp]
lemma antipode_one (r : R) : antipode R (algebraMap R T[M] r) = algebraMap R T[M] r := by
  unfold antipode
  simp

theorem coassoc : (Algebra.TensorProduct.assoc R R T[M] T[M] T[M]).toAlgHom.comp 
    ((Algebra.TensorProduct.map (comul R) (AlgHom.id R T[M])).comp (comul R)) =
    (Algebra.TensorProduct.map (AlgHom.id R T[M]) (comul R)).comp (comul R) := by
  unfold comul comul'
  ext
  /- can be reduced maybe? -/
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, AlgHom.coe_toLinearMap,
  Function.comp_apply, lift_ι_apply, LinearMap.add_apply, LinearEquiv.coe_coe,
  TensorProduct.rid_symm_apply, TensorProduct.map_tmul, Algebra.linearMap_apply, map_one,
  TensorProduct.lid_symm_apply, map_add, Algebra.TensorProduct.map_tmul, TensorProduct.tmul_add]
  abel

instance instBialgebra : Bialgebra R T[M] :=
  Bialgebra.ofAlgHom (comul R) (ε R) (coassoc R) (rTensor R) (lTensor R)

instance : HopfAlgebraStruct R T[M] where
  antipode := antipode R

@[simp]
theorem antipode_antihom_apply (x y : T[M]) : antipode R (x * y) = antipode R y * antipode R x := by
  unfold antipode
  simp

@[simp]
theorem antipode_antihom : antipode R ∘ₗ LinearMap.mul' R T[M] =
    LinearMap.mul' R T[M] ∘ₗ TensorProduct.comm R T[M] T[M] ∘ₗ TensorProduct.map (antipode R)
    (antipode R) := by
  ext x y
  simp

end TensorAlgebra
