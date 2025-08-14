/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Action of the general linear group on projectivization

Show that the general linear group of `V` acts on `ℙ K V`.
-/

open scoped LinearAlgebra.Projectivization MatrixGroups Matrix

section Preliminaries

variable {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]

instance : DistribMulAction (Matrix n n R) (n → R) :=
  .compHom _ Matrix.toLinAlgEquiv'.toMonoidHom

instance : SMulCommClass (Matrix n n R) R (n → R) :=
  SMul.comp.smulCommClass (Matrix.toLinAlgEquiv'.toMonoidHom : _ →* (Module.End R (n → R)))

instance : DistribMulAction (Matrix (Fin 2) (Fin 2) R) (R × R) :=
  (LinearEquiv.finTwoArrow R R).symm.distribMulAction _

instance : SMulCommClass (Matrix (Fin 2) (Fin 2) R) R (R × R) :=
  (LinearEquiv.finTwoArrow R R).symm.smulCommClass _ _

lemma smul_eq_mulVec (g : Matrix n n R) (v : n → R) : g • v = g *ᵥ v := rfl

end Preliminaries

namespace Projectivization

section DivisionRing

variable {α K V : Type*} [AddCommGroup V] [DivisionRing K] [Module K V]
  [Group α] [DistribMulAction α V] [SMulCommClass α K V]

/-- Any group acting `K`-linearly on `V` (such as the general linear group) acts on `ℙ V`. -/
instance : MulAction α (ℙ K V) where
  smul g x := x.map (DistribMulAction.toModuleEnd _ _ g)
    (DistribMulAction.toLinearEquiv _ _ g).injective
  one_smul x := show map _ _ _ = _ by simp [map_one, Module.End.one_eq_id]
  mul_smul g g' x := show map _ _ _ = map _ _ (map _ _ _) by
    simp_rw [map_mul, Module.End.mul_eq_comp]
    rw [map_comp, Function.comp_apply]

lemma smul_def (g : LinearMap.GeneralLinearGroup K V) (x : ℙ K V) :
    g • x = x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective := by
  rfl

@[simp]
lemma smul_mk (g : α) {v : V} (hv : v ≠ 0) :
    g • mk K _ hv = mk K _ ((smul_ne_zero_iff_ne g).mpr hv) :=
  rfl

end DivisionRing

section Field

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

@[simp]
lemma pi_smul_mk (g : GL n K) {v : n → K} (hv : v ≠ 0) :
    g • mk K v hv = mk K (g.val *ᵥ v) (g.toLin.toLinearEquiv.map_ne_zero_iff.mpr hv) := by
  rfl

private lemma finTwoProdSMul_ne_zero {v : K × K} (hv : v ≠ 0) (g : GL (Fin 2) K) :
    (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2) ≠ 0 := by
  rw [← (LinearEquiv.finTwoArrow K K).symm.map_ne_zero_iff] at hv ⊢
  convert g.toLin.toLinearEquiv.map_ne_zero_iff.mpr hv using 1
  ext i
  fin_cases i <;>
  simp [Matrix.mulVec_eq_sum, mul_comm]

@[simp]
lemma prod_smul_mk (g : GL (Fin 2) K) {v : K × K} (hv : v ≠ 0) :
    g • mk K v hv = mk K _ (finTwoProdSMul_ne_zero hv g) := by
  simp [Equiv.smul_def, Units.smul_def, smul_eq_mulVec, Matrix.mulVec_eq_sum, mul_comm]

end Field

end Projectivization
