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

namespace Projectivization

section DivisionRing

variable {K V : Type*} [AddCommGroup V] [DivisionRing K] [Module K V]

/-- The general linear group of `V` acts on `ℙ V`, via its action on `V`. -/
instance instGLAction : MulAction (LinearMap.GeneralLinearGroup K V) (ℙ K V) where
  smul g x := x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective
  one_smul := congr_fun Projectivization.map_id
  mul_smul g g' x := congr_fun (Projectivization.map_comp
    g'.toLinearEquiv.toLinearMap _ g.toLinearEquiv.toLinearMap _ _) x

lemma smul_def
    (g : LinearMap.GeneralLinearGroup K V) (x : ℙ K V) :
    g • x = x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective := by
  rfl

@[simp]
lemma smul_mk (g : LinearMap.GeneralLinearGroup K V) {v : V} (hv : v ≠ 0) :
    g • Projectivization.mk K v hv =
      Projectivization.mk K (g • v) ((smul_ne_zero_iff_ne _).mpr hv) := by
  rfl

end DivisionRing

section Field

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- For a field `K`, the group `GL n K` acts on `ℙ K (n → K)`. -/
instance instGLFinAction : MulAction (GL n K) (ℙ K (n → K)) :=
  .compHom _ Matrix.GeneralLinearGroup.toLin.toMonoidHom

@[simp]
lemma pi_smul_mk (g : GL n K) {v : n → K} (hv : v ≠ 0) :
    g • mk K v hv = mk K (g.val *ᵥ v) (g.toLin.toLinearEquiv.map_ne_zero_iff.mpr hv) := by
  rfl

/-- For a field `K`, the group `GL (Fin 2) K` acts on `ℙ K (K × K)`, via identifying `K × K` with
column vectors. -/
instance instGLFinTwoAction : MulAction (GL (Fin 2) K) (ℙ K (K × K)) :=
  .compHom _ (Matrix.GeneralLinearGroup.toLin.trans
    <| LinearMap.GeneralLinearGroup.compLinearEquiv <| LinearEquiv.finTwoArrow K K).toMonoidHom

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
  simp [MulAction.compHom_smul_def, LinearMap.GeneralLinearGroup.ofLinearEquiv,
    Matrix.mulVec_eq_sum, mul_comm]

end Field

end Projectivization
