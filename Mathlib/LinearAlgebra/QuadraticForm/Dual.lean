/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Dual

#align_import linear_algebra.quadratic_form.dual from "leanprover-community/mathlib"@"d11f435d4e34a6cea0a1797d6b625b0c170be845"

/-!
# Quadratic form structures related to `Module.Dual`

## Main definitions

* `LinearMap.dualProd R M`, the bilinear form on `(f, x) : Module.Dual R M × M` defined as
  `f x`.
* `QuadraticForm.dualProd R M`, the quadratic form on `(f, x) : Module.Dual R M × M` defined as
  `f x`.
* `QuadraticForm.toDualProd : (Q.prod <| -Q) →qᵢ QuadraticForm.dualProd R M` a form-preserving map
  from `(Q.prod <| -Q)` to `QuadraticForm.dualProd R M`.

-/


variable (R M N : Type*)

namespace LinearMap

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The symmetric bilinear form on `Module.Dual R M × M` defined as
`B (f, x) (g, y) = f y + g x`. -/
@[simps!]
def dualProd : LinearMap.BilinForm R (Module.Dual R M × M) :=
    (applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M) +
      ((applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M)).flip
#align bilin_form.dual_prod LinearMap.dualProd

theorem isSymm_dualProd : (dualProd R M).IsSymm := fun _x _y => add_comm _ _
#align bilin_form.is_symm_dual_prod LinearMap.isSymm_dualProd

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]

theorem separatingLeft_dualProd :
    (dualProd R M).SeparatingLeft ↔ Function.Injective (Module.Dual.eval R M) := by
  classical
  rw [separatingLeft_iff_ker_eq_bot, ker_eq_bot]
  let e := LinearEquiv.prodComm R _ _ ≪≫ₗ Module.dualProdDualEquivDual R (Module.Dual R M) M
  let h_d := e.symm.toLinearMap.comp (dualProd R M)
  refine (Function.Injective.of_comp_iff e.symm.injective
    (dualProd R M)).symm.trans ?_
  rw [← LinearEquiv.coe_toLinearMap, ← coe_comp]
  change Function.Injective h_d ↔ _
  have : h_d = prodMap id (Module.Dual.eval R M) := by
    refine ext fun x => Prod.ext ?_ ?_
    · ext
      dsimp [e, h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp
    · ext
      dsimp [e, h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp
  rw [this, coe_prodMap]
  refine Prod.map_injective.trans ?_
  exact and_iff_right Function.injective_id
#align bilin_form.nondenerate_dual_prod LinearMap.separatingLeft_dualProd

end Ring

end LinearMap

namespace QuadraticForm

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- The quadratic form on `Module.Dual R M × M` defined as `Q (f, x) = f x`. -/
@[simps]
def dualProd : QuadraticForm R (Module.Dual R M × M) where
  toFun p := p.1 p.2
  toFun_smul a p := by
    dsimp only  -- Porting note: added
    rw [Prod.smul_fst, Prod.smul_snd, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul,
      smul_eq_mul, mul_assoc]
  exists_companion' :=
    ⟨LinearMap.dualProd R M, fun p q => by
      dsimp only  -- Porting note: added
      rw [LinearMap.dualProd_apply_apply, Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add,
        map_add, add_right_comm _ (q.1 q.2), add_comm (q.1 p.2) (p.1 q.2), ← add_assoc, ←
        add_assoc]⟩
#align quadratic_form.dual_prod QuadraticForm.dualProd

@[simp]
theorem _root_.LinearMap.dualProd.toQuadraticForm :
    (LinearMap.dualProd R M).toQuadraticForm = 2 • dualProd R M :=
  ext fun _a => (two_nsmul _).symm
#align bilin_form.dual_prod.to_quadratic_form LinearMap.dualProd.toQuadraticForm

variable {R M N}

/-- Any module isomorphism induces a quadratic isomorphism between the corresponding `dual_prod.` -/
@[simps!]
def dualProdIsometry (f : M ≃ₗ[R] N) : (dualProd R M).IsometryEquiv (dualProd R N) where
  toLinearEquiv := f.dualMap.symm.prod f
  map_app' x := DFunLike.congr_arg x.fst <| f.symm_apply_apply _
#align quadratic_form.dual_prod_isometry QuadraticForm.dualProdIsometry

/-- `QuadraticForm.dualProd` commutes (isometrically) with `QuadraticForm.prod`. -/
@[simps!]
def dualProdProdIsometry :
    (dualProd R (M × N)).IsometryEquiv ((dualProd R M).prod (dualProd R N)) where
  toLinearEquiv :=
    (Module.dualProdDualEquivDual R M N).symm.prod (LinearEquiv.refl R (M × N)) ≪≫ₗ
      LinearEquiv.prodProdProdComm R _ _ M N
  map_app' m :=
    (m.fst.map_add _ _).symm.trans <| DFunLike.congr_arg m.fst <| Prod.ext (add_zero _) (zero_add _)
#align quadratic_form.dual_prod_prod_isometry QuadraticForm.dualProdProdIsometry

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]
variable {R M}

/-- The isometry sending `(Q.prod <| -Q)` to `(QuadraticForm.dualProd R M)`.

This is `σ` from Proposition 4.8, page 84 of
[*Hermitian K-Theory and Geometric Applications*][hyman1973]; though we swap the order of the pairs.
-/
@[simps!]
def toDualProd (Q : QuadraticForm R M) [Invertible (2 : R)] :
    (Q.prod <| -Q) →qᵢ QuadraticForm.dualProd R M where
  toLinearMap := LinearMap.prod
    (Q.associated.comp (LinearMap.fst _ _ _) + Q.associated.comp (LinearMap.snd _ _ _))
    (LinearMap.fst _ _ _ - LinearMap.snd _ _ _)
  map_app' x := by
    dsimp only [associated, associatedHom]
    dsimp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearMap.prod_apply, Pi.prod, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.sub_apply, dualProd_apply, polarBilin_apply_apply, prod_apply, neg_apply]
    simp [polar_comm _ x.1 x.2, ← sub_add, mul_sub, sub_mul, smul_sub, Submonoid.smul_def, ←
      sub_eq_add_neg (Q x.1) (Q x.2)]
#align quadratic_form.to_dual_prod QuadraticForm.toDualProdₓ

#align quadratic_form.to_dual_prod_isometry QuadraticForm.Isometry.map_appₓ

/-!
TODO: show that `QuadraticForm.toDualProd` is an `QuadraticForm.IsometryEquiv`
-/

end Ring

end QuadraticForm
