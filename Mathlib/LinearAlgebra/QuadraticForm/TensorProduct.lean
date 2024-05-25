/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The quadratic form on a tensor product

## Main definitions

* `QuadraticForm.tensorDistrib (Q₁ ⊗ₜ Q₂)`: the quadratic form on `M₁ ⊗ M₂` constructed by applying
  `Q₁` on `M₁` and `Q₂` on `M₂`. This construction is not available in characteristic two.

-/

universe uR uA uM₁ uM₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂}

open TensorProduct
open LinearMap (BilinForm)

namespace QuadraticForm

section CommRing
variable [CommRing R] [CommRing A]
variable [AddCommGroup M₁] [AddCommGroup M₂]
variable [Algebra R A] [Module R M₁] [Module A M₁]
variable [SMulCommClass R A M₁] [SMulCommClass A R M₁] [IsScalarTower R A M₁]
variable [Module R M₂] [Invertible (2 : R)]


variable (R A) in
/-- The tensor product of two quadratic forms injects into quadratic forms on tensor products.

Note this is heterobasic; the quadratic form on the left can take values in a larger ring than
the one on the right. -/
-- `noncomputable` is a performance workaround for mathlib4#7103
noncomputable def tensorDistrib :
    QuadraticForm A M₁ ⊗[R] QuadraticForm R M₂ →ₗ[A] QuadraticForm A (M₁ ⊗[R] M₂) :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  -- while `letI`s would produce a better term than `let`, they would make this already-slow
  -- definition even slower.
  let toQ := BilinForm.toQuadraticFormLinearMap A A (M₁ ⊗[R] M₂)
  let tmulB := BilinForm.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
  let toB := AlgebraTensorModule.map
      (QuadraticForm.associated : QuadraticForm A M₁ →ₗ[A] BilinForm A M₁)
      (QuadraticForm.associated : QuadraticForm R M₂ →ₗ[R] BilinForm R M₂)
  toQ ∘ₗ tmulB ∘ₗ toB

-- TODO: make the RHS `MulOpposite.op (Q₂ m₂) • Q₁ m₁` so that this has a nicer defeq for
-- `R = A` of `Q₁ m₁ * Q₂ m₂`.
@[simp]
theorem tensorDistrib_tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂) :
    tensorDistrib R A (Q₁ ⊗ₜ Q₂) (m₁ ⊗ₜ m₂) = Q₂ m₂ • Q₁ m₁ :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  (BilinForm.tensorDistrib_tmul _ _ _ _ _ _).trans <| congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

/-- The tensor product of two quadratic forms, a shorthand for dot notation. -/
-- `noncomputable` is a performance workaround for mathlib4#7103
protected noncomputable abbrev tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    QuadraticForm A (M₁ ⊗[R] M₂) :=
  tensorDistrib R A (Q₁ ⊗ₜ[R] Q₂)

theorem associated_tmul [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    associated (R := A) (Q₁.tmul Q₂)
      = (associated (R := A) Q₁).tmul (associated (R := R) Q₂) := by
  rw [QuadraticForm.tmul, tensorDistrib, BilinForm.tmul]
  dsimp
  have : Subsingleton (Invertible (2 : A)) := inferInstance
  convert associated_left_inverse A ((associated_isSymm A Q₁).tmul (associated_isSymm R Q₂))

theorem polarBilin_tmul [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    polarBilin (Q₁.tmul Q₂) = ⅟(2 : A) • (polarBilin Q₁).tmul (polarBilin Q₂) := by
  simp_rw [← two_nsmul_associated A, ← two_nsmul_associated R, BilinForm.tmul, tmul_smul,
    ← smul_tmul', map_nsmul, associated_tmul]
  rw [smul_comm (_ : A) (_ : ℕ), ← smul_assoc, two_smul _ (_ : A), invOf_two_add_invOf_two,
    one_smul]

variable (A) in
/-- The base change of a quadratic form. -/
-- `noncomputable` is a performance workaround for mathlib4#7103
protected noncomputable def baseChange (Q : QuadraticForm R M₂) : QuadraticForm A (A ⊗[R] M₂) :=
  QuadraticForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (QuadraticForm.sq (R := A)) Q

@[simp]
theorem baseChange_tmul (Q : QuadraticForm R M₂) (a : A) (m₂ : M₂) :
    Q.baseChange A (a ⊗ₜ m₂) = Q m₂ • (a * a) :=
  tensorDistrib_tmul _ _ _ _

theorem associated_baseChange [Invertible (2 : A)] (Q : QuadraticForm R M₂) :
    associated (R := A) (Q.baseChange A) = (associated (R := R) Q).baseChange A := by
  dsimp only [QuadraticForm.baseChange, LinearMap.baseChange]
  rw [associated_tmul (QuadraticForm.sq (R := A)) Q, associated_sq]
  exact rfl

theorem polarBilin_baseChange [Invertible (2 : A)] (Q : QuadraticForm R M₂) :
    polarBilin (Q.baseChange A) = (polarBilin Q).baseChange A := by
  rw [QuadraticForm.baseChange, BilinForm.baseChange, polarBilin_tmul, BilinForm.tmul,
    ← LinearMap.map_smul, smul_tmul', ← two_nsmul_associated R, coe_associatedHom, associated_sq,
    smul_comm, ← smul_assoc, two_smul, invOf_two_add_invOf_two, one_smul]

end CommRing

end QuadraticForm
