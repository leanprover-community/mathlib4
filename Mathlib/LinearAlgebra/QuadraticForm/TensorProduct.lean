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

universe uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

open LinearMap (BilinMap BilinForm)
open TensorProduct QuadraticMap

section CommRing
variable [CommRing R] [CommRing A]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]
variable [SMulCommClass R A M₁] [IsScalarTower R A M₁] [IsScalarTower R A N₁]
variable [Module R M₂] [Module R N₂]

section InvertibleTwo
variable [Invertible (2 : R)]

namespace QuadraticMap

variable (R A) in
/-- The tensor product of two quadratic maps injects into quadratic maps on tensor products.

Note this is heterobasic; the quadratic map on the left can take values in a module over a larger
ring than the one on the right. -/
-- `noncomputable` is a performance workaround for https://github.com/leanprover-community/mathlib4/issues/7103
noncomputable def tensorDistrib :
    QuadraticMap A M₁ N₁ ⊗[R] QuadraticMap R M₂ N₂ →ₗ[A] QuadraticMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  -- while `letI`s would produce a better term than `let`, they would make this already-slow
  -- definition even slower.
  let toQ := BilinMap.toQuadraticMapLinearMap A A (M₁ ⊗[R] M₂)
  let tmulB := BilinMap.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
  let toB := AlgebraTensorModule.map
      (QuadraticMap.associated : QuadraticMap A M₁ N₁ →ₗ[A] BilinMap A M₁ N₁)
      (QuadraticMap.associated : QuadraticMap R M₂ N₂ →ₗ[R] BilinMap R M₂ N₂)
  toQ ∘ₗ tmulB ∘ₗ toB

@[simp]
theorem tensorDistrib_tmul (Q₁ : QuadraticMap A M₁ N₁) (Q₂ : QuadraticMap R M₂ N₂) (m₁ : M₁)
    (m₂ : M₂) : tensorDistrib R A (Q₁ ⊗ₜ Q₂) (m₁ ⊗ₜ m₂) = Q₁ m₁ ⊗ₜ Q₂ m₂   :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  (BilinMap.tensorDistrib_tmul _ _ _ _ _ _).trans <| congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

/-- The tensor product of two quadratic maps, a shorthand for dot notation. -/
-- `noncomputable` is a performance workaround for https://github.com/leanprover-community/mathlib4/issues/7103
protected noncomputable abbrev tmul (Q₁ : QuadraticMap A M₁ N₁)
    (Q₂ : QuadraticMap R M₂ N₂) : QuadraticMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  tensorDistrib R A (Q₁ ⊗ₜ[R] Q₂)

theorem associated_tmul [Invertible (2 : A)]
    (Q₁ : QuadraticMap A M₁ N₁) (Q₂ : QuadraticMap R M₂ N₂) :
    (Q₁.tmul Q₂).associated = Q₁.associated.tmul Q₂.associated := by
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  rw [QuadraticMap.tmul, BilinMap.tmul]
  have : Subsingleton (Invertible (2 : A)) := inferInstance
  convert associated_left_inverse A (LinearMap.BilinMap.tmul_isSymm
    (QuadraticMap.associated_isSymm A Q₁) (QuadraticMap.associated_isSymm R Q₂))

end QuadraticMap

namespace QuadraticForm

variable (R A) in
/-- The tensor product of two quadratic forms injects into quadratic forms on tensor products.

Note this is heterobasic; the quadratic form on the left can take values in a larger ring than
the one on the right. -/
-- `noncomputable` is a performance workaround for https://github.com/leanprover-community/mathlib4/issues/7103
noncomputable def tensorDistrib :
    QuadraticForm A M₁ ⊗[R] QuadraticForm R M₂ →ₗ[A] QuadraticForm A (M₁ ⊗[R] M₂) :=
  (AlgebraTensorModule.rid R A A).congrQuadraticMap.toLinearMap ∘ₗ QuadraticMap.tensorDistrib R A

-- TODO: make the RHS `MulOpposite.op (Q₂ m₂) • Q₁ m₁` so that this has a nicer defeq for
-- `R = A` of `Q₁ m₁ * Q₂ m₂`.
@[simp]
theorem tensorDistrib_tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂) :
    tensorDistrib R A (Q₁ ⊗ₜ Q₂) (m₁ ⊗ₜ m₂) = Q₂ m₂ • Q₁ m₁ :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  (LinearMap.BilinForm.tensorDistrib_tmul _ _ _ _ _ _ _ _).trans <| congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

/-- The tensor product of two quadratic forms, a shorthand for dot notation. -/
-- `noncomputable` is a performance workaround for https://github.com/leanprover-community/mathlib4/issues/7103
protected noncomputable abbrev tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    QuadraticForm A (M₁ ⊗[R] M₂) :=
  tensorDistrib R A (Q₁ ⊗ₜ[R] Q₂)

theorem associated_tmul [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.tmul Q₂).associated = BilinForm.tmul Q₁.associated Q₂.associated := by
  rw [BilinForm.tmul, BilinForm.tensorDistrib, LinearMap.comp_apply, ← BilinMap.tmul,
    ← QuadraticMap.associated_tmul Q₁ Q₂]
  aesop

theorem polarBilin_tmul [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    polarBilin (Q₁.tmul Q₂) = ⅟(2 : A) • BilinForm.tmul (polarBilin Q₁) (polarBilin Q₂) := by
  simp_rw [← two_nsmul_associated A, ← two_nsmul_associated R, BilinForm.tmul, tmul_smul,
    ← smul_tmul', map_nsmul, associated_tmul]
  rw [smul_comm (_ : A) (_ : ℕ), ← smul_assoc, two_smul _ (_ : A), invOf_two_add_invOf_two,
    one_smul]

variable (A) in
/-- The base change of a quadratic form. -/
-- `noncomputable` is a performance workaround for https://github.com/leanprover-community/mathlib4/issues/7103
protected noncomputable def baseChange (Q : QuadraticForm R M₂) : QuadraticForm A (A ⊗[R] M₂) :=
  QuadraticForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (QuadraticMap.sq (R := A)) Q

@[simp]
theorem baseChange_tmul (Q : QuadraticForm R M₂) (a : A) (m₂ : M₂) :
    Q.baseChange A (a ⊗ₜ m₂) = Q m₂ • (a * a) :=
  tensorDistrib_tmul _ _ _ _

theorem associated_baseChange [Invertible (2 : A)] (Q : QuadraticForm R M₂) :
    associated (R := A) (Q.baseChange A) = BilinForm.baseChange A (associated (R := R) Q) := by
  dsimp only [QuadraticForm.baseChange, LinearMap.baseChange]
  rw [associated_tmul (QuadraticMap.sq (R := A)) Q, associated_sq]
  exact rfl

theorem polarBilin_baseChange [Invertible (2 : A)] (Q : QuadraticForm R M₂) :
    polarBilin (Q.baseChange A) = BilinForm.baseChange A (polarBilin Q) := by
  rw [QuadraticForm.baseChange, BilinForm.baseChange, polarBilin_tmul, BilinForm.tmul,
    ← LinearMap.map_smul, smul_tmul', ← two_nsmul_associated R, coe_associatedHom, associated_sq,
    smul_comm, ← smul_assoc, two_smul, invOf_two_add_invOf_two, one_smul]

end QuadraticForm

end InvertibleTwo

/-- If two quadratic maps from `A ⊗[R] M₂` agree on elements of the form `1 ⊗ m`, they are equal.

In other words, if a base change exists for a quadratic map, it is unique.

Note that unlike `QuadraticForm.baseChange`, this does not need `Invertible (2 : R)`. -/
@[ext]
theorem baseChange_ext ⦃Q₁ Q₂ : QuadraticMap A (A ⊗[R] M₂) N₁⦄
    (h : ∀ m, Q₁ (1 ⊗ₜ m) = Q₂ (1 ⊗ₜ m)) :
    Q₁ = Q₂ := by
  replace h (a m) : Q₁ (a ⊗ₜ m) = Q₂ (a ⊗ₜ m) := by
    rw [← mul_one a, ← smul_eq_mul, ← smul_tmul', QuadraticMap.map_smul, QuadraticMap.map_smul, h]
  ext x
  induction x with
  | tmul => simp [h]
  | zero => simp
  | add x y hx hy =>
    have : Q₁.polarBilin = Q₂.polarBilin := by
      ext
      dsimp [polar]
      rw [← TensorProduct.tmul_add, h, h, h]
    replace := congr($this x y)
    dsimp [polar] at this
    linear_combination (norm := module) this + hx + hy

end CommRing
