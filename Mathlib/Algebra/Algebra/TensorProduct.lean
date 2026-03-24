/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Exact

/-!
# Construction of the tensor product over an algebra from the tensor product over its ring

If $A$ is an $R$-algebra, then the tensor product $M\otimes_A N$ of two modules $M,N$ over $A$
can be constructed as a quotient of $M\otimes_R N$. In this file the relation underlying this
quotient procedure is defined and it is shown that this construction of the tensor product agrees
with the construction of the tensor product directly over the ring $A$.

# Main constructions

 - `mk` : The construction of the tensor product using the algebra structure
 - `mk_eq_tens` The isomorphism between this construction of the tensor product and the generic
  one
-/

@[expose] public section

namespace Algebra.TensorProduct.FromRing

variable {R : Type*} [CommSemiring R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {N : Type*} [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]

open _root_.TensorProduct

variable (R A M N) in
/-- The relations on an `R`-tensor product `(M ⊗[R] N)` assuring `A`-linearity. -/
abbrev rels := (Submodule.span A ({(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m: M) (n : N)}))

variable (R A M N) in
/-- The tensor product `(M ⊗[A] N)` constructed as a quotient of `(M ⊗[R] N)` -/
abbrev mk := (M ⊗[R] N) ⧸ (rels R A M N)

variable (R A M N) in
lemma rels_in_ker : (rels R A M N) ≤ (mapOfCompatibleSMul' A R M N).ker := by
  rw [Submodule.span_le]
  rintro x ⟨a, m, n, h⟩
  simp [← h, smul_tmul]

variable (R A M N) in
/-- The equivalence between the algebra-based construction of the tensor product `mk`
and the general construction of the tensor product. -/
def mk_eq_tens : (mk R A M N) ≃ₗ[A] M ⊗[A] N where
  toLinearMap := Submodule.liftQ (rels R A M N) (mapOfCompatibleSMul' A R M N) (rels_in_ker R A M N)
  invFun : M ⊗[A] N →ₗ[A] mk R A M N := TensorProduct.lift ({
    toFun m := {
      toFun n := (rels R A M N).mkQ (m⊗ₜn)
      map_add' _ _ := by simp [tmul_add]
      map_smul' a n := by
        symm
        simp_rw [Submodule.mkQ_apply, ←Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        exact Submodule.subset_span ⟨a, m, n, rfl⟩ }
    map_add' _ _ := by ext _; simp [add_tmul]
    map_smul' _ _ := by simp; rfl })
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    induction x using TensorProduct.induction_on <;> simp_all
  right_inv := by
    intro x
    induction x using TensorProduct.induction_on <;> simp_all

variable (R A M N) in
@[simp]
lemma mk_eq_tens_mapOfCompatibleSMul' : mk_eq_tens R A M N ∘ₗ (rels R A M N).mkQ
    = (mapOfCompatibleSMul' A R M N) := rfl

variable (R A) in
@[simp]
lemma mk_eq_tens_tmul_apply (m : M) (n : N) :
    mk_eq_tens R A M N  (Submodule.Quotient.mk (m⊗ₜ[R] n)) = m⊗ₜ[A] n := by
  unfold mk_eq_tens
  simp [Submodule.liftQ_apply]

variable (R A) in
@[simp]
lemma mk_eq_tens_inv_tmul_apply (m : M) (n : N) :
    (mk_eq_tens R A M N).symm (m⊗ₜ[A] n) =  (rels R A M N).mkQ  (m⊗ₜ[R] n) := by
  unfold mk_eq_tens
  simp

lemma rels_tens_mk_exact : Function.Exact ((rels R A M N).subtype) (mapOfCompatibleSMul' A R M N)
    := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro h
    rw [← mk_eq_tens_mapOfCompatibleSMul', LinearEquiv.ker_comp] at h
    simp_all
  · intro h
    apply (rels_in_ker R A M N)
    simp_all








end Algebra.TensorProduct.FromRing

end
