/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Construction of the tensor product over an algebra from the tensor product over its ring

If $A$ is an $R$-algebra, then the tensor product $M\otimes_A N$ of two modules $M,N$ over $A$
can be constructed as a quotient of $M\otimes_R N$. In this file the relation underlying this
quotient procedure is defined and it is shown that this construction of the tensor product agrees
with the construction of the tensor product directly over the ring $A$.

# Main constructions

 - `mk` : The construction of the tensor product using the algebra structure
 - `quot_equi_tens` The isomorphism between this construction of the tensor product and the generic
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
/-- The (additive) generators of the kernel of the natural map `M ⊗[R] N → M ⊗[A] N`. -/
def elem_rel : SubMulAction A (M ⊗[R] N) where
  carrier :=  { (a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m: M) (n : N)}
  smul_mem' := by
    intros a x hx
    obtain ⟨a', m, n, h⟩ := hx
    use  a',  a • m, n
    simp_rw [←h, smul_sub, ←smul_tmul', sub_left_inj, smul_smul, mul_comm]

omit [IsScalarTower R A N] in
lemma elem_rel_mem (x : (M ⊗[R] N)) : x ∈ (elem_rel R A M N) ↔
    (∃ (a : A) (m : M) (n : N), x = (a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n)) := by
  simp_rw [← SetLike.mem_coe, ← SubMulAction.mem_carrier, elem_rel, Set.mem_setOf, eq_comm]

variable (R A M N) in
/-- The module of relations in `(M ⊗[R] N)` that have to be divided out to obtain `(M ⊗[A] N)` -/
abbrev rels := (Submodule.span A ((elem_rel R A M N) : Set (M ⊗[R] N) ))

variable (R A M N) in
/-- The tensor product `(M ⊗[A] N)` constructed as a quotient of `(M ⊗[R] N)` -/
abbrev mk := (M⊗[R] N) ⧸ (rels R A M N)

variable (R A M N) in
/-- The natural bilinear map into the algebra-based construction of the tensor product -/
def bil_to_mk : M →ₗ[A] N →ₗ[A] (mk R A M N) where
  toFun m := {
    toFun n := (rels R A M N).mkQ (m⊗ₜn)
    map_add' _ _ := by simp [tmul_add]
    map_smul' a n := by
      rw [RingHom.id_apply, ←LinearMap.map_smul, ←sub_eq_zero, ← LinearMap.map_sub,smul_tmul',
        ← LinearMap.mem_ker, Submodule.ker_mkQ, ←neg_mem_iff]
      refine Submodule.mem_span_of_mem ?_
      rw [SetLike.mem_coe, elem_rel_mem]
      use a, m, n
      simp}
  map_add' _ _ := by ext _; simp [add_tmul]
  map_smul' _ _ := by
    ext _
    simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
      LinearMap.smul_apply, ←LinearMap.map_smul, smul_tmul']

omit [IsScalarTower R A N] in
@[simp] lemma bil_to_mk_apply (m : M) (n : N) : bil_to_mk R A M N m n = ⟦m⊗ₜn⟧ := by rfl

variable (R A M N) in
/-- the natural map from the tensor product to the algebra-based construction of the tensor product
-/
abbrev tens_to_mk := TensorProduct.lift (bil_to_mk R A M N)

omit [IsScalarTower R A N] in
@[simp] lemma tens_to_mk_apply (m : M) (n : N) : tens_to_mk R A M N (m⊗ₜn) = ⟦m⊗ₜn⟧ := by rfl

variable (R A M N) in
lemma span_in_ker : (rels R A M N) ≤ (mapOfCompatibleSMul' A R M N).ker := by
  simp_rw [LinearMap.le_ker_iff_comp_subtype_eq_zero, Submodule.linearMap_eq_zero_iff_of_eq_span
   (S:=((elem_rel R A M N) : Set (M ⊗[R] N) )) , LinearMap.coe_comp, Submodule.coe_subtype,
   Function.comp_apply, Subtype.forall]
  intro x hx
  rw [SetLike.mem_coe, elem_rel_mem] at hx
  obtain ⟨a, m, n, heq⟩ := hx
  simp [heq, mapOfCompatibleSMul', smul_tmul]


variable (R A M N) in
/-- the natural map from the algebra-based construction of the tensor product to
the tensor product -/
abbrev mk_to_tens := Submodule.liftQ  (rels R A M N) (mapOfCompatibleSMul' A R M N)
  (span_in_ker R A M N)

@[simp]
lemma mk_to_tens_apply (m : M) (n : N) : mk_to_tens R A M N ⟦m⊗ₜn⟧ = m⊗ₜn := by rfl

variable (R A M N) in
/-- The definition of the equivalence between the algebra-based construction of the tensor product
and the tensor product -/
def quot_equi_tens :(mk R A M N) ≃ₗ[A] M ⊗[A] N where
  toLinearMap := mk_to_tens R A M N
  invFun := tens_to_mk R A M N
  left_inv := by
    rw [Function.leftInverse_iff_comp]
    ext z
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Function.comp_apply, id_eq]
    obtain ⟨y, hy⟩ := Quotient.exists_rep z
    obtain ⟨S, h⟩ := exists_finset (y)
    simp_rw [← hy, h, Submodule.Quotient.mk''_eq_mk, ← Submodule.mkQ_apply, map_sum,
      Submodule.mkQ_apply, ← Submodule.Quotient.mk''_eq_mk]
    simp only [mk_to_tens_apply, tens_to_mk_apply]
  right_inv := by
    rw [Function.rightInverse_iff_comp]
    ext z
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Function.comp_apply, id_eq]
    obtain ⟨S, h⟩ := exists_finset (z)
    simp_rw [h]
    simp

variable (R A M N) in
lemma compose_eq_mkQ :(tens_to_mk R A M N) ∘ₗ (mapOfCompatibleSMul' A R M N)
    = (rels R A M N).mkQ := by
  ext _ _
  simp [mapOfCompatibleSMul', Submodule.Quotient.mk''_eq_mk]

variable (R A M N) in
lemma CompatibleSMul_ker_eq_span : (mapOfCompatibleSMul' A R M N).ker = (rels R A M N)
    := by
  rw [← LinearEquiv.ker_comp (quot_equi_tens R A M N).symm (mapOfCompatibleSMul' A R M N)]
  have h : (quot_equi_tens R A M N).symm.toLinearMap = tens_to_mk R A M N := rfl
  rw [h, compose_eq_mkQ]
  simp

end Algebra.TensorProduct.FromRing

end
