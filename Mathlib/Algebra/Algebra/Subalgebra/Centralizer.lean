/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Properties of centers and centralizers

This file contains theorems about the center and centralizer of a subalgebra.

## Main results

Let `R` be a commutative ring and `A` and `B` two `R`-algebras.
- `Subalgebra.centralizer_sup`: if `S` and `T` are subalgebras of `A`, then the centralizer of
  `S ⊔ T` is the intersection of the centralizer of `S` and the centralizer of `T`.
- `Subalgebra.centralizer_range_includeLeft_eq_center_tensorProduct`: if `B` is free as a module,
  then the centralizer of `A` in `A ⊗ B` is `C(A) ⊗ B` where `C(A)` is the center of `A`.
- `Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct`: if `A` is free as a module,
  then the centralizer of `B` in `A ⊗ B` is `A ⊗ C(B)` where `C(B)` is the center of `B`.
-/

namespace Subalgebra

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {A : Type*} [Semiring A] [Algebra R A]

lemma le_centralizer_iff (S T : Subalgebra R A) : S ≤ centralizer R T ↔ T ≤ centralizer R S :=
  ⟨fun h t ht _ hs ↦ (h hs t ht).symm, fun h s hs _ ht ↦ (h ht s hs).symm⟩

lemma centralizer_sup (S T : Subalgebra R A) :
    centralizer R ((S ⊔ T : Subalgebra R A) : Set A) = centralizer R S ⊓ centralizer R T := by
  refine eq_of_forall_le_iff fun K ↦ ?_
  simp_rw [le_centralizer_iff, sup_le_iff, le_inf_iff, K.le_centralizer_iff]

lemma centralizer_iSup {ι : Sort*} (S : ι → Subalgebra R A) :
    centralizer R ((⨆ i, S i : Subalgebra R A) : Set A) = ⨅ i, centralizer R (S i) := by
  refine eq_of_forall_le_iff fun K ↦ ?_
  simp_rw [le_centralizer_iff, iSup_le_iff, le_iInf_iff, K.le_centralizer_iff]

end CommSemiring

section Free

variable (R : Type*) [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable (B : Type*) [Semiring B] [Algebra R B]

open Finsupp TensorProduct

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R`-module.
Then the centralizer of `A ⊆ A ⊗ B` is `C(A) ⊗ B` where `C(A)` is the center of `A`.
-/
lemma centralizer_range_includeLeft_eq_center_tensorProduct [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).range =
    (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.id R B)).range := by
  classical
  ext w
  constructor
  · intro hw
    rw [Subalgebra.mem_centralizer_iff] at hw
    let ℬ := Module.Free.chooseBasis R B
    obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ w
    refine Subalgebra.sum_mem _ fun j hj => ⟨⟨b j, ?_⟩ ⊗ₜ[R] ℬ j, by simp⟩
    rw [Subalgebra.mem_center_iff]
    intro x
    suffices x • b = b.mapRange (fun a ↦ a * x) (by simp) from Finsupp.ext_iff.1 this j
    specialize hw (x ⊗ₜ[R] 1) ⟨x, rfl⟩
    simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Finset.sum_mul, mul_one] at hw
    refine TensorProduct.sum_tmul_basis_right_injective ℬ ?_
    simp only [Finsupp.coe_lsum]
    rw [sum_of_support_subset (s := b.support) (hs := Finsupp.support_smul) (h := by aesop),
      sum_of_support_subset (s := b.support) (hs := support_mapRange) (h := by aesop)]
    simpa only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, LinearMap.flip_apply,
      TensorProduct.mk_apply, Finsupp.mapRange_apply] using hw

  · rintro ⟨w, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.map_tmul, coe_val, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Subalgebra.mem_center_iff.1 b.2 x]
    | add y z hy hz => rw [map_add, mul_add, hy, hz, add_mul]

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `A` is free as `R`-module.
Then the centralizer of `B ⊆ A ⊗ B` is `A ⊗ C(B)` where `C(B)` is the center of `B`.
-/
lemma centralizer_range_includeRight_eq_center_tensorProduct [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).range =
    (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).range := by
  have eq1 := centralizer_range_includeLeft_eq_center_tensorProduct R B A
  apply_fun Subalgebra.comap (Algebra.TensorProduct.comm R A B).toAlgHom at eq1
  convert eq1
  · ext x
    simpa only [AlgHom.coe_range, mem_centralizer_iff, Set.mem_range,
      Algebra.TensorProduct.includeRight_apply, forall_exists_index, forall_apply_eq_imp_iff,
      AlgEquiv.toAlgHom_eq_coe, mem_comap, AlgHom.coe_coe,
      Algebra.TensorProduct.includeLeft_apply] using
      ⟨fun h b ↦ (Algebra.TensorProduct.comm R A B).symm.injective <| by simpa using h b,
        fun h b ↦ (Algebra.TensorProduct.comm R A B).injective <| by simpa using h b⟩
  ext x
  simp only [AlgHom.mem_range, AlgEquiv.toAlgHom_eq_coe, mem_comap, AlgHom.coe_coe]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(Algebra.TensorProduct.comm R _ _) x, by rw [Algebra.TensorProduct.comm_comp_map_apply]⟩
  · rintro ⟨y, hy⟩
    refine ⟨(Algebra.TensorProduct.comm R _ _) y, (Algebra.TensorProduct.comm R A B).injective ?_⟩
    rw [← hy, Algebra.TensorProduct.comm_comp_map_apply, ← Algebra.TensorProduct.comm_symm,
      AlgEquiv.symm_apply_apply]

lemma centralizer_tensorProduct_eq_center_tensorProduct_left [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.ofId R B)).range =
    (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.id R B)).range := by
  rw [← centralizer_range_includeLeft_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

lemma centralizer_tensorProduct_eq_center_tensorProduct_right [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.map (Algebra.ofId R A) (AlgHom.id R B)).range =
    (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).range := by
  rw [← centralizer_range_includeRight_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

end Free

end Subalgebra
