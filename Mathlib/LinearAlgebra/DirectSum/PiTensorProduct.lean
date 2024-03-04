/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Eric Wieser
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Algebra.DirectSum.Module

/-!
# Tensor products of direct sums

This file shows that taking `PiTensorProduct`s commutes with taking `DirectSum`s in all arguments.

## Main results

* `PiTensorProduct.directSum`
-/

set_option maxHeartbeats 500000

suppress_compilation

namespace MultilinearMap

open PiTensorProduct DirectSum LinearMap BigOperators Function

open scoped TensorProduct

attribute [local ext] TensorProduct.ext

variable (R : Type*) [CommSemiring R]

variable {ι : Type*}

variable [Fintype ι]

variable [DecidableEq ι]

section fromDirectSum

variable (κ : ι → Type*) [(i : ι) → DecidableEq (κ i)]

variable {M : (i : ι) → κ i → Type*} {M' : Type*}

variable [∀ i (j : κ i), AddCommMonoid (M i j)] [AddCommMonoid M']

variable [∀ i (j : κ i), Module R (M i j)] [Module R M']

variable [(i : ι) → (j : κ i) → (x : M i j) → Decidable (x ≠ 0)]

theorem fromDirectSum_aux1 (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : (i : ι) → ⨁ (j : κ i), M i j) {p : (i : ι) → κ i}
    (hp : p ∉ Fintype.piFinset (fun i ↦ (x i).support)) :
    (f p) (fun j ↦ (x j) (p j)) = 0 := by
  simp only [Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq, not_forall, not_not] at hp
  obtain ⟨i, hi⟩ := hp
  exact (f p).map_coord_zero i hi

theorem fromDirectSum_aux2 (x : (i : ι) → ⨁ (j : κ i), M i j) (i : ι) (p : (i : ι) → κ i)
    (a : ⨁ (j : κ i), M i j) :
    (fun j ↦ (update x i a j) (p j)) = update (fun j ↦ x j (p j)) i (a (p i)) := by
  ext j
  by_cases h : j =i
  · rw [h]; simp only [update_same]
  · simp only [ne_eq, h, not_false_eq_true, update_noteq]

def fromDirectSum (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M') :
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' where
  toFun x := ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i))
  map_add' x i a b := by
    simp only
    rename_i myinst _ _ _ _ _ _ _
    conv_lhs => rw [← Finset.sum_union_eq_right (s₁ := @Fintype.piFinset _ myinst _ _
        (fun j ↦ (update x i a j).support)
        ∪ @Fintype.piFinset _ myinst _ _ (fun j ↦ (update x i b j).support))
        (fun p _ hp ↦ by
          letI := myinst
          exact fromDirectSum_aux1 _ _ f _ hp)]
    rw [Finset.sum_congr rfl (fun p _ ↦ by rw [fromDirectSum_aux2 _ _ _ p (a + b)])]
    erw [Finset.sum_congr rfl (fun p _ ↦ (f p).map_add _ i (a (p i)) (b (p i)))]
    rw [Finset.sum_add_distrib]
    congr 1
    · conv_lhs => rw [← Finset.sum_congr rfl (fun p _ ↦ by rw [← fromDirectSum_aux2 _ _ _ p a]),
                    Finset.sum_congr (Finset.union_assoc _ _ _) (fun _ _ ↦ rfl)]
      rw [Finset.sum_union_eq_left (fun p _ hp ↦ by
        letI := myinst
        exact fromDirectSum_aux1 _ _ f _ hp)]
    · conv_lhs => rw [← Finset.sum_congr rfl (fun p _ ↦ by rw [← fromDirectSum_aux2 _ _ _ p b]),
        Finset.sum_congr (Finset.union_assoc _ _ _) (fun _ _ ↦ rfl),
        Finset.sum_congr (Finset.union_comm _ _) (fun _ _ ↦ rfl),
        Finset.sum_congr (Finset.union_assoc _ _ _) (fun _ _ ↦ rfl)]
      rw [Finset.sum_union_eq_left (fun p _ hp ↦ by
        letI := myinst
        exact fromDirectSum_aux1 _ _ f _ hp)]
  map_smul' x i c a := by
    simp only
    rename_i myinst _ _ _ _ _ _ _
    conv_lhs => rw [← Finset.sum_union_eq_right (s₁ := @Fintype.piFinset _ myinst _ _
      (fun j ↦ (update x i a j).support))
        (fun p _ hp ↦ by
          letI := myinst
          exact fromDirectSum_aux1 _ _ f _ hp),
      Finset.sum_congr rfl (fun p _ ↦ by rw [fromDirectSum_aux2 _ _ _ p _])]
    erw [Finset.sum_congr rfl (fun p _ ↦ (f p).map_smul _ i c (a (p i)))]
    rw [← Finset.smul_sum]
    conv_lhs => rw [← Finset.sum_congr rfl (fun p _ ↦ by rw [← fromDirectSum_aux2 _ _ _ p _]),
      Finset.sum_union_eq_left (fun p _ hp ↦ by
          letI := myinst
          exact fromDirectSum_aux1 _ _ f _ hp)]

@[simp]
theorem fromDirectSum_apply (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : (i : ι) → ⨁ (j : κ i), M i j) : fromDirectSum R κ f x =
    ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := rfl

def fromDirectSumₗ : ((p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M') →ₗ[R]
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' where
  toFun := fromDirectSum R κ
  map_add' f g := by
    ext x
    simp only [fromDirectSum_apply, Pi.add_apply, MultilinearMap.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    simp only [fromDirectSum_apply, Pi.smul_apply, MultilinearMap.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]

@[simp]
theorem fromDirectSumₗ_apply (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : (i : ι) → ⨁ (j : κ i), M i j) : fromDirectSumₗ R κ f x =
    ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := rfl

def fromDirectSumEquiv : ((p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M') ≃ₗ[R]
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' := by
  refine LinearEquiv.ofLinear (fromDirectSumₗ R κ) (LinearMap.pi
    (fun p ↦ MultilinearMap.compLinearMapₗ (fun i ↦ DirectSum.lof R (κ i) _ (p i)))) ?_ ?_
  · ext f x
    simp only [coe_comp, Function.comp_apply, fromDirectSumₗ_apply, pi_apply,
      MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply, id_coe, id_eq]
    change _ = f (fun i ↦ x i)
    rw [funext (fun i ↦ Eq.symm (DirectSum.sum_support_of (fun j ↦ M i j) (x i)))]
    rw [MultilinearMap.map_sum_finset]
    rfl
  · ext f p a
    simp only [coe_comp, Function.comp_apply, LinearMap.pi_apply, compLinearMapₗ_apply,
      compLinearMap_apply, fromDirectSumₗ_apply, id_coe, id_eq]
    have hsub : Fintype.piFinset (fun i ↦ DFinsupp.support ((lof R (κ i) (M i) (p i)) (a i)))
        ⊆ {p} := by
      intro q
      simp only [Fintype.mem_piFinset, ne_eq, Finset.mem_singleton]
      simp_rw [DirectSum.lof_eq_of]
      exact fun hq ↦
          funext fun i ↦ Finset.mem_singleton.mp (DirectSum.support_of_subset _ (hq i))
    rw [Finset.sum_subset hsub]
    · rw [Finset.sum_singleton]
      simp only [lof_apply]
    · simp only [Finset.mem_singleton, Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq,
        not_forall, not_not, forall_exists_index, forall_eq, lof_apply]
      intro i hi
      exact (f p).map_coord_zero i hi


-- hsub should be a lemma, it has already been used three times

@[simp]
theorem fromDirectSumEquiv_apply (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : (i : ι) → ⨁ (j : κ i), M i j) : fromDirectSumEquiv R κ f x =
    ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := rfl

@[simp]
theorem fromDirectSumEquiv_symm_apply (f : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M')
    (p : (i : ι) → κ i) : (fromDirectSumEquiv R κ).symm f p =
    f.compLinearMap (fun i ↦ DirectSum.lof R (κ i) _ (p i)) := rfl

end fromDirectSum

end MultilinearMap

section Ring

namespace PiTensorProduct

open PiTensorProduct

open DirectSum

open LinearMap

open scoped TensorProduct

attribute [local ext] TensorProduct.ext

variable (R : Type*) [CommSemiring R]

variable {ι : Type*} {κ : ι → Type*}

variable [Fintype ι]

variable [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]

variable (M : (i : ι) → κ i → Type*) (M' : Type*)

variable [∀ i (j : κ i), AddCommMonoid (M i j)] [AddCommMonoid M']

variable [∀ i (j : κ i), Module R (M i j)] [Module R M']

variable [(i : ι) → (j : κ i) → (x : M i j) → Decidable (x ≠ 0)]

/-- The linear equivalence `⨂[R] i, (⨁ j : κ i, M i j) ≃ ⨁ p : (i : ι) → κ i, ⨂[R] i, M i (p i)`,
 i.e. "tensor product distributes over direct sum". -/
protected def directSum :
    (⨂[R] i, (⨁ j : κ i, M i j)) ≃ₗ[R] ⨁ p : (i : ι) → κ i, ⨂[R] i, M i (p i) := by
  refine LinearEquiv.ofLinear (R := R) (R₂ := R) ?toFun ?invFun ?left ?right
  · exact lift (MultilinearMap.fromDirectSumEquiv R (M := M)
      (fun p ↦ (DirectSum.lof R _ _ p).compMultilinearMap (PiTensorProduct.tprod R)))
  · refine DirectSum.toModule R _ _ (fun p ↦ lift (LinearMap.compMultilinearMap
      (PiTensorProduct.map (fun i ↦ DirectSum.lof R _ _ (p i))) (tprod R)))
  · ext p x
    simp only [compMultilinearMap_apply, coe_comp, Function.comp_apply, toModule_lof, lift.tprod,
      map_tprod, MultilinearMap.fromDirectSumEquiv_apply, id_comp]
    have hsub : (Fintype.piFinset fun i ↦ DFinsupp.support
        ((lof R (κ i) (fun j ↦ M i j) (p i)) (x i))) ⊆ {p} := by
      intro q
      simp only [Fintype.mem_piFinset, ne_eq, Finset.mem_singleton]
      simp_rw [DirectSum.lof_eq_of]
      exact fun hq ↦
          funext fun i ↦ Finset.mem_singleton.mp (DirectSum.support_of_subset _ (hq i))
    rw [Finset.sum_subset hsub]
    · rw [Finset.sum_singleton]
      simp only [lof_apply]
    · simp only [Finset.mem_singleton, Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq,
        not_forall, not_not, forall_exists_index, forall_eq, lof_apply]
      intro i hi
      rw [(tprod R).map_coord_zero i hi, LinearMap.map_zero]
  · ext x
    simp only [compMultilinearMap_apply, coe_comp, Function.comp_apply, lift.tprod,
      MultilinearMap.fromDirectSumEquiv_apply, map_sum, toModule_lof, map_tprod, id_coe, id_eq]
    change _ = tprod R (fun i ↦ x i)
    rw [funext (fun i ↦ Eq.symm (DirectSum.sum_support_of (fun j ↦ M i j) (x i)))]
    rw [MultilinearMap.map_sum_finset]
    rfl
-- We are doing stuff that we did in the construction of `MultilinearMap.fromDirectSumEquiv`,
-- so there must be a better way.

end PiTensorProduct

end Ring
