/-
Copyright (c) 2018 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!

# Dual submodule with respect to a bilinear form.

## Main definitions and results
- `BilinForm.dualSubmodule`: The dual submodule with respect to a bilinear form.
- `BilinForm.dualSubmodule_span_of_basis`: The dual of a lattice is spanned by the dual basis.

## TODO
Properly develop the material in the context of lattices.
-/

open LinearMap (BilinForm)

variable {R S M} [CommRing R] [Field S] [AddCommGroup M]
variable [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

namespace LinearMap

namespace BilinForm

variable (B : BilinForm S M)

/-- The dual submodule of a submodule with respect to a bilinear form. -/
def dualSubmodule (N : Submodule R M) : Submodule R M where
  carrier := { x | ∀ y ∈ N, B x y ∈ (1 : Submodule R S) }
  add_mem' {a b} ha hb y hy := by simpa using add_mem (ha y hy) (hb y hy)
  zero_mem' y _ := by rw [B.zero_left]; exact zero_mem _
  smul_mem' r a ha y hy := by
    convert (1 : Submodule R S).smul_mem r (ha y hy)
    rw [← IsScalarTower.algebraMap_smul S r a]
    simp only [algebraMap_smul, map_smul_of_tower, LinearMap.smul_apply]

lemma mem_dualSubmodule {N : Submodule R M} {x} :
    x ∈ B.dualSubmodule N ↔ ∀ y ∈ N, B x y ∈ (1 : Submodule R S) := Iff.rfl

lemma le_flip_dualSubmodule {N₁ N₂ : Submodule R M} :
    N₁ ≤ B.flip.dualSubmodule N₂ ↔ N₂ ≤ B.dualSubmodule N₁ := by
  show (∀ (x : M), x ∈ N₁ → _) ↔ ∀ (x : M), x ∈ N₂ → _
  simp only [mem_dualSubmodule, Submodule.mem_one, flip_apply]
  exact forall₂_swap

/-- The natural paring of `B.dualSubmodule N` and `N`.
This is bundled as a bilinear map in `BilinForm.dualSubmoduleToDual`. -/
noncomputable
def dualSubmoduleParing {N : Submodule R M} (x : B.dualSubmodule N) (y : N) : R :=
  (Submodule.mem_one.mp <| x.prop y y.prop).choose

@[simp]
lemma dualSubmoduleParing_spec {N : Submodule R M} (x : B.dualSubmodule N) (y : N) :
    algebraMap R S (B.dualSubmoduleParing x y) = B x y :=
  (Submodule.mem_one.mp <| x.prop y y.prop).choose_spec

/-- The natural paring of `B.dualSubmodule N` and `N`. -/
-- TODO: Show that this is perfect when `N` is a lattice and `B` is nondegenerate.
@[simps]
noncomputable
def dualSubmoduleToDual [NoZeroSMulDivisors R S] (N : Submodule R M) :
    B.dualSubmodule N →ₗ[R] Module.Dual R N :=
  { toFun := fun x ↦
    { toFun := B.dualSubmoduleParing x
      map_add' := fun x y ↦ FaithfulSMul.algebraMap_injective R S (by simp)
      map_smul' := fun r m ↦ FaithfulSMul.algebraMap_injective R S
        (by simp [← Algebra.smul_def]) }
    map_add' := fun x y ↦ LinearMap.ext fun z ↦ FaithfulSMul.algebraMap_injective R S
      (by simp)
    map_smul' := fun r x ↦ LinearMap.ext fun y ↦ FaithfulSMul.algebraMap_injective R S
      (by simp [← Algebra.smul_def]) }

lemma dualSubmoduleToDual_injective (hB : B.Nondegenerate) [NoZeroSMulDivisors R S]
    (N : Submodule R M) (hN : Submodule.span S (N : Set M) = ⊤) :
    Function.Injective (B.dualSubmoduleToDual N) := by
  intro x y e
  ext
  apply LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  apply LinearMap.ext_on hN
  intro z hz
  simpa using congr_arg (algebraMap R S) (LinearMap.congr_fun e ⟨z, hz⟩)

lemma dualSubmodule_span_of_basis {ι} [Finite ι] [DecidableEq ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.dualSubmodule (Submodule.span R (Set.range b)) =
      Submodule.span R (Set.range <| B.dualBasis hB b) := by
  cases nonempty_fintype ι
  apply le_antisymm
  · intro x hx
    rw [← (B.dualBasis hB b).sum_repr x]
    apply sum_mem
    rintro i -
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp <| hx (b i) (Submodule.subset_span ⟨_, rfl⟩)
    simp only [dualBasis_repr_apply, ← hr, Algebra.linearMap_apply, algebraMap_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ y hy
    obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
    simp only [map_sum, map_smul]
    apply sum_mem
    rintro j -
    rw [← IsScalarTower.algebraMap_smul S (f j), map_smul]
    simp_rw [apply_dualBasis_left]
    rw [smul_eq_mul, mul_ite, mul_one, mul_zero, ← (algebraMap R S).map_zero, ← apply_ite]
    exact Submodule.mem_one.mpr ⟨_, rfl⟩

lemma dualSubmodule_dualSubmodule_flip_of_basis {ι : Type*} [Finite ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.dualSubmodule (B.flip.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) := by
  classical
  letI := FiniteDimensional.of_fintype_basis b
  rw [dualSubmodule_span_of_basis _ hB.flip, dualSubmodule_span_of_basis B hB,
    dualBasis_dualBasis_flip B hB]

lemma dualSubmodule_flip_dualSubmodule_of_basis {ι : Type*} [Finite ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.flip.dualSubmodule (B.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) := by
  classical
  letI := FiniteDimensional.of_fintype_basis b
  rw [dualSubmodule_span_of_basis B hB, dualSubmodule_span_of_basis _ hB.flip,
    dualBasis_flip_dualBasis B hB]

lemma dualSubmodule_dualSubmodule_of_basis
    {ι} [Finite ι] (hB : B.Nondegenerate) (hB' : B.IsSymm) (b : Basis ι S M) :
    B.dualSubmodule (B.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) := by
  classical
  letI := FiniteDimensional.of_fintype_basis b
  rw [dualSubmodule_span_of_basis B hB, dualSubmodule_span_of_basis B hB,
    dualBasis_dualBasis B hB hB']

end BilinForm

end LinearMap
