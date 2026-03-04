/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Exactness properties of the difference map on tensor products

For an `R`-algebra `S`, we collect some properties of the `R`-linear map `S →ₗ[R] S ⊗[R] S` given
by `s ↦ s ⊗ₜ 1 - 1 ⊗ₜ s`.

## Main definitions

* `includeLeftSubRight`: The `R`-linear map sending `s : S` to `s ⊗ₜ 1 - 1 ⊗ₜ s`.
* `IsEffective`: Exactness of the sequence `R → S → S ⊗[R] S` where the first map is
  `Algebra.linearMap R S` and the second map is `includeLeftSubRight`. When `R` and `S` are
  commutative rings, this is equivalent to the inclusion `im (algebraMap : R → S) → S` being an
  effective monomorphism in `CommRingCat`.

## Main results

* `IsEffective.of_faithfullyFlat`: `IsEffective R S` is true for any faithfully flat `R`-algebra `S`

-/

@[expose] public section

open scoped TensorProduct

namespace Algebra

variable {R : Type*} [CommSemiring R]
variable {S : Type*} [Ring S] [Algebra R S]

namespace TensorProduct

section IncludeLeftSubRight

variable (R S) in
/-- The `R`-linear map `S →ₗ[R] S ⊗[R] S` sending `s : S` to `s ⊗ₜ 1 - 1 ⊗ₜ s`. -/
def includeLeftSubRight : S →ₗ[R] S ⊗[R] S :=
  includeLeft.toLinearMap - includeRight.toLinearMap

@[simp]
lemma includeLeftSubRight_apply (s : S) : includeLeftSubRight R S s = s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s :=
  rfl

/-- `includeLeftSubRight R S` vanishes in the range of `algebraMap R S`. -/
lemma includeLeftSubRight_zero_of_mem_range {s : S} (hs : s ∈ Set.range ⇑(algebraMap R S)) :
    includeLeftSubRight R S s = 0 := by
  obtain ⟨_, hr⟩ := Set.mem_range.mp hs
  simp [includeLeftSubRight, ← hr]

/-- `includeLeftSubRight R S` vanishes at `algebraMap R S r`. -/
lemma includeLeftSubRight_algebraMap_zero (r : R) :
    includeLeftSubRight R S (algebraMap R S r) = 0 :=
  includeLeftSubRight_zero_of_mem_range (Set.mem_range.mp (exists_apply_eq_apply _ _))

/-- `includeLeftSubRight` is compatible with `distribBaseChange` and `lTensor`. -/
lemma distribBaseChange_comp_includeLeftSubRight (T : Type*) [CommRing T] [Algebra R T] :
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).restrictScalars R).toLinearMap ∘ₗ
      (includeLeftSubRight R S).lTensor T =
    (includeLeftSubRight T (T ⊗[R] S)).restrictScalars R := by
  ext
  simp [TensorProduct.tmul_sub, TensorProduct.one_def, tmul_one_tmul_one_tmul]

@[simp]
lemma distribBaseChange_includeLeftSubRight_apply (T : Type*) [CommRing T] [Algebra R T]
    (x : T ⊗[R] S) :
    TensorProduct.AlgebraTensorModule.distribBaseChange R T S S
      ((includeLeftSubRight R S).lTensor T x) =
    includeLeftSubRight T (T ⊗[R] S) x :=
  congr($(distribBaseChange_comp_includeLeftSubRight _) x)

end IncludeLeftSubRight

end TensorProduct

variable (R S) in
/-- For an `R`-algebra `S`, this asserts that the maps `algebraMap : R → S` and
`includeLeftSubRight R S : S → S ⊗[R] S` form an exact pair.
When `R` and `S` are commutative rings, this is true if and only if the inclusion
`im (algebraMap : R → S) → S` is an effective monomorphism in the category of commutative rings. -/
def IsEffective : Prop :=
  Function.Exact (Algebra.linearMap R S) (TensorProduct.includeLeftSubRight R S)

namespace IsEffective

/-- If `IsEffective R S` is true, then the equalizer of `s ↦ s ⊗ₜ 1 : S →+* S ⊗[R] S` and
`s ↦ 1 ⊗ₜ s : S →+* S ⊗[R] S` is the image of `algebraMap R S : R →+* S`. -/
lemma eqLocus_includeLeft_includeRight (h : IsEffective R S) :
    TensorProduct.includeLeftRingHom.eqLocus TensorProduct.includeRight.toRingHom (S := S ⊗[R] S) =
      Set.range (algebraMap R S) := by
  ext s
  refine ⟨?_, fun ⟨_, hr⟩ ↦ by simp [← hr]⟩
  intro hs
  exact (h s).mp <| (TensorProduct.includeLeftSubRight_apply (R := R) s).symm ▸ sub_eq_zero.mpr hs

/-- `IsEffective` is true for any `R`-algebra `S` having an `R`-algebra section of
`Algebra.ofId _ _ : R →ₐ[R] S`. -/
lemma of_section (g : S →ₐ[R] R) : IsEffective R S := by
  intro s
  refine ⟨?_, TensorProduct.includeLeftSubRight_zero_of_mem_range⟩
  intro hs
  use g s
  apply (TensorProduct.lid R S).symm.injective
  rw [TensorProduct.lid_symm_apply, TensorProduct.lid_symm_apply,
    ← mul_one ((Algebra.linearMap R S) _), Algebra.coe_linearMap, ← Algebra.smul_def,
    ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, ← AlgHom.id_apply (R := R) (1 : S),
    ← TensorProduct.map_tmul,
    sub_eq_zero.mp ((TensorProduct.includeLeftSubRight_apply s).symm.trans hs),
    TensorProduct.map_tmul, map_one, AlgHom.id_apply]

section FaithfullyFlat

variable (R : Type*) [CommRing R]
variable (S : Type*)
variable (T : Type*) [CommRing T] [Algebra R T]

/-- `IsEffective` descends along faithfully flat algebras. -/
lemma of_isEffective_tensorProduct_of_faithfullyFlat
    [Ring S] [Algebra R S] [Module.FaithfullyFlat R T] (h : IsEffective T (T ⊗[R] S)) :
    IsEffective R S := by
  refine Module.FaithfullyFlat.lTensor_reflects_exact _ _ _ _ <|
    AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      ((Algebra.linearMap R S).lTensor T) ((TensorProduct.includeLeftSubRight R S).lTensor T)
      (Algebra.linearMap T (T ⊗[R] S)) (TensorProduct.includeLeftSubRight T (T ⊗[R] S))
      (TensorProduct.rid R R T).toAddMonoidHom (AddMonoidHom.id (T ⊗[R] S))
      (TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).toAddMonoidHom ?_ ?_
      (TensorProduct.rid R R T).surjective Function.bijective_id
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).injective)|>.mpr ‹_›
  · ext
    simp [← Algebra.TensorProduct.linearMap_comp_rid]
  · ext
    simp

/-- `IsEffective R S` is true for any faithfully flat `R`-algebra `S`. -/
lemma of_faithfullyFlat [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] :
    IsEffective R S :=
  of_isEffective_tensorProduct_of_faithfullyFlat _ _ _ (of_section (TensorProduct.lmul'' R))

end FaithfullyFlat

end IsEffective

end Algebra
