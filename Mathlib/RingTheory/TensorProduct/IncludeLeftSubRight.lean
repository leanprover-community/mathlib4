/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Exactness properties of the difference map for tensor products

For an `R`-algebra `S`, we collect some properties of the `R`-linear map `S →ₗ[R] S ⊗[R] S` given
by `s ↦ (s ⊗ₜ[R] 1) - (1 ⊗ₜ[R] s)`.

## Main definitions

* `includeLeftSubRight`: The `R`-linear map sending `s : S` to `s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s`.
* `ExactIncludeLeftSubRight`: Exactness of the sequence `R → S → S ⊗[R] S` with the right map given
  by `includeLeftSubRight`
* `toEqLocusOfInclusion`: The ring map from `R` to the equalizer locus in `S` of the two maps
  `s ↦ s ⊗ₜ (1 : S)` and `s ↦ (1 : S) ⊗ₜ s`.

## Main results

* `exactIncludeLeftSubRight_of_faithfullyFlat`: `ExactIncludeLeftSubRight R S` is true for any
  faithfully flat `R`-algebras `S`.
* `toEqLocusOfInclusion_surjective`: /-- If `ExactIncludeLeftSubRight R S` is true, then
  `toEqLocusOfInclusion R S` is surjective. -/

-/

open scoped TensorProduct

namespace Algebra.TensorProduct

universe uR uS uT

section IncludeLeftSubRight

variable {R : Type uR} [CommSemiring R]
variable {S : Type uS} [Ring S] [Algebra R S]

variable (R S) in
/-- The `R`-linear map `S →ₗ[R] S ⊗[R] S` sending `s : S` to `(s ⊗ₜ[R] 1) - (1 ⊗ₜ[R] s)`. -/
def includeLeftSubRight : S →ₗ[R] S ⊗[R] S :=
  (includeLeft (R := R) (S := R) (A := S) (B := S)).toLinearMap -
    (includeRight (R := R) (A:= S) (B := S)).toLinearMap

@[simp]
lemma includeLeftSubRight_apply (s : S) : includeLeftSubRight R S s = s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s :=
  rfl

/-- `includeLeftSubRight R S` vanishes in the range of `algebraMap R S`. -/
lemma includeLeftSubRight_zero_of_mem_range {s : S} (hs : s ∈ Set.range ⇑(algebraMap R S)) :
    (includeLeftSubRight R S) s = 0 := by
  obtain ⟨_, hr⟩ := Set.mem_range.mp hs
  simp [includeLeftSubRight, ← hr]

/-- `includeLeftSubRight` is compatible with `distribBaseChange` and `lTensor`. -/
lemma includeLeftSubRight_distribBaseChange (T : Type uT) [CommRing T] [Algebra R T] :
    (includeLeftSubRight T (T ⊗[R] S)).restrictScalars R =
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).restrictScalars R).toLinearMap ∘ₗ
      ((includeLeftSubRight R S).lTensor T) := by
  simp only [includeLeftSubRight, LinearMap.lTensor_sub, LinearMap.comp_sub,
    distribBaseChange_includeLeft_lTensor, distribBaseChange_includeRight_lTensor]
  rfl

variable (R S) in
/-- For an `R`-algebra `S`, this asserts that the maps `algebraMap : R → S` and
`includeLeftSubRight R S : S → S ⊗[R] S` form an exact pair. -/
def ExactIncludeLeftSubRight : Prop :=
  Function.Exact ⇑(algebraMap R S) ⇑(includeLeftSubRight R S)

/-- `ExactIncludeLeftSubRight` is true for any `R`-algebra `S` having an `R`-algebra section of
`Algebra.ofId _ _ : R →ₐ[R] S`. -/
lemma ExactIncludeLeftSubRight_of_section (g : AlgHom R S R) : ExactIncludeLeftSubRight R S := by
  intro s
  refine ⟨?_, includeLeftSubRight_zero_of_mem_range⟩
  intro hs
  use g s
  apply (TensorProduct.lid R S).symm.injective
  rw [lid_symm_apply, lid_symm_apply, ← mul_one ((algebraMap R S) (g s)), ← Algebra.smul_def,
    ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, ← AlgHom.id_apply (R := R) (1 : S), ← map_tmul,
    sub_eq_zero.mp ((includeLeftSubRight_apply s).symm.trans hs), map_tmul, map_one,
    AlgHom.id_apply]

end IncludeLeftSubRight

section FaithfullyFlat

variable (R : Type uR) [CommRing R]
variable (S : Type uS)
variable (T : Type uT) [CommRing T] [Algebra R T]

/-- `ExactIncludeLeftSubRight` descends along faithfully flat algebras. -/
lemma ExactIncludeLeftSubRight_desc_faithfullyFlat [Ring S] [Algebra R S]
    [Module.FaithfullyFlat R T] (h : ExactIncludeLeftSubRight T (T ⊗[R] S)) :
    ExactIncludeLeftSubRight R S := by
  refine Module.FaithfullyFlat.lTensor_reflects_exact _ _ _ _ <|
    AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      ((Algebra.linearMap R S).lTensor T) ((includeLeftSubRight R S).lTensor T)
      (Algebra.linearMap T (T ⊗[R] S)) (includeLeftSubRight T (T ⊗[R] S))
      (TensorProduct.rid R R T).toAddMonoidHom (AddMonoidHom.id (T ⊗[R] S))
      (TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).toAddMonoidHom ?_ ?_
      (TensorProduct.rid R R T).surjective Function.bijective_id
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).injective)|>.mpr ‹_›
  · ext
    simp [← Algebra.TensorProduct.rid_lTensor]
  · change ((includeLeftSubRight _ _).restrictScalars R).toAddMonoidHom.comp _ = _
    ext
    simp only [includeLeftSubRight_distribBaseChange]
    rfl

/-- `ExactIncludeLeftSubRight R S` is true for any faithfully flat `R`-algebras `S`. -/
lemma exactIncludeLeftSubRight_of_faithfullyFlat [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] : ExactIncludeLeftSubRight R S :=
  ExactIncludeLeftSubRight_desc_faithfullyFlat _ _ _
    (ExactIncludeLeftSubRight_of_section (lmul'' R))

end FaithfullyFlat

section CommRingCat

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- For an `R`-algebra `S`, the canonical ring map from `R` to the equalizer locus of
`s ↦ s ⊗ₜ (1 : S)` and `s ↦ (1 : S) ⊗ₜ s`. -/
def toEqLocusOfInclusion : R →+* (CommRingCat.pushoutCocone R S S).inl.hom.eqLocus
    (CommRingCat.pushoutCocone R S S).inr.hom where
  toFun r := Subtype.mk (algebraMap R S r) (by simp [RingHom.eqLocus, tmul_one_eq_one_tmul])
  map_zero' := by apply Subtype.ext; simp
  map_one' := by apply Subtype.ext; simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp

/-- If the underlying ring map of an `R`-algebra `S` is injective, so is
`toEqLocusOfInclusion R S`. -/
lemma toEqLocusOfInclusion_injective (h : Function.Injective (algebraMap R S)) :
    Function.Injective (toEqLocusOfInclusion R S) := by
  intro _ _ h_eq
  simp only [toEqLocusOfInclusion, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Subtype.mk.injEq] at h_eq
  exact h h_eq

/-- If `ExactIncludeLeftSubRight R S` is true, then `toEqLocusOfInclusion R S` is surjective. -/
lemma toEqLocusOfInclusion_surjective (h : ExactIncludeLeftSubRight R S) :
    Function.Surjective (toEqLocusOfInclusion R S) := by
  intro s
  have s_mem : s.val ∈ Set.range ⇑(Algebra.linearMap R S) :=
    (h s.val).mp ((includeLeftSubRight_apply (R := R) s.val).symm ▸ sub_eq_zero.mpr s.property)
  use (Set.mem_range.mp s_mem).choose
  ext
  nth_rw 5 [← (Set.mem_range.mp s_mem).choose_spec]
  simp [toEqLocusOfInclusion]

end CommRingCat

end Algebra.TensorProduct
