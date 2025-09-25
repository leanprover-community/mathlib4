/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Exactness properties of the difference map for tensor products

For an `R`-algebra `S`, we collect some properties of the `R`-linear map `S →ₗ[R] S ⊗[R] S` defined
by `s ↦ s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s`.

## Main definitions

* `Algebra.TensorProduct.includeLeftSubRight`: The `R`-linear map sending `s : S` to
  `s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s`.

## Main results

* `Algebra.TensorProduct.Exact.includeLeftSubRight_of_section`: If the algebra map
  `R → S` has a section, then the sequence `R → S → S ⊗[R] S` is exact.
* `Algebra.TensorProduct.Exact.includeLeftSubRight_of_faithfullyFlat`: For a faithfully flat algebra
  `S` over `R`, the sequence `R → S → S ⊗[R] S` is exact.
* `Algebra.TensorProduct.toEqLocusOfInclusion_surjective`: When the exactness condition holds,
  the map from `R` to the equalizer locus is surjective.

-/

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R S : Type*} [CommSemiring R] [Ring S] [Algebra R S]

variable (R S) in
/-- The `R`-linear map `S →ₗ[R] S ⊗[R] S` sending `s : S` to `(s ⊗ₜ[R] 1) - (1 ⊗ₜ[R] s)`. -/
def includeLeftSubRight : S →ₗ[R] S ⊗[R] S :=
  (includeLeft (R := R) (S := R) (A := S) (B := S)).toLinearMap -
    (includeRight (R := R) (A:= S) (B := S)).toLinearMap

variable (R) in
/-- Explicit evaluation of `includeLeftSubRight R S` at `s : S`. -/
@[simp]
lemma includeLeftSubRight_apply (s : S) : includeLeftSubRight R S s = s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s :=
  rfl

/-- Evaluation of `includeLeftSubRight R S` at `s ∈ Set.range ⇑(Algebra.linearMap R S)` is zero. -/
lemma includeLeftSubRight_zero_of_mem_range {s : S} (hs : s ∈ Set.range ⇑(Algebra.linearMap R S)) :
    (includeLeftSubRight R S) s = 0 := by
  obtain ⟨_, hr⟩ := Set.mem_range.mp hs
  simp [includeLeftSubRight, ← hr]

/-- `includeLeftSubRight` is compatible with `distribBaseChange` and `lTensor`. -/
lemma includeLeftSubRight_distribBaseChange (S : Type*) [Ring S] [Algebra R S] (T : Type*)
    [CommRing T] [Algebra R T] : (includeLeftSubRight T (T ⊗[R] S)).restrictScalars R =
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).restrictScalars R).toLinearMap ∘ₗ
      ((includeLeftSubRight R S).lTensor T) := by
  simp only [includeLeftSubRight, LinearMap.lTensor_sub, LinearMap.comp_sub,
    distribBaseChange_includeLeft_lTensor, distribBaseChange_includeRight_lTensor]
  rfl

variable (R S) in
/-- For an `R`-algebra `S`, this `Prop` asserts that the maps
`algebraMap : R → S` and `includeLeftSubRight R S : S → S ⊗[R] S` form an exact pair. -/
def Exact.IncludeLeftSubRight : Prop :=
  Function.Exact ⇑(algebraMap R S) ⇑(includeLeftSubRight R S)

/-- For an `R`-algebra `S`, whenever `Algebra.ofId R S : R →ₐ[R] S` has an `R`-algebra section,
then the maps `R → S` and `includeLeftSubRight R S` form an exact pair. -/
lemma Exact.includeLeftSubRight_of_section (g : AlgHom R S R) :
    Exact.IncludeLeftSubRight R S := by
  intro s
  constructor
  · intro hs
    use g s
    apply (TensorProduct.lid R S).symm.injective
    rw [lid_symm_apply, lid_symm_apply, ← mul_one ((algebraMap R S) (g s)),
      ← Algebra.smul_def, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, ← id_eq (1 : S),
      ← AlgHom.coe_id R S, ← map_tmul,
      sub_eq_zero.mp ((includeLeftSubRight_apply R s).symm.trans hs), map_tmul, map_one,
      AlgHom.coe_id, id_eq]
  · exact includeLeftSubRight_zero_of_mem_range

section FaithfullyFlat

variable (R S : Type*) [CommRing R]

/-- For an `R`-algebra `S`, if there is a faithfully flat `R`-algebra `T` such that `T → T ⊗[R] S`
satisfies `Exact.IncludeLeftSubRight`, so does `R → S`. -/
lemma Exact.includeLeftSubRight_desc_faithfullyFlat [Ring S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    (h : Exact.IncludeLeftSubRight T (TensorProduct R T S)) :
    Exact.IncludeLeftSubRight R S := by
  refine Module.FaithfullyFlat.lTensor_reflects_exact R T _ _ <|
    AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      ((Algebra.linearMap R S).lTensor T).toAddMonoidHom
      ((includeLeftSubRight R S).lTensor T).toAddMonoidHom
      (Algebra.linearMap T (T ⊗[R] S)).toAddMonoidHom
      (includeLeftSubRight T (T ⊗[R] S)).toAddMonoidHom
      (TensorProduct.rid R R T).toAddMonoidHom
      (AddMonoidHom.id (T ⊗[R] S))
      (TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).toAddMonoidHom ?_ ?_
      (TensorProduct.rid R R T).surjective Function.bijective_id
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).injective)|>.mpr h
  · ext
    simp [← Algebra.TensorProduct.rid_lTensor]
  · change (((includeLeftSubRight T (T ⊗[R] S)).restrictScalars R).toAddMonoidHom).comp _ = _
    ext
    simp only [includeLeftSubRight_distribBaseChange]
    rfl

/-- The maps `R ⟶ S` and `includeLeftSubRight R S : S ⟶ S ⊗[R] S` form an exact pair for
any faithfully flat algebra `R S`. -/
lemma Exact.includeLeftSubRight_of_faithfullyFlat [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] : Exact.IncludeLeftSubRight R S :=
  Exact.includeLeftSubRight_desc_faithfullyFlat R S S
    (Exact.includeLeftSubRight_of_section (Algebra.TensorProduct.lmul'' R (S := S)))

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

/-- If the underlying ring map of an `R`-algebra `S` is injective, so is `toEqLocusOfInclusion`. -/
lemma toEqLocusOfInclusion_injective (h : Function.Injective (algebraMap R S)) :
    Function.Injective (toEqLocusOfInclusion R S) := by
  intro _ _ h_eq
  simp only [toEqLocusOfInclusion, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Subtype.mk.injEq] at h_eq
  exact h h_eq

/-- For an `R`-algebra `S` with `Exact.IncludeLeftSubRight` property, `toEqLocusOfInclusion` is
surjective. -/
lemma toEqLocusOfInclusion_surjective (h : Exact.IncludeLeftSubRight R S) :
    Function.Surjective (toEqLocusOfInclusion R S) := by
  intro s
  have s_mem : s.val ∈ Set.range ⇑(Algebra.linearMap R S) :=
    (h s.val).mp ((includeLeftSubRight_apply R s.val).symm ▸ sub_eq_zero.mpr s.property)
  use (Set.mem_range.mp s_mem).choose
  ext
  nth_rw 5 [← (Set.mem_range.mp s_mem).choose_spec]
  simp [toEqLocusOfInclusion]

end FaithfullyFlat

end Algebra.TensorProduct
