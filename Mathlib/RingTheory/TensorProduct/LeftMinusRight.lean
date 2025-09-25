/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Some properties of `TensorProduct.includeLeft` minus `TensorProduct.includeRight` for rings

For an `R`-algebra `S`,
we collect some properties regarding the `R`-linear map `S →ₗ[R] S ⊗[R] S` sending
`s : S` to `s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s`.

-/

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R S : Type*} [CommSemiring R] [Ring S] [Algebra R S]

variable (R S) in
/-- The `R`-linear map `S →ₗ[R] S ⊗[R] S` sending `s : S` to `(s ⊗ₜ[R] 1) - (1 ⊗ₜ[R] s)`. -/
def leftMinusRight : S →ₗ[R] S ⊗[R] S :=
  (includeLeft (R := R) (S := R) (A := S) (B := S)).toLinearMap -
    (includeRight (R := R) (A:= S) (B := S)).toLinearMap

variable (R) in
/-- Evaluation of `leftMinusRight R S` at `s : S` as `tmul`. -/
@[simp]
lemma leftMinusRight_apply (s : S) : leftMinusRight R S s = s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s :=
  rfl

/-- Evaluation of `leftMinusRight R S` at `s ∈ Set.range ⇑(Algebra.linearMap R S)` is zero. -/
lemma leftMinusRight_zero_of_range {s : S} (hs : s ∈ Set.range ⇑(Algebra.linearMap R S)) :
    (leftMinusRight R S) s = 0 := by
  obtain ⟨_, hr⟩ := Set.mem_range.mp hs
  simp [leftMinusRight, ← hr]

/-- `leftMinusRight` is compatible with `distribBaseChange` and `lTensor`. -/
lemma leftMinusRight_distribBaseChange (S : Type*) [Ring S] [Algebra R S] (T : Type*)
    [CommRing T] [Algebra R T] : (leftMinusRight T (T ⊗[R] S)).restrictScalars R =
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).restrictScalars R).toLinearMap ∘ₗ
      ((leftMinusRight R S).lTensor T) := by
  simp only [leftMinusRight, LinearMap.lTensor_sub, LinearMap.comp_sub,
    distribBaseChange_includeLeft_lTensor, distribBaseChange_includeRight_lTensor]
  rfl

variable (R S) in
/-- For an `R`-algebra `S`, this `Prop` asserts that the maps
`algebraMap : R → S` and `leftMinusRight R S : S → S ⊗[R] S` form an exact pair. -/
def ExactLeftMinusRight : Prop :=
  Function.Exact ⇑(algebraMap R S) ⇑(leftMinusRight R S)

/-- For an `R`-algebra `S`, whenever `Algebra.ofId R S : R →ₐ[R] S` has an `R`-algebra section,
then the maps `R → S` and `leftMinusRight R S` form an exact pair. -/
lemma exactLeftMinusRight_of_section (g : AlgHom R S R) :
    ExactLeftMinusRight R S := by
  intro s
  constructor
  · intro hs
    use g s
    apply (TensorProduct.lid R S).symm.injective
    rw [lid_symm_apply, lid_symm_apply, ← mul_one ((algebraMap R S) (g s)),
      ← Algebra.smul_def, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, ← id_eq (1 : S),
      ← AlgHom.coe_id R S, ← map_tmul, sub_eq_zero.mp ((leftMinusRight_apply R s).symm.trans hs),
      map_tmul, map_one, AlgHom.coe_id, id_eq]
  · exact leftMinusRight_zero_of_range

section FaithfullyFlat

variable (R S : Type*) [CommRing R]

/-- For an `R`-algebra `S`, if there is a faithfully flat `R`-algebra `T` such that
`T → T ⊗[R] S` is `ExactLeftMinusRight`, then `R → S` is `ExactLeftMinusRight` as well. -/
lemma ExactLeftMinusRight.desc_faithfullyFlat [Ring S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    (h : ExactLeftMinusRight T (TensorProduct R T S)) :
    ExactLeftMinusRight R S := by
  refine Module.FaithfullyFlat.lTensor_reflects_exact R T _ _ <|
    AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      ((Algebra.linearMap R S).lTensor T).toAddMonoidHom
      ((leftMinusRight R S).lTensor T).toAddMonoidHom
      (Algebra.linearMap T (T ⊗[R] S)).toAddMonoidHom
      (leftMinusRight T (T ⊗[R] S)).toAddMonoidHom
      (TensorProduct.rid R R T).toAddMonoidHom
      (AddMonoidHom.id (T ⊗[R] S))
      (TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).toAddMonoidHom ?_ ?_
      (TensorProduct.rid R R T).surjective Function.bijective_id
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).injective)|>.mpr h
  · ext
    simp [← Algebra.TensorProduct.rid_lTensor]
  · change (((leftMinusRight T (T ⊗[R] S)).restrictScalars R).toAddMonoidHom).comp _ = _
    ext
    simp only [leftMinusRight_distribBaseChange]
    rfl

/-- The maps `R ⟶ S` and `leftMinusRight R S : S ⟶ S ⊗[R] S` form an exact pair for
any faithfully flat algebra `R S`. -/
lemma ExactLeftMinusRight.of_faithfullyFlat [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] :
    ExactLeftMinusRight R S :=
  ExactLeftMinusRight.desc_faithfullyFlat R S S
    (exactLeftMinusRight_of_section (Algebra.TensorProduct.lmul'' R (S := S)))

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- For an `R`-algebra `S`, the canonical ring map from `R` to the equalizer locus of
`s ↦ s ⊗ₜ (1 : S)` and `s ↦ (1 : S) ⊗ₜ s`. -/
def toEqLocus : R →+* (CommRingCat.pushoutCocone R S S).inl.hom.eqLocus
    (CommRingCat.pushoutCocone R S S).inr.hom where
  toFun r := Subtype.mk (algebraMap R S r) (by simp [RingHom.eqLocus, tmul_one_eq_one_tmul])
  map_zero' := by apply Subtype.ext; simp
  map_one' := by apply Subtype.ext; simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp

/-- If the underlying ring map of an `R`-algebra `S` is injective, so is `toEqLocus`. -/
lemma toEqLocus.inj (h : Function.Injective (algebraMap R S)) :
    Function.Injective (toEqLocus R S) := by
  intro _ _ h_eq
  simp only [toEqLocus, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.mk.injEq] at h_eq
  exact h h_eq

/-- For an `R`-algebra `S` with `ExactLeftMinusRight` property, `toEqLocus` is surjective. -/
lemma toEqLocus.surj (h : ExactLeftMinusRight R S) : Function.Surjective (toEqLocus R S) := by
  intro s
  have s_mem : s.val ∈ Set.range ⇑(Algebra.linearMap R S) :=
    (h s.val).mp ((leftMinusRight_apply R s.val).symm ▸ sub_eq_zero.mpr s.property)
  use (Set.mem_range.mp s_mem).choose
  ext
  nth_rw 5 [← (Set.mem_range.mp s_mem).choose_spec]
  simp [toEqLocus]

end FaithfullyFlat

end Algebra.TensorProduct
