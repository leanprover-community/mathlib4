/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/

import Mathlib.RingTheory.HopfAlgebra

/-!
# Sweedler notations for co/bi/hopf algebras

-/

namespace SweedlerNotation

open TensorProduct BigOperators Coalgebra HopfAlgebra

section

variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
variable {F : Type*} [FunLike F A (A ⊗[R] A)] [LinearMapClass F R A (A ⊗[R] A)] (comul : F)

lemma abstract_comul_exists_repr (x : A) :
    ∃ (I : Finset (A ⊗[R] A)) (Δ₁ Δ₂: A ⊗[R] A → A),
      comul x = ∑ i in I, Δ₁ i ⊗ₜ Δ₂ i := by
  classical
  have mem1 : comul x ∈ (⊤ : Submodule R (A ⊗[R] A)) := ⟨⟩
  rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem1
  obtain ⟨r, hr, (eq1 : ∑ i in r.support, (_ • _) = _)⟩ := mem1
  choose a a' haa' using hr
  replace eq1 := calc _
    comul x = ∑ i in r.support, r i • i := eq1.symm
    _ = ∑ i in r.support.attach, (r i : R) • i.1 := Finset.sum_attach _ _ |>.symm
    _ = ∑ i in r.support.attach, (r i • a i.2 ⊗ₜ[R] a' i.2) :=
        Finset.sum_congr rfl fun i _ ↦ congr(r i.1 • $(haa' i.2)).symm
    _ = ∑ i in r.support.attach, ((r i • a i.2) ⊗ₜ[R] a' i.2) :=
        Finset.sum_congr rfl fun i _ ↦ TensorProduct.smul_tmul' _ _ _
  refine ⟨r.support, fun i ↦ if h : i ∈ r.support then r i • a h else 0,
    fun i ↦ if h : i ∈ r.support then a' h else 0, eq1 ▸ ?_⟩
  conv_rhs => rw [← Finset.sum_attach]
  exact Finset.sum_congr rfl fun _ _ ↦ (by aesop)

/-- an arbitrarily chosen indexing set for comul(a) = ∑ a₁ ⊗ a₂. -/
noncomputable def ℐ (a : A) : Finset (A ⊗[R] A) := abstract_comul_exists_repr comul a |>.choose

/-- an arbitrarily chosen first coordinate for comul(a) = ∑ a₁ ⊗ a₂. -/
noncomputable def Δ₁ (a : A) : A ⊗[R] A → A := abstract_comul_exists_repr comul a |>.choose_spec.choose

/-- an arbitrarily chosen second coordinate for comul(a) = ∑ a₁ ⊗ a₂. -/
noncomputable def Δ₂ (a : A) : A ⊗[R] A → A :=
  abstract_comul_exists_repr comul a |>.choose_spec.choose_spec.choose

lemma abstract_comul_repr (a : A) :
    comul a = ∑ i in ℐ comul a, Δ₁ comul a i ⊗ₜ[R] Δ₂ comul a i :=
  abstract_comul_exists_repr comul a |>.choose_spec.choose_spec.choose_spec

end

section Coalgebra

variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

lemma sum_counit_tmul_eq_one_tmul (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i in s, x i ⊗ₜ[R] y i) :
    ∑ i in s, counit (R := R) (x i) ⊗ₜ y i = 1 ⊗ₜ[R] a := by
  simpa [repr, map_sum] using congr($(rTensor_counit_comp_comul (R := R) (A := A)) a)

lemma sum_tmul_counit_eq_tmul_one (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i in s, x i ⊗ₜ[R] y i) :
    ∑ i in s, (x i) ⊗ₜ counit (R := R) (y i) = a ⊗ₜ[R] 1 := by
  simpa [repr, map_sum] using congr($(lTensor_counit_comp_comul (R := R) (A := A)) a)

end Coalgebra

section HopfAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

lemma sum_antipode_mul_eq_algebraMap_counit (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i in s, x i ⊗ₜ[R] y i) :
    ∑ i in s, antipode (R := R) (x i) * y i = algebraMap R A (counit a) := by
  simpa [repr, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)

lemma sum_mul_antipode_eq_algebraMap_counit (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i in s, x i ⊗ₜ[R] y i) :
    ∑ i in s, x i * antipode (R := R) (y i) = algebraMap R A (counit a) := by
  simpa [repr, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

lemma sum_antipode_mul_eq_smul (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i in s, x i ⊗ₜ[R] y i) :
    ∑ i in s, antipode (R := R) (x i) * y i = (counit (R := R) a) • 1 := by
  rw [sum_antipode_mul_eq_algebraMap_counit (repr := repr), Algebra.smul_def, mul_one]

lemma sum_mul_antipode_eq_smul (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i in s, x i ⊗ₜ[R] y i) :
    ∑ i in s, x i * antipode (R := R) (y i) = (counit (R := R) a) • 1 := by
  rw [sum_mul_antipode_eq_algebraMap_counit (repr := repr), Algebra.smul_def, mul_one]

end HopfAlgebra

end SweedlerNotation
