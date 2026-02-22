/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Descent of finiteness conditions under faithfully flat maps

In this file we show that

- `Algebra.FiniteType`:
- `Algebra.FinitePresentation`:
- `Module.Finite`:

descend along faithfully flat base change.
-/

@[expose] public section

universe u v w

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (T : Type*) [CommRing T] [Algebra R T]

lemma Module.Finite.of_finite_tensorProduct_of_faithfullyFlat {M : Type*} [AddCommGroup M]
    [Module R M] [Module.FaithfullyFlat R T] [Module.Finite T (T ⊗[R] M)] :
    Module.Finite R M := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := T) (M := T ⊗[R] M)
  choose k t m h using fun i : Fin n ↦ TensorProduct.exists_sum_tmul_eq (s i)
  let f₀ : ((Σ i, Fin (k i)) → R) →ₗ[R] M := (Pi.basisFun R _).constr R fun ⟨i, j⟩ ↦ m i j
  apply of_surjective f₀
  have : Function.Surjective (AlgebraTensorModule.lTensor T T f₀) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le, Set.range_subset_iff]
    intro i
    use ∑ (j : Fin (k i)), t i j ⊗ₜ Pi.basisFun R _ ⟨i, j⟩
    simp [f₀, -Pi.basisFun_equivFun, -Pi.basisFun_apply, h i]
  rwa [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ T]

set_option backward.isDefEq.respectTransparency false in
lemma Ideal.FG.of_FG_map_of_faithfullyFlat [Module.FaithfullyFlat R S] {I : Ideal R}
    (hI : (I.map (algebraMap R S)).FG) : I.FG := by
  change Submodule.FG I
  rw [← Module.Finite.iff_fg]
  let f : S ⊗[R] I →ₗ[S] S :=
    (AlgebraTensorModule.rid _ _ _).toLinearMap ∘ₗ AlgebraTensorModule.lTensor S S I.subtype
  have hf : Function.Injective f := by simp [f]
  have : I.map (algebraMap R S) = LinearMap.range f := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      use 1 ⊗ₜ ⟨x, hx⟩
      simp [f, Algebra.smul_def]
    · rintro - ⟨x, rfl⟩
      induction x with
      | zero => simp
      | add _ _ _ _ => simp_all [Ideal.add_mem]
      | tmul s x =>
        have : f (s ⊗ₜ[R] x) = s • f (1 ⊗ₜ x) := by simp [f]
        rw [this]
        apply Ideal.mul_mem_left
        simpa [f, Algebra.smul_def] using Ideal.mem_map_of_mem _ x.2
  let e : S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) := .ofInjective _ hf ≪≫ₗ .ofEq _ _ this.symm
  have : Module.Finite S (S ⊗[R] ↥I) := by
    rwa [Module.Finite.equiv_iff e, Module.Finite.iff_fg]
  apply Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

namespace Algebra

/-- If `T ⊗[R] S` is of finite type over `T` and `T` is `R`-faithfully flat,
then `S` is of finite type over `R` -/
lemma FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat R T] [Algebra.FiniteType T (T ⊗[R] S)] :
    Algebra.FiniteType R S := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := T) (A := T ⊗[R] S)
  have (x : s) := TensorProduct.exists_sum_tmul_eq x.1
  choose k t m h using this
  let f : MvPolynomial (Σ x : s, Fin (k x)) R →ₐ[R] S := MvPolynomial.aeval (fun ⟨x, i⟩ ↦ m x i)
  apply Algebra.FiniteType.of_surjective f
  have hf : Function.Surjective (Algebra.TensorProduct.map (.id T T) f) := by
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← hs, adjoin_le_iff]
    intro x hx
    let i : s := ⟨x, hx⟩
    use ∑ (j : Fin (k i)), t i j ⊗ₜ MvPolynomial.X ⟨i, j⟩
    simp [f, ← h, i]
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ T _).mp hf

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- If `T ⊗[R] S` is of finite presentation over `T` and `T` is `R`-faithfully flat,
then `S` is of finite presentation over `R` -/
lemma FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat R T] [Algebra.FinitePresentation T (T ⊗[R] S)] :
    Algebra.FinitePresentation R S := by
  have : Algebra.FiniteType R S := .of_finiteType_tensorProduct_of_faithfullyFlat T
  rw [Algebra.FiniteType.iff_quotient_mvPolynomial''] at this
  obtain ⟨n, f, hf⟩ := this
  have : Module.FaithfullyFlat (MvPolynomial (Fin n) R) (T ⊗[R] MvPolynomial (Fin n) R) :=
    .of_linearEquiv _ _ (Algebra.TensorProduct.commRight _ _ _).symm.toLinearEquiv
  let fT := Algebra.TensorProduct.map (.id T T) f
  refine .of_surjective hf (.of_FG_map_of_faithfullyFlat (S := T ⊗[R] MvPolynomial (Fin n) R) ?_)
  have : (RingHom.ker f.toRingHom).map
      (algebraMap (MvPolynomial (Fin n) R) (T ⊗[R] MvPolynomial (Fin n) R)) = RingHom.ker fT :=
    (Algebra.TensorProduct.lTensor_ker f hf).symm
  rw [this]
  apply ker_fG_of_surjective
  exact FiniteType.baseChangeAux_surj T hf

end Algebra

namespace RingHom

lemma FiniteType.codescendsAlong_faithfullyFlat :
    CodescendsAlong FiniteType FaithfullyFlat := by
  refine .mk _ finiteType_respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [finiteType_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finiteType_tensorProduct_of_faithfullyFlat S

lemma FinitePresentation.codescendsAlong_faithfullyFlat :
    CodescendsAlong FinitePresentation FaithfullyFlat := by
  refine .mk _ finitePresentation_respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [finitePresentation_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finitePresentation_tensorProduct_of_faithfullyFlat S

lemma Finite.codescendsAlong_faithfullyFlat :
    CodescendsAlong Finite FaithfullyFlat := by
  refine .mk _ finite_respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [finite_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finite_tensorProduct_of_faithfullyFlat S

end RingHom
