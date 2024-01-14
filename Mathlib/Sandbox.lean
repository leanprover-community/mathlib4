import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.RingTheory.Localization.Module

open NumberField FiniteDimensional Module

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

open scoped nonZeroDivisors BigOperators

-- change to fractionalideal
variable (I : (Ideal (𝓞 K))⁰)

attribute [local instance 2000] inst_ringOfIntegersAlgebra Algebra.toSMul Algebra.toModule
  Submodule.module

theorem ideal_rank_eq : finrank ℤ I = finrank ℤ (𝓞 K) := by
  let b := (I.1.selfBasis (RingOfIntegers.basis K) (mem_nonZeroDivisors_iff_ne_zero.mp I.2))
  rw [finrank_eq_card_basis b, finrank_eq_card_chooseBasisIndex]

theorem ideal_absNorm_ne_zero : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 := by
  rw [ne_eq, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
  exact mem_nonZeroDivisors_iff_ne_zero.mp I.2

noncomputable def Ideal.basis :
    Basis (Free.ChooseBasisIndex ℤ I) ℤ (I : Ideal (𝓞 K)) := Free.chooseBasis ℤ I

instance : IsLocalizedModule ℤ⁰
    ((Subalgebra.val (𝓞 K)).toLinearMap ∘ₗ ((Submodule.subtype I.1).restrictScalars ℤ)) := by
  constructor
  · intro x
    rw [← (Algebra.lmul _ _).commutes, Algebra.lmul_isUnit_iff, isUnit_iff_ne_zero, eq_intCast,
      Int.cast_ne_zero]
    exact nonZeroDivisors.coe_ne_zero x
  · intro x
    obtain ⟨⟨a, ⟨_, ⟨d, hd, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) x
    refine ⟨⟨⟨Ideal.absNorm I.1 * a, ?_⟩, ?_⟩ , ?_⟩
    · exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem I.1)
    · refine ⟨d * Ideal.absNorm I.1, ?_⟩
      refine Submonoid.mul_mem _ hd ?_
      refine mem_nonZeroDivisors_of_ne_zero ?_
      rw [Nat.cast_ne_zero]
      exact ideal_absNorm_ne_zero K _
    dsimp at h ⊢
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, SubringClass.coe_natCast]
    rw [show (a : K) = algebraMap (𝓞 K) K a by rfl, ← h]
    simp only [map_intCast]
    ring_nf
  · intro x y h
    use 1
    rw [one_smul, one_smul]
    rwa [Function.Injective.eq_iff] at h
    rw [LinearMap.coe_comp]
    refine Function.Injective.comp ?_ (Submodule.injective_subtype _)
    exact Subtype.val_injective

noncomputable def idealBasis :
    Basis (Free.ChooseBasisIndex ℤ I) ℚ K := by
  let f := ((Subalgebra.val (𝓞 K)).toLinearMap ∘ₗ ((Submodule.subtype I.1).restrictScalars ℤ))
  exact (Ideal.basis K I).ofIsLocalizedModule ℚ ℤ⁰ f

theorem idealBasis_apply (i : Free.ChooseBasisIndex ℤ I) :
    idealBasis K I i = algebraMap (𝓞 K) K (Ideal.basis K I i) := by
  exact (Ideal.basis K I).ofIsLocalizedModule_apply ℚ ℤ⁰ _ i

theorem mem_span_idealBasis {x : K} :
    x ∈ Submodule.span ℤ (Set.range (idealBasis K I)) ↔ x ∈ algebraMap (𝓞 K) K '' I := by
  rw [idealBasis, (Ideal.basis K I).ofIsLocalizedModule_span ℚ ℤ⁰ _]
  simp_rw [LinearMap.mem_range,  LinearMap.coe_comp, LinearMap.coe_restrictScalars, Set.mem_image,
    Submodule.coeSubtype, Function.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.coe_val]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem det_idealBasis_eq_ideal_absNorm
    (e : (Free.ChooseBasisIndex ℤ (𝓞 K)) ≃ (Free.ChooseBasisIndex ℤ I)) :
    |(integralBasis K).det ((idealBasis K I).reindex e.symm)| =
      Ideal.absNorm (I : Ideal (𝓞 K)) := by
  have := Ideal.natAbs_det_basis_change (RingOfIntegers.basis K) I.1
    ((Ideal.basis K I).reindex e.symm)
  have := congr_arg ((↑) : ℕ → ℚ) this
  rw [← this, Int.cast_natAbs, Int.cast_abs]
  rw [Basis.det_apply, Basis.det_apply]
  change _ = |(algebraMap ℤ ℚ) _|
  simp_rw [RingHom.map_det (algebraMap ℤ ℚ), Basis.coe_reindex, Equiv.symm_symm]
  congr
  ext : 2
  rw [Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply]
  simp_rw [Function.comp_apply, idealBasis_apply]
  erw [integralBasis_repr_apply]
