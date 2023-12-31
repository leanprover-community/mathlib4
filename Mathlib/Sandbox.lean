import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Ideal.Norm

section extendScalars

open FiniteDimensional Submodule

--- Generalize?
variable {ι R K : Type*} [Fintype ι] [Nonempty ι] [CommRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [CommRing V] [Algebra R V] [Module K V] {M : Submodule R V}
  [IsScalarTower R K V] (b : Basis ι R M) (h : Fintype.card ι = finrank K V)

/-- Docstring -/
noncomputable def Basis.extendScalars : Basis ι K V :=
  basisOfLinearIndependentOfCardEqFinrank
    ((LinearIndependent.iff_fractionRing R K).mp <|
      LinearIndependent.map' b.linearIndependent _ (ker_subtype M)) h

@[simp]
theorem Basis.extendScalars_apply (i : ι) : b.extendScalars h i = b i := by
  rw [Basis.extendScalars, coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply,
    coeSubtype]

theorem Basis.extendScalars_repr_apply (m : M) (i : ι) :
    (b.extendScalars h).repr (m : V) i = algebraMap R K (b.repr m i) := by
  suffices ((b.extendScalars h).repr.toLinearMap.restrictScalars R) ∘ₗ M.subtype =
    Finsupp.mapRange.linearMap (Algebra.linearMap R K) ∘ₗ b.repr.toLinearMap
      from FunLike.congr_fun (LinearMap.congr_fun this m) i
  refine Basis.ext b fun i ↦ ?_
  simp_rw [extendScalars, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, coeSubtype, ← b.extendScalars_apply h i, extendScalars, repr_self,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]

theorem Basis.extendScalars_mem_span  (x : V) :
    x ∈ span R (Set.range (b.extendScalars h)) ↔ x ∈ M := by
  rw [Basis.mem_span_iff_repr_mem]
  refine ⟨fun hx ↦ ?_, fun hx i ↦ ?_⟩
  · rw [← (b.extendScalars h).sum_repr x]
    conv =>
      congr; congr; rfl; ext i
      rw [← (hx i).choose_spec, ← algebra_compatible_smul]
    refine Submodule.sum_smul_mem _ _ (fun _ _ ↦ ?_)
    rw [Basis.extendScalars_apply]
    exact coe_mem (b _)
  · exact ⟨b.repr ⟨x, hx⟩ i, by rw [← Basis.extendScalars_repr_apply]⟩

end extendScalars

section Ring

open scoped nonZeroDivisors

variable (R : Type*) [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] (I : (Ideal R)⁰)

instance : Nontrivial I :=
  Submodule.nontrivial_iff_ne_bot.mpr <| mem_nonZeroDivisors_iff_ne_zero.mp I.2

instance : Top (Ideal R)⁰ := {
  top := ⟨⊤, by
      rw [mem_nonZeroDivisors_iff_ne_zero, show (0 : Ideal R) = ⊥ by rfl, Submodule.ne_bot_iff]
      exact ⟨1, trivial, one_ne_zero⟩⟩ }

instance : OrderTop (Ideal R)⁰ := ⟨fun _ ↦ Subtype.coe_le_coe.mp le_top⟩

theorem Ideal.nonZeroDivisors_coe_top : ((⊤ : (Ideal R)⁰) : Ideal R) = ⊤ := rfl

end Ring

section Ideal

open Module
open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.Free R S] [Module.Finite R S]  (I : (Ideal S))

instance : Module.Free R I := by
  by_cases hI : I = ⊥
  · have : Subsingleton I := Submodule.subsingleton_iff_eq_bot.mpr hI
    exact Module.Free.of_subsingleton R I
  · exact Free.of_basis (I.selfBasis (Free.chooseBasis R S) hI)

instance : Module.Finite R I := by
  by_cases hI : I = ⊥
  · have : Subsingleton I := Submodule.subsingleton_iff_eq_bot.mpr hI
    exact IsNoetherian.finite R ↥I
  · exact Finite.of_basis (I.selfBasis (Free.chooseBasis R S) hI)

end Ideal

open NumberField FiniteDimensional Module

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

open scoped nonZeroDivisors BigOperators

variable (I : (Ideal (𝓞 K))⁰)

attribute [local instance 2000] inst_ringOfIntegersAlgebra Algebra.toSMul Algebra.toModule
  Submodule.module

theorem ideal_rank_eq : finrank ℤ I = finrank ℤ (𝓞 K) := by
  let b := (I.1.selfBasis (RingOfIntegers.basis K) (mem_nonZeroDivisors_iff_ne_zero.mp I.2))
  rw [finrank_eq_card_basis b, finrank_eq_card_chooseBasisIndex]

noncomputable def Ideal.basis :
    Basis (Free.ChooseBasisIndex ℤ I) ℤ (I : Ideal (𝓞 K)) := Free.chooseBasis ℤ I

noncomputable def idealBasis :
    Basis (Free.ChooseBasisIndex ℤ I) ℚ K := by
  have : Function.Injective
      ((Subalgebra.val (𝓞 K)).toLinearMap ∘ₗ ((Submodule.subtype I.1).restrictScalars ℤ)) := by
    exact Subtype.val_injective.comp Subtype.val_injective
  refine Basis.extendScalars ((Ideal.basis K I).map (LinearEquiv.ofInjective _ this)) ?_
  rw [← finrank_eq_card_chooseBasisIndex, ideal_rank_eq, RingOfIntegers.rank]

theorem idealBasis_apply (i : Free.ChooseBasisIndex ℤ I) :
    idealBasis K I i = algebraMap (𝓞 K) K (Ideal.basis K I i) := by
  simp only [idealBasis, Basis.extendScalars_apply, Basis.map_apply, LinearEquiv.ofInjective_apply,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Submodule.coeSubtype, Function.comp_apply,
    AlgHom.toLinearMap_apply, Subalgebra.coe_val]
  rfl

theorem mem_span_idealBasis {x : K} :
    x ∈ Submodule.span ℤ (Set.range (idealBasis K I)) ↔ x ∈ algebraMap (𝓞 K) K '' I := by
  simp_rw [idealBasis, Basis.extendScalars_mem_span, LinearMap.mem_range, Set.mem_image,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, Submodule.coeSubtype,
    AlgHom.toLinearMap_apply, Subalgebra.coe_val]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, Subtype.mem x, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem det_idealBasis_eq_ideal_absNorm
    (e : (Free.ChooseBasisIndex ℤ (𝓞 K)) ≃ (Free.ChooseBasisIndex ℤ I)) :
    |(integralBasis K).det ((idealBasis K I).reindex e.symm)| = Ideal.absNorm (I : Ideal (𝓞 K)) := by
  have := Ideal.natAbs_det_basis_change (RingOfIntegers.basis K) I.1 ((Ideal.basis K I).reindex e.symm)
  have := congr_arg ((↑) : ℕ → ℚ) this
  rw [← this, Int.cast_natAbs, Int.cast_abs]
  rw [Basis.det_apply, Basis.det_apply]
  change _ = |(algebraMap ℤ ℚ) _|
  simp_rw [RingHom.map_det (algebraMap ℤ ℚ), Basis.coe_reindex, Equiv.symm_symm]
  congr!
  ext : 2
  rw [Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply,
    Function.comp_apply, idealBasis_apply]
  erw [integralBasis_repr_apply]
  rfl

theorem ideal_absNorm_ne_zero : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 := by
  let e : (Free.ChooseBasisIndex ℤ (𝓞 K)) ≃ (Free.ChooseBasisIndex ℤ I) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex, ideal_rank_eq]
  rw [← Nat.cast_ne_zero (R := ℚ)]
  rw [← det_idealBasis_eq_ideal_absNorm K I e, ne_eq, abs_eq_zero, ← ne_eq]
  exact IsUnit.ne_zero (Basis.isUnit_det (integralBasis K) _)
