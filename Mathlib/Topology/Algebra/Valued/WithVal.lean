/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Ring topologised by a valuation

For a given valuation `v : Valuation R Γ₀` on a ring `R` taking values in `Γ₀`, this file
defines the type synonym `WithVal v` of `R`. By assigning a `Valued (WithVal v) Γ₀` instance,
`WithVal v` represents the ring `R` equipped with the topology coming from `v`. The type
synonym `WithVal v` is in isomorphism to `R` as rings via `WithVal.equiv v`. This
isomorphism should be used to explicitly map terms of `WithVal v` to terms of `R`.

The `WithVal` type synonym is used to define the completion of `R` with respect to `v` in
`Valuation.Completion`. An example application of this is
`IsDedekindDomain.HeightOneSpectrum.adicCompletion`, which is the completion of the field of
fractions of a Dedekind domain with respect to a height-one prime ideal of the domain.

## Main definitions
- `WithVal` : type synonym for a ring equipped with the topology coming from a valuation.
- `WithVal.equiv` : the canonical ring equivalence between `WithValuation v` and `R`.
- `Valuation.Completion` : the uniform space completion of a field `K` according to the
  uniform structure defined by the specified valuation.
-/

noncomputable section

variable {R Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Type synonym for a ring equipped with the topology coming from a valuation. -/
@[nolint unusedArguments]
def WithVal [Ring R] : Valuation R Γ₀ → Type _ := fun _ => R

namespace WithVal

section Instances

variable {P S : Type*} [LinearOrderedCommGroupWithZero Γ₀]

instance [Ring R] (v : Valuation R Γ₀) : Ring (WithVal v) := inferInstanceAs (Ring R)

instance [CommRing R] (v : Valuation R Γ₀) : CommRing (WithVal v) := inferInstanceAs (CommRing R)

instance [Field R] (v : Valuation R Γ₀) : Field (WithVal v) := inferInstanceAs (Field R)

instance [Ring R] (v : Valuation R Γ₀) : Inhabited (WithVal v) := ⟨0⟩

instance [CommSemiring S] [CommRing R] [Algebra S R] (v : Valuation R Γ₀) :
    Algebra S (WithVal v) := inferInstanceAs (Algebra S R)

instance [CommRing S] [CommRing R] [Algebra S R] [IsFractionRing S R] (v : Valuation R Γ₀) :
    IsFractionRing S (WithVal v) := inferInstanceAs (IsFractionRing S R)

instance [Ring R] [SMul S R] (v : Valuation R Γ₀) : SMul S (WithVal v) :=
  inferInstanceAs (SMul S R)

instance [Ring R] [SMul P S] [SMul S R] [SMul P R] [IsScalarTower P S R] (v : Valuation R Γ₀) :
    IsScalarTower P S (WithVal v) :=
  inferInstanceAs (IsScalarTower P S R)

variable [CommRing R] (v : Valuation R Γ₀)

instance {S : Type*} [Ring S] [Algebra R S] :
    Algebra (WithVal v) S := inferInstanceAs (Algebra R S)

instance {S : Type*} [Ring S] [Algebra R S] (w : Valuation S Γ₀) :
    Algebra R (WithVal w) := inferInstanceAs (Algebra R S)

instance {P S : Type*} [Ring S] [Semiring P] [Module P R] [Module P S]
    [Algebra R S] [IsScalarTower P R S] :
    IsScalarTower P (WithVal v) S := inferInstanceAs (IsScalarTower P R S)

end Instances

variable [Ring R] (v : Valuation R Γ₀)

/-- Canonical ring equivalence between `WithVal v` and `R`. -/
def equiv : WithVal v ≃+* R := RingEquiv.refl _

instance {R} [Ring R] (v : Valuation R Γ₀) : Valued (WithVal v) Γ₀ :=
  Valued.mk' (v.comap (WithVal.equiv v))

@[simp]
theorem apply_equiv (r : WithVal v) :
    (Valued.v : Valuation (WithVal v) Γ₀) (WithVal.equiv v r) = v r :=
  rfl

@[simp]
theorem apply_symm_equiv (r : R) : v ((WithVal.equiv v).symm r) = v r := rfl

theorem equiv_symm_apply (r : R) : v ((WithVal.equiv v).symm r) = v r := rfl

end WithVal

/-! The completion of a field with respect to a valuation. -/

namespace Valuation

open WithVal

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

/-- The completion of a field with respect to a valuation. -/
def Completion := UniformSpace.Completion (WithVal v)

namespace Completion

instance : Ring v.Completion := UniformSpace.Completion.ring

instance : Inhabited v.Completion := ⟨0⟩

instance : Coe R v.Completion :=
  inferInstanceAs <| Coe (WithVal v) (UniformSpace.Completion (WithVal v))

instance : UniformSpace v.Completion :=
  UniformSpace.Completion.uniformSpace _

instance : CompleteSpace v.Completion :=
  UniformSpace.Completion.completeSpace _

instance {M : Type*} [SMul M (WithVal v)] : SMul M v.Completion :=
  UniformSpace.Completion.instSMul _ _

instance (M N : Type*) [SMul M (WithVal v)] [SMul N (WithVal v)] [SMul M N]
    [UniformContinuousConstSMul M (WithVal v)] [UniformContinuousConstSMul N (WithVal v)]
    [IsScalarTower M N (WithVal v)] :
    IsScalarTower M N v.Completion :=
  UniformSpace.Completion.instIsScalarTower M N (WithVal v)

variable {K : Type*} [Field K] (v : Valuation K Γ₀)

instance valued : Valued v.Completion Γ₀ := Valued.valuedCompletion

theorem valued_apply (x : WithVal v) : (valued v).v x = Valued.v x :=
  Valued.valuedCompletion_apply _

instance [CompletableTopField (WithVal v)] : Field v.Completion :=
  UniformSpace.Completion.instField

variable {S : Type*} [CommSemiring S] [Algebra S K]

variable (K) in
instance : UniformContinuousConstSMul S (WithVal v) := by
  refine ⟨fun l ↦ ?_⟩
  simp_rw [Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _

open UniformSpace in
instance : Algebra S v.Completion where
  algebraMap := Completion.coeRingHom.comp (algebraMap _ _)
  commutes' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_mul_left _) (continuous_mul_right _)
    | ih x =>
      change (↑(algebraMap S (WithVal v) r) : v.Completion) * x
        = x * (↑(algebraMap S (WithVal v) r) : v.Completion)
      norm_cast
      rw [Algebra.commutes]
  smul_def' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const_smul _) (continuous_mul_left _)
    | ih x =>
      change _ = (↑(algebraMap S (WithVal v) r) : v.Completion) * x
      norm_cast
      simp_rw [← Algebra.smul_def]
      rw [UniformSpace.Completion.coe_smul]

theorem coe_smul (r : S) (x : WithVal v) :
    (↑(r • x) : v.Completion) = r • (↑x : v.Completion) :=
  UniformSpace.Completion.coe_smul r x

theorem coe_algebraMap : ⇑(algebraMap S v.Completion) = (↑) ∘ algebraMap S K :=
  rfl

/-- The ring of integers of `Valuation.Completion`. -/
def integers [CompletableTopField (WithVal v)] : ValuationSubring v.Completion :=
  (valued v).v.valuationSubring

instance : Inhabited (valuationSubring v) := ⟨0⟩

theorem mem_integers {x : v.Completion} :
    x ∈ integers v ↔ Valued.v x ≤ 1 :=
  Iff.rfl

theorem not_mem_integers {x : v.Completion} :
    x ∉ integers v ↔ 1 < Valued.v x := by
  rw [not_congr <| mem_integers v]
  exact not_le

open scoped algebraMap in
theorem valued_eq_valuation (s : S) :
    Valued.v (s : v.Completion) = v s :=
  valued_apply v (s : K)

theorem valued_eq_valuation' (k : K) :
    Valued.v (k : v.Completion) = v k :=
  valued_eq_valuation v k

end Valuation.Completion

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] (v : Valuation K Γ₀)

instance : CoeHead (𝓞 (WithVal v)) (WithVal v) := inferInstanceAs (CoeHead (𝓞 K) K)

instance [NumberField K] : IsDedekindDomain (𝓞 (WithVal v)) :=
  inferInstanceAs (IsDedekindDomain (𝓞 K))

instance (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    IsIntegralClosure R ℤ (WithVal v) := ‹IsIntegralClosure R ℤ K›

/-- The ring equivalence between `𝓞 (WithVal v)` and an integral closure of
`ℤ` in `K`. -/
@[simps!]
def withValEquiv (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    𝓞 (WithVal v) ≃+* R := NumberField.RingOfIntegers.equiv R

theorem withValEquiv_symm_apply_coe (R : Type*) [CommRing R] [Algebra R K]
    [IsIntegralClosure R ℤ K] (x : R) :
    ((withValEquiv v R).symm x).1 = (algebraMap R (WithVal v) x) := by
  rw [withValEquiv_symm_apply, ← IsIntegralClosure.algebraMap_equiv ℤ R (WithVal v) (𝓞 (WithVal v))]
  rfl

@[simp]
theorem withVal_coe_eq_algebraMap (x : 𝓞 K) :
    algebraMap (𝓞 K) (WithVal v) x = (x : K) := rfl

end NumberField.RingOfIntegers

open scoped NumberField in
/-- The ring of integers of `WithVal v`, when `v` is a valuation on `ℚ`, is
equivalent to `ℤ`. -/
@[simps! apply]
def Rat.ringOfIntegersWithValEquiv (v : Valuation ℚ Γ₀) : 𝓞 (WithVal v) ≃+* ℤ :=
  NumberField.RingOfIntegers.withValEquiv v ℤ
