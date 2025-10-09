/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.Valued.ValuationTopology
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

instance [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation R Γ₀} : Preorder (WithVal v) := v.toPreorder

end Instances

section Ring

variable [Ring R] (v : Valuation R Γ₀)

/-- Canonical ring equivalence between `WithVal v` and `R`. -/
def equiv : WithVal v ≃+* R := RingEquiv.refl _

/-- Canonical valuation on the `WithVal v` type synonym. -/
def valuation : Valuation (WithVal v) Γ₀ := v.comap (equiv v)

@[simp] lemma valuation_equiv_symm (x : R) : valuation v ((equiv v).symm x) = v x := rfl

/-- Canonical ring equivalence between `WithVal v` and `WithVal w`. -/
def equivWithVal {Γ'₀ : Type*} [LinearOrderedCommGroupWithZero Γ'₀]
    (v : Valuation R Γ₀) (w : Valuation R Γ'₀) :
    WithVal v ≃+* WithVal w :=
  (WithVal.equiv v).trans (WithVal.equiv w).symm

instance {R} [Ring R] (v : Valuation R Γ₀) : Valued (WithVal v) Γ₀ :=
  Valued.mk' (valuation v)

theorem apply_equiv (r : WithVal v) : v (equiv v r) = Valued.v r := rfl

@[simp] theorem apply_symm_equiv (r : R) : Valued.v ((equiv v).symm r) = v r := rfl

theorem le_def {v : Valuation R Γ₀} {a b : WithVal v} :
    a ≤ b ↔ v (equiv v a) ≤ v (equiv v b) := .rfl

theorem lt_def {v : Valuation R Γ₀} {a b : WithVal v} :
    a < b ↔ v (equiv v a) < v (equiv v b) := .rfl

@[simp]
theorem equiv_equivWithVal_apply {Γ'₀ : Type*} [LinearOrderedCommGroupWithZero Γ'₀]
    (v : Valuation R Γ₀) (w : Valuation R Γ'₀) (x : WithVal v) :
    equiv w (equivWithVal v w x) = equiv v x := rfl

@[simp]
theorem equiv_equivWithVal_symm_apply {Γ'₀ : Type*} [LinearOrderedCommGroupWithZero Γ'₀]
    (v : Valuation R Γ₀) (w : Valuation R Γ'₀) (x : WithVal w) :
    equiv v ((equivWithVal v w).symm x) = equiv w x := rfl

end Ring

section CommRing

variable [CommRing R] (v : Valuation R Γ₀)

instance : ValuativeRel (WithVal v) := .ofValuation (valuation v)
instance : (valuation v).Compatible := .ofValuation (valuation v)

end CommRing

end WithVal

/-! The completion of a field with respect to a valuation. -/

namespace Valuation

open WithVal

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

/-- The completion of a field with respect to a valuation. -/
abbrev Completion := UniformSpace.Completion (WithVal v)

instance : Coe R v.Completion :=
  inferInstanceAs <| Coe (WithVal v) (UniformSpace.Completion (WithVal v))

section Equivalence

/-! The uniform isomorphism between `WithVal v` and `WithVal w` when `v` and `w` are
equivalent. -/

variable {R Γ₀ Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀']

/-- If two valuations `v` and `w` are equivalent then `WithVal v` is order-isomorphic
to `WithVal w`. -/
def IsEquiv.orderRingIso [Ring R] {v : Valuation R Γ₀} {w : Valuation R Γ₀'} (h : v.IsEquiv w) :
    WithVal v ≃+*o WithVal w where
  __ := equivWithVal v w
  map_le_map_iff' := by
    intro a b
    simp [h.symm (equiv v a), le_def]

theorem IsEquiv.isUniformInducing_equivWithVal [DivisionRing R] {v : Valuation R Γ₀}
    {w : Valuation R Γ₀'} (hv : Function.Surjective v) (hw : Function.Surjective w)
    (h : v.IsEquiv w) : IsUniformInducing (equivWithVal v w) := by
  refine (isUniformInducing_iff _).2 <| Filter.ext fun u ↦ ?_
  simp only [Filter.mem_comap, (Valued.hasBasis_uniformity _ _).mem_iff, true_and]
  refine ⟨fun ⟨t, ⟨γ, hγ⟩, htu⟩ ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · obtain ⟨a, ha⟩ := hw γ
    have : v (equiv w ((equiv v).symm a)) ≠ 0 := by
      simpa [map_eq_zero (equiv v).symm] using
        fun ha₀ ↦ absurd (map_zero w ▸ ha₀ ▸ ha).symm (Units.ne_zero γ)
    refine ⟨.mk0 _ this, Set.Subset.trans (fun p hp ↦ Set.mem_preimage.2 ?_) htu⟩
    apply hγ
    rw [← ha]
    rw [Units.val_mk0, ← equiv_equivWithVal_symm_apply v] at hp
    change equivWithVal v w p.2 - equivWithVal v w p.1 < (equiv w).symm a
    change p.2 - p.1 < h.orderRingIso.symm ((equiv w).symm a) at hp
    simpa using h.orderRingIso.lt_symm_apply.1 hp
  · use Prod.map (equivWithVal v w) (equivWithVal v w) '' u
    have hinj : (Prod.map (equivWithVal v w) (equivWithVal v w)).Injective :=
      Prod.map_injective.2 ⟨(equivWithVal v w).injective, (equivWithVal v w).injective⟩
    refine ⟨?_, subset_of_eq <| hinj.preimage_image u⟩
    obtain ⟨a, ha⟩ := hv γ
    have : w (equiv v ((equiv w).symm a)) ≠ 0 := by
      simpa [map_eq_zero (equiv w).symm] using
        fun ha₀ ↦ absurd (map_zero v ▸ ha₀ ▸ ha).symm (Units.ne_zero γ)
    refine ⟨.mk0 _ this, ?_⟩
    refine Set.Subset.trans (fun p hp ↦ ?_) ((Set.image_subset_image_iff hinj).2 hγ)
    refine ⟨((equivWithVal v w).symm p.1, (equivWithVal v w).symm p.2), ?_, by simp⟩
    rw [← ha]
    rw [Units.val_mk0, ← equiv_equivWithVal_apply v w] at hp
    change p.2 - p.1 < h.orderRingIso ((equiv v).symm a) at hp
    change (equivWithVal v w).symm p.2 - (equivWithVal v w).symm p.1 < (equiv v).symm a
    simpa using h.orderRingIso.symm_apply_lt.2 hp

/-- If two valuations `v` and `w` are equivalent then `WithVal v` and `WithVal w` are
isomorphic as uniform spaces. -/
@[simps!]
def IsEquiv.uniformEquiv [DivisionRing R] {v : Valuation R Γ₀} {v' : Valuation R Γ₀'}
    (hv : Function.Surjective v) (hv' : Function.Surjective v') (h : v.IsEquiv v') :
    WithVal v ≃ᵤ WithVal v' :=
  Equiv.toUniformEquivOfIsUniformInducing (WithVal.equivWithVal v v')
    (h.isUniformInducing_equivWithVal hv hv')

end Equivalence

end Valuation

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (v : Valuation K Γ₀)

instance : CoeHead (𝓞 (WithVal v)) (WithVal v) := inferInstanceAs (CoeHead (𝓞 K) K)

instance : IsDedekindDomain (𝓞 (WithVal v)) := inferInstanceAs (IsDedekindDomain (𝓞 K))

instance (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    IsIntegralClosure R ℤ (WithVal v) := ‹IsIntegralClosure R ℤ K›

/-- The ring equivalence between `𝓞 (WithVal v)` and an integral closure of
`ℤ` in `K`. -/
@[simps!]
def withValEquiv (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    𝓞 (WithVal v) ≃+* R := NumberField.RingOfIntegers.equiv R

end NumberField.RingOfIntegers

open scoped NumberField in
/-- The ring of integers of `WithVal v`, when `v` is a valuation on `ℚ`, is
equivalent to `ℤ`. -/
@[simps! apply]
def Rat.ringOfIntegersWithValEquiv (v : Valuation ℚ Γ₀) : 𝓞 (WithVal v) ≃+* ℤ :=
  NumberField.RingOfIntegers.withValEquiv v ℤ
