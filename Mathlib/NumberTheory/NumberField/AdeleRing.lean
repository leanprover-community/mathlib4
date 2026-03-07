/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.Ideal.Int

/-!
# The adele ring of a number field

This file contains the formalisation of the adele ring of a number field as the
direct product of the infinite adele ring and the finite adele ring.

## Main definitions

- `NumberField.AdeleRing K` is the adele ring of a number field `K`.
- `NumberField.AdeleRing.principalSubgroup K` is the subgroup of principal adeles `(x)ᵥ`.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
adele ring, number field
-/

@[expose] public section

noncomputable section

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

/-! ## The adele ring  -/

/-- `AdeleRing (𝓞 K) K` is the adele ring of a number field `K`.

More generally `AdeleRing R K` can be used if `K` is the field of fractions
of the Dedekind domain `R`. This enables use of rings like `AdeleRing ℤ ℚ`, which
in practice are easier to work with than `AdeleRing (𝓞 ℚ) ℚ`.

Note that this definition does not give the correct answer in the function field case.
-/
def AdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] := InfiniteAdeleRing K × FiniteAdeleRing R K

namespace AdeleRing

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

instance : CommRing (AdeleRing R K) := Prod.instCommRing

instance : Inhabited (AdeleRing R K) := ⟨0⟩

instance : TopologicalSpace (AdeleRing R K) := instTopologicalSpaceProd

instance : IsTopologicalRing (AdeleRing R K) := instIsTopologicalRingProd

instance : Algebra K (AdeleRing R K) := Prod.algebra _ _ _

@[simp]
theorem algebraMap_fst_apply (x : K) (v : InfinitePlace K) :
    (algebraMap K (AdeleRing R K) x).1 v = x := rfl

theorem algebraMap_fst_def (x : K) :
    (algebraMap K (AdeleRing R K) x).1 = algebraMap K (InfiniteAdeleRing K) x := rfl

@[simp]
theorem algebraMap_snd_apply (x : K) (v : HeightOneSpectrum R) :
    (algebraMap K (AdeleRing R K) x).2 v = x := rfl

theorem algebraMap_snd_def (x : K) :
    (algebraMap K (AdeleRing R K) x).2 = algebraMap K (FiniteAdeleRing R K) x := rfl

theorem algebraMap_injective [NumberField K] : Function.Injective (algebraMap K (AdeleRing R K)) :=
  fun _ _ hxy => (algebraMap K _).injective (Prod.ext_iff.1 hxy).1

/-- The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`. -/
abbrev principalSubgroup : AddSubgroup (AdeleRing R K) := (algebraMap K _).range.toAddSubgroup

end AdeleRing

section norm

variable {K : Type*} [Field K] [NumberField K]

namespace AdeleRing

set_option backward.isDefEq.respectTransparency false in
theorem isUnit_iff {x : AdeleRing (𝓞 K) K} :
    IsUnit x ↔ (∀ v, x.1 v ≠ 0) ∧ (∀ v, x.2 v ≠ 0) ∧
      ∀ᶠ v in Filter.cofinite, Valued.v (x.2 v) = 1 := by
  rw [Prod.isUnit_iff, Pi.isUnit_iff, FiniteAdeleRing.isUnit_iff]
  simp_rw [isUnit_iff_ne_zero]

instance : Norm (AdeleRing (𝓞 K) K) where norm x := ‖x.1‖ * ‖x.2‖

theorem norm_def (x : AdeleRing (𝓞 K) K) : ‖x‖ = ‖x.1‖ * ‖x.2‖ := rfl

theorem norm_def_unit (x : (AdeleRing (𝓞 K) K)ˣ) :
    ‖x.1‖ = ‖x.1.1‖ * ‖(MulEquiv.prodUnits x).2.1‖ := rfl

theorem norm_apply_unit (x : (AdeleRing (𝓞 K) K)ˣ) :
    ‖x.1‖ = (∏ v, ‖x.1.1 v‖ ^ v.mult) * ∏ᶠ v, ‖(MulEquiv.prodUnits x).2.1 v‖ := by
  rw [norm_def_unit, FiniteAdeleRing.norm_def_unit]
  rfl

theorem norm_eq_zero_of_not_isUnit {x : AdeleRing (𝓞 K) K} (hx : ¬IsUnit x) : ‖x‖ = 0 := by
  rcases not_and_or.1 <| Prod.isUnit_iff.not.1 hx with hi | hf
  · simp [norm_def, InfiniteAdeleRing.norm_eq_zero_of_not_isUnit hi]
  · simp [norm_def, FiniteAdeleRing.norm_eq_zero_of_not_isUnit hf]

variable (K) in
/-- The global embedding of the units of `K` into the units of `AdeleRing (𝓞 K) K`. -/
def unitEmbedding : Kˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K))

@[simp] theorem unitEmbedding_apply (k : Kˣ) :
    unitEmbedding K k = algebraMap K (AdeleRing (𝓞 K) K) k := rfl

theorem unitEmbedding_prodUnits_apply (k : Kˣ) :
    (MulEquiv.prodUnits (unitEmbedding K k)).2 = k := rfl

theorem unitEmbedding_norm_eq_one {x : Kˣ} :
    ‖(unitEmbedding K x).1‖ = 1 := by
  rw [norm_def_unit, unitEmbedding_apply, algebraMap_fst_def, unitEmbedding_prodUnits_apply,
    InfiniteAdeleRing.coe_norm_eq_abs_norm, FiniteAdeleRing.unitEmbedding_norm_eq_inv_abs_norm]
  simp

end AdeleRing

end norm

end NumberField
