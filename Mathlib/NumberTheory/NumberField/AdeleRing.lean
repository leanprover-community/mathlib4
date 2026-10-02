/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

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

open AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

/-! ## The adele ring  -/

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- `AdeleRing (𝓞 K) K` is the adele ring of a number field `K`.

More generally `AdeleRing R K` can be used if `K` is the field of fractions
of the Dedekind domain `R`. This enables use of rings like `AdeleRing ℤ ℚ`, which
in practice are easier to work with than `AdeleRing (𝓞 ℚ) ℚ`.

Note that this definition does not give the correct answer in the function field case.
-/
def AdeleRing := InfiniteAdeleRing K × FiniteAdeleRing R K
deriving CommRing, TopologicalSpace, IsTopologicalRing, Algebra K

namespace AdeleRing

/-- `𝔸[R, K]` is notation for `NumberField.AdeleRing R K`. -/
scoped notation:max "𝔸[" R ", " K "]" => AdeleRing R K
/-- `𝔸[K]` is notation for `NumberField.AdeleRing (𝓞 K) K`. -/
scoped notation:max "𝔸[" K "]" => AdeleRing (𝓞 K) K

instance : Inhabited 𝔸[R, K] := ⟨0⟩

@[simp]
theorem algebraMap_fst_apply (x : K) (v : InfinitePlace K) :
    (algebraMap K 𝔸[R, K] x).1 v = x := rfl

@[simp]
theorem algebraMap_snd_apply (x : K) (v : HeightOneSpectrum R) :
    (algebraMap K 𝔸[R, K] x).2 v = x := rfl

theorem algebraMap_injective [NumberField K] : Function.Injective (algebraMap K 𝔸[R, K]) :=
  fun _ _ hxy => (algebraMap K K∞).injective (Prod.ext_iff.1 hxy).1

/-- The embedding of the completion `Kᵥ` at an infinite place `v` into the adele ring. -/
@[simps!]
def ofCompletion (v : InfinitePlace K) : v.Completion →* 𝔸[R, K] :=
  .prod (InfiniteAdeleRing.ofCompletion v) 1

/-- The embedding of the completion `Kᵥ` at a finite place `v` into the adele ring. -/
@[simps!]
def ofAdicCompletion (v : HeightOneSpectrum R) : v.adicCompletion K →* 𝔸[R, K] :=
  .prod 1 (FiniteAdeleRing.ofAdicCompletion K v)

/-- The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`. -/
abbrev principalSubgroup : AddSubgroup 𝔸[R, K] := (algebraMap K 𝔸[R, K]).range.toAddSubgroup

end AdeleRing

open scoped AdeleRing

/-- The idele group is the group of units of the adele ring. -/
abbrev IdeleGroup := 𝔸[R, K]ˣ

namespace IdeleGroup

/-- The map from `Kˣ` to the idele group of `K`. The image is the subgroup of principal ideles. -/
@[simps!]
def unitEmbedding : Kˣ →* IdeleGroup R K :=
  Units.map (algebraMap K 𝔸[R, K]).toMonoidHom

/-- The map from the completion `Kᵥ` at an infinite place `v` to the idele group. -/
@[simps!]
def ofCompletion (v : InfinitePlace K) : v.Completionˣ →* IdeleGroup R K :=
  Units.map (AdeleRing.ofCompletion R K v)

/-- The map from the completion `Kᵥ` at a finite place `v` to the idele group. -/
@[simps!]
def ofAdicCompletion (v : HeightOneSpectrum R) : (v.adicCompletion K)ˣ →* IdeleGroup R K :=
  Units.map (AdeleRing.ofAdicCompletion R K v)

/-- The subgroup of principal ideles `(x)ᵥ` where `x ∈ Kˣ`. -/
abbrev principalSubgroup : Subgroup (IdeleGroup R K) :=
  (IdeleGroup.unitEmbedding R K).range

end IdeleGroup

/-- The idele class group is the quotient of the idele group by the subgroup of principal ideles. -/
abbrev IdeleClassGroup := IdeleGroup R K ⧸ IdeleGroup.principalSubgroup R K

namespace IdeleClassGroup

/-- The map from the completion `Kᵥ` at an infinite place `v` to the idele class group. -/
@[simps!]
def ofCompletion (v : InfinitePlace K) : v.Completionˣ →* IdeleClassGroup R K :=
  (QuotientGroup.mk' (IdeleGroup.principalSubgroup R K)).comp (IdeleGroup.ofCompletion R K v)

/-- The map from the completion `Kᵥ` at a finite place `v` to the idele class group. -/
@[simps!]
def ofAdicCompletion (v : HeightOneSpectrum R) : (v.adicCompletion K)ˣ →* IdeleClassGroup R K :=
  (QuotientGroup.mk' (IdeleGroup.principalSubgroup R K)).comp (IdeleGroup.ofAdicCompletion R K v)

end IdeleClassGroup

end NumberField
