/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.FinitePlaces
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

open InfinitePlace AbsoluteValue.Completion Completion IsDedekindDomain HeightOneSpectrum

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

@[simp]
theorem algebraMap_snd_apply (x : K) (v : HeightOneSpectrum R) :
    (algebraMap K (AdeleRing R K) x).2 v = x := rfl

theorem algebraMap_injective [NumberField K] : Function.Injective (algebraMap K (AdeleRing R K)) :=
  fun _ _ hxy => (algebraMap K _).injective (Prod.ext_iff.1 hxy).1

/-- The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`. -/
abbrev principalSubgroup : AddSubgroup (AdeleRing R K) := (algebraMap K _).range.toAddSubgroup

variable [NumberField K] [Module.Free ℤ R] [Module.Finite ℤ R]

set_option backward.isDefEq.respectTransparency false in
instance (v : HeightOneSpectrum R) : LocallyCompactSpace (v.adicCompletion K) := by
  have : IsCompact (Set.univ : Set (v.adicCompletionIntegers K)) := isCompact_univ
  refine IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup ?_
    ((Valued.is_topological_valuation {x | Valued.v.restrict x < 1}).2 ⟨1, by grind⟩)
  exact (isCompact_iff_isCompact_univ.2 this).of_isClosed_subset (Valued.isClosed_ball _ _)
    fun _ _ ↦ by grind [Valuation.restrict_lt_one_iff, SetLike.mem_coe, mem_adicCompletionIntegers]

open scoped RestrictedProduct in
instance : LocallyCompactSpace (IsDedekindDomain.FiniteAdeleRing R K) :=
  have : Fact (∀ v : HeightOneSpectrum R, IsOpen (v.adicCompletionIntegers K).carrier) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  inferInstanceAs (LocallyCompactSpace (Πʳ _, [_, _]))

instance : LocallyCompactSpace (AdeleRing R K) := Prod.locallyCompactSpace _ _

end AdeleRing

end NumberField
