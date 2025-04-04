/-
Copyright (c) 2025 X. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# CM extension of number fields

A CM-extension of number fields is a totally complex number field that is a quadratic extension of
a totally real number field.

## Main definitions

* `IsCM`: a predicate on two number fields `F` and `K` stating that `K/F` is a CM-extension.

-/

open NumberField InfinitePlace ComplexEmbedding

/--
An extension `K/F` of number fields is a `CM`-extension if `K` is totally complex, `F` is totally
real and the extension `K/F` is of degree `2`.
-/
class IsCM (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : Prop
  extends IsTotallyReal F, IsTotallyComplex K where
  finrank_eq_two' : Module.finrank F K = 2

namespace IsCM

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

theorem isTotallyComplex [IsCM F K] :
    IsTotallyComplex K := toIsTotallyComplex F

theorem isTotallyReal [IsCM F K] :
    IsTotallyReal F := toIsTotallyReal K

theorem finrank_eq_two [IsCM F K] :
    Module.finrank F K = 2 := finrank_eq_two'

section first_results

variable [IsCM F K]

instance : IsGalois F K :=
{ to_isSeparable := Algebra.IsSeparable.of_integral _ _
  to_normal := normal_of_rank_eq_two _ _ (finrank_eq_two  F K) }

theorem card_infinitePlace_eq_card_infinitePlace :
    Fintype.card (InfinitePlace K) = Fintype.card (InfinitePlace F) := by
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_zero_iff.mpr (isTotallyComplex F K), zero_add,
    nrComplexPlaces_eq_zero_iff.mpr (isTotallyReal F K), add_zero, ← IsTotallyReal.finrank,
    ← Nat.mul_left_cancel_iff zero_lt_two, ← IsTotallyComplex.finrank,
    ← Module.finrank_mul_finrank ℚ F K, finrank_eq_two F K, mul_comm]

theorem units_rank_eq_units_rank :
    Units.rank K = Units.rank F := by
  rw [Units.rank, Units.rank, card_infinitePlace_eq_card_infinitePlace F K]

end first_results

end IsCM
