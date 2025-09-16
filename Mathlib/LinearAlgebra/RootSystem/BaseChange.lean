/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.PerfectPairing.Restrict
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Base change for root pairings

When the coefficients are a field, root pairings behave well with respect to restriction and
extension of scalars.

## Main results:
* `RootPairing.restrict`: if `RootPairing.pairing` takes values in a subfield, we may restrict to
  get a root _system_ with coefficients in the subfield. Of particular interest is the case when
  the pairing takes values in its prime subfield (which happens for crystallographic pairings).

## TODO

* Extension of scalars
* Crystallographic root systems are isomorphic to base changes of root systems over `ℤ`: Take
  `M₀` and `N₀` to be the `ℤ`-span of roots and coroots.

-/

noncomputable section

open Set Function
open Submodule (span injective_subtype span subset_span span_setOf_mem_eq_top)

namespace RootPairing

/-- We say a root pairing is balanced if the root span and coroot span are perfectly
complementary.

All root systems are balanced and all finite root pairings over a field are balanced. -/
class IsBalanced {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N) : Prop where
  isPerfectCompl : P.toLinearMap.IsPerfectCompl (P.rootSpan R) (P.corootSpan R)

instance {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [CommRing R] [Module R M] [Module R N] (P : RootSystem ι R M N) :
    P.IsBalanced where
  isPerfectCompl := by simp

variable {ι L M N : Type*}
  [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N)

section restrictScalars

variable (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced]

section SubfieldValued

variable (hP : ∀ i j, P.pairing i j ∈ (algebraMap K L).range)

/-- Restriction of scalars for a root pairing taking values in a subfield.

Note that we obtain a root system (not just a root pairing). See also
`RootPairing.restrictScalars`. -/
def restrictScalars' :
    RootSystem ι K (span K (range P.root)) (span K (range P.coroot)) where
  toLinearMap := .restrictScalarsRange₂ (R := L)
    (span K (range P.root)).subtype (span K (range P.coroot)).subtype (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) P.toLinearMap fun x y ↦
      LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (LinearMap.range (Algebra.linearMap K L)) (range P.root) (range P.coroot)
      (LinearMap.restrictScalarsₗ K L _ _ _ ∘ₗ P.toLinearMap.restrictScalars K)
      (by rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩; exact hP i j) _ _ x.property y.property
  isPerfPair_toLinearMap := .restrictScalars_of_field P.toLinearMap _ _
    (injective_subtype _) (injective_subtype _) (by simpa using IsBalanced.isPerfectCompl) _
  root := ⟨fun i ↦ ⟨_, subset_span (mem_range_self i)⟩, fun i j h ↦ by simpa using h⟩
  coroot := ⟨fun i ↦ ⟨_, subset_span (mem_range_self i)⟩, fun i j h ↦ by simpa using h⟩
  root_coroot_two i := by
    have : algebraMap K L 2 = 2 := by
      rw [← Int.cast_two (R := K), ← Int.cast_two (R := L), map_intCast]
    exact FaithfulSMul.algebraMap_injective K L <| by simp [this]
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    ext; simpa [algebra_compatible_smul L] using P.reflectionPerm_root i j
  reflectionPerm_coroot i j := by
    ext; simpa [algebra_compatible_smul L] using P.reflectionPerm_coroot i j
  span_root_eq_top := by
    rw [← span_setOf_mem_eq_top]
    congr
    ext ⟨x, hx⟩
    simp
  span_coroot_eq_top := by
    rw [← span_setOf_mem_eq_top]
    congr
    ext ⟨x, hx⟩
    simp

@[simp] lemma restrictScalars_toLinearMap_apply_apply
    (x : span K (range P.root)) (y : span K (range P.coroot)) :
    algebraMap K L ((P.restrictScalars' K hP).toLinearMap x y) = P.toLinearMap x y := by
  simp [restrictScalars']

@[simp] lemma restrictScalars_coe_root (i : ι) :
    (P.restrictScalars' K hP).root i = P.root i :=
  rfl

@[simp] lemma restrictScalars_coe_coroot (i : ι) :
    (P.restrictScalars' K hP).coroot i = P.coroot i :=
  rfl

@[simp] lemma restrictScalars_pairing (i j : ι) :
    algebraMap K L ((P.restrictScalars' K hP).pairing i j) = P.pairing i j := by
  simp only [pairing, restrictScalars_toLinearMap_apply_apply, restrictScalars_coe_root,
    restrictScalars_coe_coroot]

end SubfieldValued

/-- Restriction of scalars for a crystallographic root pairing. -/
abbrev restrictScalars [P.IsCrystallographic] :
    RootSystem ι K (span K (range P.root)) (span K (range P.coroot)) :=
  P.restrictScalars' K (IsValuedIn.trans P K ℤ).exists_value

/-- Restriction of scalars to `ℚ` for a crystallographic root pairing in characteristic zero. -/
abbrev restrictScalarsRat [CharZero L] [P.IsCrystallographic] :=
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ L)
  let _i : Module ℚ N := Module.compHom N (algebraMap ℚ L)
  P.restrictScalars ℚ

end restrictScalars

end RootPairing
