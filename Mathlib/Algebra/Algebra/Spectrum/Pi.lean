/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Group.Pi.Units

/-!
# Spectrum and quasispectrum of products

This file contains results regarding the spectra and quasispectra of (indexed) products of
elements of a (non-unital) ring. The main result is that the (quasi)spectrum of a product is the
union of the (quasi)spectra.

## Main declarations

+ `Pi.spectrum_eq`: `spectrum R a = ⋃ i, spectrum R (a i)` for `a : ∀ i, κ i`
+ `Prod.spectrum_eq`: `spectrum R ⟨a, b⟩ = spectrum R a ∪ spectrum R b`
+ `Pi.quasispectrum_eq`: `quasispectrum R a = ⋃ i, quasispectrum R (a i)` for `a : ∀ i, κ i`
+ `Prod.quasispectrum_eq`: `quasispectrum R ⟨a, b⟩ = quasispectrum R a ∪ quasispectrum R b`

## TODO

+ Apply these results to block matrices.

-/

variable {ι A B R : Type*} {κ : ι → Type*}

section quasiregular

variable (κ) in
/-- The equivalence between pre-quasiregular elements of an indexed product and the indexed product
of pre-quasiregular elements. -/
def PreQuasiregular.toPi [∀ i, NonUnitalSemiring (κ i)] :
    PreQuasiregular (∀ i, κ i) ≃* ∀ i, PreQuasiregular (κ i) where
  toFun := fun x i => .mk <| x.val i
  invFun := fun x => .mk <| fun i => (x i).val
  map_mul' _ _ := rfl

variable (A B) in
/-- The equivalence between pre-quasiregular elements of a product and the product of
pre-quasiregular elements. -/
def PreQuasiregular.toProd [NonUnitalSemiring A] [NonUnitalSemiring B] :
    PreQuasiregular (A × B) ≃* PreQuasiregular A × PreQuasiregular B where
  toFun := fun p => ⟨.mk p.val.1, .mk p.val.2⟩
  invFun := fun ⟨a, b⟩ => .mk ⟨a.val, b.val⟩
  map_mul' _ _ := rfl

lemma isQuasiregular_pi_iff [∀ i, NonUnitalSemiring (κ i)] (x : ∀ i, κ i) :
    IsQuasiregular x ↔ ∀ i, IsQuasiregular (x i) := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toPi κ), Pi.isUnit_iff]
  congr!

lemma isQuasiregular_prod_iff [NonUnitalSemiring A] [NonUnitalSemiring B] (a : A) (b : B) :
    IsQuasiregular (⟨a, b⟩ : A × B) ↔ IsQuasiregular a ∧ IsQuasiregular b := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toProd A B), Prod.isUnit_iff]
  congr!

lemma quasispectrum.mem_iff_of_isUnit [CommSemiring R] [NonUnitalRing A]
    [Module R A] {a : A} {r : R} (hr : IsUnit r) :
    r ∈ quasispectrum R a ↔ ¬ IsQuasiregular (-(hr.unit⁻¹ • a)) :=
  ⟨fun h => h hr, fun h _ => h⟩

end quasiregular

section spectrum

lemma Pi.spectrum_eq [CommSemiring R] [∀ i, Ring (κ i)] [∀ i, Algebra R (κ i)]
    (a : ∀ i, κ i) : spectrum R a = ⋃ i, spectrum R (a i) := by
  apply compl_injective
  simp_rw [spectrum, Set.compl_iUnion, compl_compl, resolventSet, Set.iInter_setOf,
    Pi.isUnit_iff, sub_apply, algebraMap_apply]

lemma Prod.spectrum_eq [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (a : A) (b : B) : spectrum R (⟨a, b⟩ : A × B) = spectrum R a ∪ spectrum R b := by
  apply compl_injective
  simp_rw [spectrum, Set.compl_union, compl_compl, resolventSet, ← Set.setOf_and,
    Prod.isUnit_iff, algebraMap_apply, mk_sub_mk]

lemma Pi.quasispectrum_eq [Nonempty ι] [CommSemiring R] [∀ i, NonUnitalRing (κ i)]
    [∀ i, Module R (κ i)] (a : ∀ i, κ i) :
    quasispectrum R a = ⋃ i, quasispectrum R (a i) := by
  apply compl_injective
  ext r
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall,
    not_not, Set.mem_iUnion, not_exists]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_pi_iff]
  · simp [hr]

lemma Prod.quasispectrum_eq [CommSemiring R] [NonUnitalRing A] [NonUnitalRing B]
    [Module R A] [Module R B] (a : A) (b : B) :
    quasispectrum R (⟨a, b⟩ : A × B) = quasispectrum R a ∪ quasispectrum R b := by
  apply compl_injective
  ext r
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not, Set.mem_union]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_prod_iff]
  · simp [hr]

end spectrum
