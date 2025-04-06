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

+ `Pi.spectrum_eq`: `spectrum R a = ⋃ i, spectrum R (a i)`
+ `Prod.spectrum_eq`: `spectrum R ⟨a, b⟩ = spectrum R a ∪ spectrum R b`
+ `Pi.quasispectrum_eq`: `quasispectrum R a = ⋃ i, quasispectrum R (a i)`
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
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (A B) in
/-- The equivalence between pre-quasiregular elements of a product and the product of
pre-quasiregular elements. -/
def PreQuasiregular.toProd [NonUnitalSemiring A] [NonUnitalSemiring B] :
    PreQuasiregular (A × B) ≃* PreQuasiregular A × PreQuasiregular B where
  toFun := fun p => ⟨.mk p.val.1, .mk p.val.2⟩
  invFun := fun ⟨a, b⟩ => .mk ⟨a.val, b.val⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

lemma isQuasiregular_pi_iff [∀ i, NonUnitalSemiring (κ i)] (x : ∀ i, κ i) :
    IsQuasiregular x ↔ ∀ i, IsQuasiregular (x i) := by
  refine ⟨fun ⟨u, h⟩ => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [funext_iff] at h
    let u' := u.map ((PreQuasiregular.toPi κ).toMonoidHom)
    let u'' := MulEquiv.piUnits u'
    exact fun i => ⟨u'' i, h i⟩
  case mpr =>
    let u i := Classical.choose (h i)
    let u' := MulEquiv.piUnits.symm u
    let u'' := u'.map ((PreQuasiregular.toPi κ).symm.toMonoidHom)
    refine ⟨u'', ?_⟩
    ext i
    exact Classical.choose_spec (h i)

lemma isQuasiregular_prod_iff [NonUnitalSemiring A] [NonUnitalSemiring B] (a : A) (b : B) :
    IsQuasiregular (⟨a, b⟩ : A × B) ↔ IsQuasiregular a ∧ IsQuasiregular b := by
  refine ⟨fun ⟨u, h⟩ => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [Prod.ext_iff] at h
    let u' := u.map ((PreQuasiregular.toProd A B).toMonoidHom)
    let u'' := MulEquiv.prodUnits u'
    exact ⟨⟨u''.1, h.1⟩, ⟨u''.2, h.2⟩⟩
  case mpr =>
    let ua := Classical.choose h.1
    let ub := Classical.choose h.2
    let u' := MulEquiv.prodUnits.symm ⟨ua, ub⟩
    let u'' := u'.map ((PreQuasiregular.toProd A B).symm.toMonoidHom)
    refine ⟨u'', ?_⟩
    ext
    case fst => exact Classical.choose_spec h.1
    case snd => exact Classical.choose_spec h.2

lemma quasispectrum.mem_iff_of_isUnit [CommSemiring R] [NonUnitalRing A]
    [Module R A] {a : A} {r : R} (hr : IsUnit r) :
    r ∈ quasispectrum R a ↔ ¬ IsQuasiregular (-(hr.unit⁻¹ • a)) :=
  ⟨fun h => h hr, fun h _ => h⟩

end quasiregular

section spectrum

lemma Pi.spectrum_eq [CommSemiring R] [∀ i, Ring (κ i)] [∀ i, Algebra R (κ i)]
    (a : ∀ i, κ i) : spectrum R a = ⋃ i, spectrum R (a i) := by
  refine subset_antisymm ?sub ?super
  case sub =>
    intro r hr
    rw [spectrum.mem_iff, Pi.isUnit_iff] at hr
    push_neg at hr
    obtain ⟨i, hi⟩ := hr
    rw [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    simpa [spectrum.mem_iff] using hi
  case super =>
    intro r hr
    rw [spectrum.mem_iff, Pi.isUnit_iff]
    rw [Set.mem_iUnion] at hr
    obtain ⟨i, hi⟩ := hr
    rw [spectrum.mem_iff] at hi
    push_neg
    refine ⟨i, hi⟩

lemma Prod.spectrum_eq [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (a : A) (b : B) : spectrum R (⟨a, b⟩ : A × B) = spectrum R a ∪ spectrum R b := by
  refine subset_antisymm ?sub ?super
  case sub =>
    intro r hr
    rw [spectrum.mem_iff, Prod.isUnit_iff, not_and_or] at hr
    rw [Set.mem_union]
    exact hr
  case super =>
    intro r hr
    rw [spectrum.mem_iff, Prod.isUnit_iff]
    rw [not_and_or]
    rw [Set.mem_union] at hr
    exact hr

lemma Pi.quasispectrum_eq [Nonempty ι] [CommSemiring R] [∀ i, NonUnitalRing (κ i)]
    [∀ i, Module R (κ i)] (a : ∀ i, κ i) :
    quasispectrum R a = ⋃ i, quasispectrum R (a i) := by
  refine subset_antisymm ?sub ?super
  case sub =>
    intro r hr
    by_cases hr' : IsUnit r
    · rw [Set.mem_iUnion]
      rw [quasispectrum.mem_iff_of_isUnit hr', isQuasiregular_pi_iff] at hr
      push_neg at hr
      obtain ⟨i, hi⟩ := hr
      refine ⟨i, ?_⟩
      rw [quasispectrum.mem_iff_of_isUnit hr']
      exact hi
    · rw [Set.mem_iUnion]
      let i := Classical.arbitrary ι
      exact ⟨i, quasispectrum.not_isUnit_mem (a i) hr'⟩
  case super =>
    intro r hr
    by_cases hr' : IsUnit r
    · rw [quasispectrum.mem_iff_of_isUnit hr', isQuasiregular_pi_iff]
      push_neg
      rw [Set.mem_iUnion] at hr
      obtain ⟨i, hi⟩ := hr
      rw [quasispectrum.mem_iff_of_isUnit hr'] at hi
      exact ⟨i, hi⟩
    · exact quasispectrum.not_isUnit_mem _ hr'

lemma Prod.quasispectrum_eq [CommSemiring R] [NonUnitalRing A] [NonUnitalRing B]
    [Module R A] [Module R B] (a : A) (b : B) :
    quasispectrum R (⟨a, b⟩ : A × B) = quasispectrum R a ∪ quasispectrum R b := by
  refine subset_antisymm ?sub ?super
  case sub =>
    intro r hr
    by_cases hr' : IsUnit r
    · rw [Set.mem_union]
      rw [quasispectrum.mem_iff_of_isUnit hr', isQuasiregular_prod_iff, not_and_or] at hr
      simp only [quasispectrum.mem_iff_of_isUnit hr']
      exact hr
    · exact Or.inl <| quasispectrum.not_isUnit_mem _ hr'
  case super =>
    intro r hr
    by_cases hr' : IsUnit r
    · rw [Set.mem_union] at hr
      simp only [quasispectrum.mem_iff_of_isUnit hr'] at hr
      simp only [quasispectrum.mem_iff_of_isUnit hr']
      rw [isQuasiregular_prod_iff, not_and_or]
      exact hr
    · exact quasispectrum.not_isUnit_mem _ hr'

end spectrum
