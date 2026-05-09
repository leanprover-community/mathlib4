/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# Ramification theory of completions of number fields

This file studies the ramification of completions of number fields.

## Main definitions

- `NumberField.InfinitePlace.inertiaDeg` : the inertia degree of a place `w` of `L` over a
  place `v` of `K`, defined as the local degree of the extension of completions at `w` and
  `v` if `w` lies over `v` and zero otherwise.

## Main results

- `NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank` : the degree of `L` over `K` is equal to
  the sum of the inertia degrees of the places of `L` over `v`.

## Tags

number field, infinite places, ramification
-/

@[expose] public section

section infinite_place

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding Finset AbsoluteValue.Completion

-- to enable `w.1.LiesOver v.1 → Algebra v.Completion w.Completion` instance
open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K) {w : InfinitePlace L}

namespace Completion

set_option backward.isDefEq.respectTransparency false in
/-- If `w` is a ramified place over `v` then `w.Completion` has `v.Completion` dimension two. -/
theorem finrank_eq_two_of_isRamified [w.1.LiesOver v.1] (h : w.IsRamified K) :
    Module.finrank v.Completion w.Completion = 2 := by
  have H := NumberField.InfinitePlace.isRamified_iff.mp h
  rw [NumberField.InfinitePlace.LiesOver.comap_eq w v] at H
  have := LiesOver.extensionEmbedding_liesOver_of_isReal w H.2
  rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal H.2)
      (ringEquivComplexOfIsComplex H.1) (by ext; simp),
    Complex.finrank_real_complex]

set_option backward.isDefEq.respectTransparency false in
/-- If `w` is an unramified place over `v` then `w.Completion` has `v.Completion` dimension one. -/
theorem finrank_eq_one_of_isUnramified [w.1.LiesOver v.1] (h : w.IsUnramified K) :
    Module.finrank v.Completion w.Completion = 1 := by
  rcases v.isReal_or_isComplex with (hv | hv)
  · have := LiesOver.extensionEmbedding_liesOver_of_isReal w hv
    rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal
        (h.liesOver_isReal_over _ _ hv)) (RingHom.ext fun _ ↦ Complex.ofReal_inj.1 <| by simp),
      Module.finrank_self]
  · cases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with
    | inl hl =>
      have : ComplexEmbedding.LiesOver w.embedding v.embedding := ⟨hl⟩
      have := liesOver_extensionEmbedding w v
      rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
          (ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv)) (by ext; simp),
        Module.finrank_self]
    | inr hr =>
      have : ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding := ⟨hr⟩
      have := liesOver_conjugate_extensionEmbedding w v
      rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        ((ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv)).trans
          (starRingAut (R := ℂ))) (by ext; simp [← conjugate_coe_eq]),
        Module.finrank_self]

end Completion

open Completion

variable (w)

open scoped Classical in
/-- The inertia degree of `w` over `v`. -/
protected noncomputable def inertiaDeg : ℕ :=
  if _ : w.1.LiesOver v.1 then (⊥ : Ideal v.Completion).inertiaDeg (⊥ : Ideal w.Completion) else 0

theorem inertiaDeg_of_liesOver [w.1.LiesOver v.1] :
    v.inertiaDeg w = (⊥ : Ideal v.Completion).inertiaDeg (⊥ : Ideal w.Completion) := by
  simp only [InfinitePlace.inertiaDeg, dif_pos]

theorem inertiaDeg_eq_finrank [w.1.LiesOver v.1] :
    v.inertiaDeg w = Module.finrank v.Completion w.Completion := by
  simp only [inertiaDeg_of_liesOver, Ideal.inertiaDeg, Ideal.comap_bot_of_injective _ <|
    FaithfulSMul.algebraMap_injective v.Completion w.Completion]
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.Completion) (by ext; simp [RingHom.algebraMap_toAlgebra])

variable {v w} in
theorem inertiaDeg_eq_one (hw : w ∈ unramifiedPlacesOver L v) : v.inertiaDeg w = 1 :=
  have := (Set.mem_setOf.1 hw).1; finrank_eq_one_of_isUnramified v hw.2 ▸ inertiaDeg_eq_finrank v w

variable {v w} in
theorem inertiaDeg_eq_two (hw : w ∈ ramifiedPlacesOver L v) : v.inertiaDeg w = 2 :=
  have := (Set.mem_setOf.1 hw).1; finrank_eq_two_of_isRamified v hw.2 ▸ inertiaDeg_eq_finrank v w

variable (K L) in
open scoped Classical in
open Finset Set in
/-- The degree of `L` over `K` is equal to the sum of the inertia degrees of the places over `v`. -/
theorem sum_inertiaDeg_eq_finrank [NumberField K] [NumberField L] :
    ∑ w ∈ v.placesOver L, v.inertiaDeg w = Module.finrank K L := by
  rw [← union_ramifiedPlacesOver_unramifiedPlacesOver L v, toFinset_union,
    sum_union (Set.disjoint_toFinset.2 <| disjoint_ramifiedPlacesOver_unramifiedPlacesOver L v),
    sum_congr rfl (fun _ h ↦ inertiaDeg_eq_two (by simpa using h)),
    sum_congr rfl (fun _ h ↦ inertiaDeg_eq_one (by simpa using h)), sum_const, add_comm]
  simp [← unramifedPlacesOver_ncard_add_eq_finrank L v, mul_comm, ncard_eq_toFinset_card']

end NumberField.InfinitePlace

end infinite_place
