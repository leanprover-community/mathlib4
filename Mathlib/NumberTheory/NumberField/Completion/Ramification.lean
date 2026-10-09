/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Ramification theory of completions of number fields

This file studies the ramification of completions of number fields.

If `w` is an infinite place of `L` lying over the infinite place `v` of `K`, then `algebraMap K L`
extends to a continuous ring homomorphism `v.Completion →+* w.Completion`. Any algebra
`v.Completion → w.Completion` that is continuous and compatible with `K → L` is equal to the one
induced by this map.

## Main definitions

- `NumberField.InfinitePlace.Completion.completionMap` : the ring homomorphism
  `v.Completion →+* w.Completion` extending `algebraMap K L`.
- `NumberField.InfinitePlace.Completion.algebraOfLiesOver` : the algebra induced by
  `completionMap`.
- `NumberField.InfinitePlace.inertiaDeg` : the inertia degree of a place `w` of `L` over a
  place `v` of `K`, defined as the local degree of the extension of completions at `w` and
  `v` if `w` lies over `v` and zero otherwise.

## Main results

- `NumberField.InfinitePlace.Completion.algebra_eq` : a continuous algebra
  `v.Completion → w.Completion` compatible with `K → L` is `algebraOfLiesOver`.
- `NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank` : the degree of `L` over `K` is equal to
  the sum of the inertia degrees of the places of `L` over `v`.

## Tags

number field, infinite places, ramification
-/

@[expose] public section

namespace NumberField.InfinitePlace

namespace Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K) (w : InfinitePlace L)
variable [w.LiesOver v]

/-- The ring homomorphism `v.Completion →+* w.Completion` induced by `algebraMap K L`, when `w`
lies over `v`. -/
noncomputable def completionMap : v.Completion →+* w.Completion :=
  ((Completion.equiv w).symm.toRingHom.comp <|
    UniformSpace.Completion.mapRingHom _ (LiesOver.isometry_algebraMap w v).continuous).comp
    (Completion.equiv v).toRingHom

theorem continuous_completionMap : Continuous (completionMap v w) :=
  (continuous_ofCompletion w).comp <|
    UniformSpace.Completion.continuous_map.comp (continuous_toCompletion v)

theorem completionMap_coe (x : WithAbs v.1) :
    completionMap v w (x : v.Completion) =
      ((algebraMap (WithAbs v.1) (WithAbs w.1) x : WithAbs w.1) : w.Completion) :=
  Completion.ext <| UniformSpace.Completion.mapRingHom_coe _ x

@[instance_reducible]
noncomputable def algebraOfLiesOver : Algebra v.Completion w.Completion :=
  (completionMap v w).toAlgebra

instance : letI := algebraOfLiesOver v w
    IsScalarTower K v.Completion w.Completion :=
  let := algebraOfLiesOver v w
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, algebraMap_eq_coe', completionMap_coe]
    apply Completion.ext
    rw [algebraMap_toCompletion, WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]
    exact toCompletion_ofCompletion w _

instance : letI := algebraOfLiesOver v w
    ContinuousSMul v.Completion w.Completion :=
  let := algebraOfLiesOver v w
  continuousSMul_of_algebraMap v.Completion w.Completion (continuous_completionMap v w)

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion]

theorem algebraMap_eq_of_liesOver : algebraMap v.Completion w.Completion =
    completionMap v w := by
  refine DFunLike.ext' <| ext_of_continuous v (continuous_algebraMap _ _)
    (continuous_completionMap v w) fun k ↦ ?_
  rw [algebraMap_coe]
  exact (completionMap_coe v w _).symm

theorem algebraMap_apply_of_liesOver (x : v.Completion) :
    algebraMap v.Completion w.Completion x = completionMap v w x := by
  rw [algebraMap_eq_of_liesOver]

theorem algebra_eq : ‹_› = algebraOfLiesOver v w :=
  Algebra.algebra_ext _ _ (algebraMap_apply_of_liesOver v w)

end Completion

section InertiaDeg

open NumberField.ComplexEmbedding Finset Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K) (w : InfinitePlace L)

open scoped Classical in
/-- The inertia degree of `w` over `v`. -/
protected noncomputable def inertiaDeg : ℕ :=
  if _ : w.LiesOver v then
    letI := algebraOfLiesOver v w
    (⊥ : Ideal w.Completion).inertiaDeg v.Completion else 0

section Algebra

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion] {w}

open Completion

/-- If `w` is a ramified place over `v` then `w.Completion` has `v.Completion` dimension two. -/
theorem IsRamified.finrank_eq_two [w.LiesOver v] (h : w.IsRamified K) :
    Module.finrank v.Completion w.Completion = 2 := by
  have H := NumberField.InfinitePlace.isRamified_iff.mp h
  rw [NumberField.InfinitePlace.LiesOver.comap_eq w v] at H
  have := LiesOver.extensionEmbedding_liesOver_of_isReal w H.2
  rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal H.2)
      (ringEquivComplexOfIsComplex H.1) (by ext; simp),
    Complex.finrank_real_complex]

/-- If `w` is an unramified place over `v` then `w.Completion` has `v.Completion` dimension one. -/
theorem IsUnramified.finrank_eq_one [w.LiesOver v] (h : w.IsUnramified K) :
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

@[deprecated (since := "2026-07-10")] alias Completion.finrank_eq_two_of_isRamified :=
  IsRamified.finrank_eq_two

@[deprecated (since := "2026-07-10")] alias Completion.finrank_eq_one_of_isUnramified :=
  IsUnramified.finrank_eq_one

variable (w) in
theorem mult_mul_finrank [w.LiesOver v] :
    v.mult * Module.finrank v.Completion w.Completion = w.mult := by
  have hv : v = w.comap (algebraMap K L) := Subtype.ext ‹w.LiesOver v›.under_eq.symm
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v, hv, h.eq, mul_one]
  · rw [h.finrank_eq_two v, hv, h.isReal.mult_eq_one, h.isComplex.mult_eq_two, one_mul]

variable (w) in
theorem inertiaDeg_of_liesOver [w.LiesOver v] :
    v.inertiaDeg w = (⊥ : Ideal w.Completion).inertiaDeg v.Completion := by
  rw [algebra_eq v w, InfinitePlace.inertiaDeg, dite_eq_left]

variable (w) in
theorem inertiaDeg_eq_finrank [w.LiesOver v] :
    v.inertiaDeg w = Module.finrank v.Completion w.Completion := by
  rw [inertiaDeg_of_liesOver, Ideal.inertiaDeg_eq_of_isMaximal ⊥]
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.Completion) (by ext; simp [algebraMap_eq_of_liesOver])

end Algebra

variable {v w} in
theorem inertiaDeg_eq_one (hw : w ∈ unramifiedPlacesOver L v) : v.inertiaDeg w = 1 :=
  have := (Set.mem_ofPred.1 hw).1
  let := algebraOfLiesOver v w
  hw.2.finrank_eq_one v ▸ inertiaDeg_eq_finrank v w

variable {v w} in
theorem inertiaDeg_eq_two (hw : w ∈ ramifiedPlacesOver L v) : v.inertiaDeg w = 2 :=
  have := (Set.mem_ofPred.1 hw).1
  let := algebraOfLiesOver v w
  hw.2.finrank_eq_two v ▸ inertiaDeg_eq_finrank v w

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
  simp [← unramifiedPlacesOver_ncard_add_eq_finrank L v, mul_comm, ncard_eq_toFinset_card']

end InertiaDeg

end NumberField.InfinitePlace

namespace NumberField.LiesOver

@[deprecated (since := "2026-10-09")] alias completionMap := InfinitePlace.Completion.completionMap

@[deprecated (since := "2026-10-09")] alias continuous_completionMap :=
  InfinitePlace.Completion.continuous_completionMap

@[deprecated (since := "2026-10-09")] alias completionMap_coe :=
  InfinitePlace.Completion.completionMap_coe

end NumberField.LiesOver
