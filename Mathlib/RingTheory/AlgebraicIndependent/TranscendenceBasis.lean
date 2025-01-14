/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Transcendence basis

This file defines the transcendence basis as a maximal algebraically independent subset.

## Main results

* `exists_isTranscendenceBasis`: a ring extension has a transcendence basis

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## TODO
Define the transcendence degree and show it is independent of the choice of a
transcendence basis.

## Tags
transcendence basis, transcendence degree, transcendence

-/

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u v w

variable {ι ι' : Type*} (R : Type*) {K A A' : Type*}
variable {x : ι → A}
variable [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

open AlgebraicIndependent

theorem exists_isTranscendenceBasis (h : Injective (algebraMap R A)) :
    ∃ s : Set A, IsTranscendenceBasis R ((↑) : s → A) := by
  cases' exists_maximal_algebraicIndependent (∅ : Set A) Set.univ (Set.subset_univ _)
      ((algebraicIndependent_empty_iff R A).2 h) with
    s hs
  refine ⟨s, hs.2.1.1, fun t ht hst ↦ ?_⟩
  simp only [Subtype.range_coe_subtype, setOf_mem_eq] at *
  exact hs.2.eq_of_le ⟨ht, subset_univ _⟩ hst

/-- `Type` version of `exists_isTranscendenceBasis`. -/
theorem exists_isTranscendenceBasis' (R : Type u) {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] (h : Injective (algebraMap R A)) :
    ∃ (ι : Type v) (x : ι → A), IsTranscendenceBasis R x := by
  obtain ⟨s, h⟩ := exists_isTranscendenceBasis R h
  exact ⟨s, Subtype.val, h⟩

variable {R}

theorem AlgebraicIndependent.isTranscendenceBasis_iff {ι : Type w} {R : Type u} [CommRing R]
    [Nontrivial R] {A : Type v} [CommRing A] [Algebra R A] {x : ι → A}
    (i : AlgebraicIndependent R x) :
    IsTranscendenceBasis R x ↔
      ∀ (κ : Type v) (w : κ → A) (_ : AlgebraicIndependent R w) (j : ι → κ) (_ : w ∘ j = x),
        Surjective j := by
  fconstructor
  · rintro p κ w i' j rfl
    have p := p.2 (range w) i'.coe_range (range_comp_subset_range _ _)
    rw [range_comp, ← @image_univ _ _ w] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p
    use i
    intro w i' h
    specialize p w ((↑) : w → A) i' (fun i => ⟨x i, range_subset_iff.mp h i⟩) (by ext; simp)
    have q := congr_arg (fun s => ((↑) : w → A) '' s) p.range_eq
    dsimp at q
    rw [← image_univ, image_image] at q
    simpa using q

theorem IsTranscendenceBasis.isAlgebraic [Nontrivial R] (hx : IsTranscendenceBasis R x) :
    Algebra.IsAlgebraic (adjoin R (range x)) A := by
  constructor
  intro a
  rw [← not_iff_comm.1 (hx.1.option_iff _).symm]
  intro ai
  have h₁ : range x ⊆ range fun o : Option ι => o.elim a x := by
    rintro x ⟨y, rfl⟩
    exact ⟨some y, rfl⟩
  have h₂ : range x ≠ range fun o : Option ι => o.elim a x := by
    intro h
    have : a ∈ range x := by
      rw [h]
      exact ⟨none, rfl⟩
    rcases this with ⟨b, rfl⟩
    have : some b = none := ai.injective rfl
    simpa
  exact h₂ (hx.2 (Set.range fun o : Option ι => o.elim a x)
    ((algebraicIndependent_subtype_range ai.injective).2 ai) h₁)

/-- If `x` is a transcendence basis of `A/R`, then it is empty if and only if
`A/R` is algebraic. -/
theorem IsTranscendenceBasis.isEmpty_iff_isAlgebraic [Nontrivial R]
    (hx : IsTranscendenceBasis R x) :
    IsEmpty ι ↔ Algebra.IsAlgebraic R A := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ hx.1.isEmpty_of_isAlgebraic⟩
  have := hx.isAlgebraic
  rw [Set.range_eq_empty x, adjoin_empty] at this
  exact algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left R A

/-- If `x` is a transcendence basis of `A/R`, then it is not empty if and only if
`A/R` is transcendental. -/
theorem IsTranscendenceBasis.nonempty_iff_transcendental [Nontrivial R]
    (hx : IsTranscendenceBasis R x) :
    Nonempty ι ↔ Algebra.Transcendental R A := by
  rw [← not_isEmpty_iff, Algebra.transcendental_iff_not_isAlgebraic, hx.isEmpty_iff_isAlgebraic]

theorem IsTranscendenceBasis.isAlgebraic_field {F E : Type*} {x : ι → E}
    [Field F] [Field E] [Algebra F E] (hx : IsTranscendenceBasis F x) :
    Algebra.IsAlgebraic (IntermediateField.adjoin F (range x)) E := by
  haveI := hx.isAlgebraic
  set S := range x
  letI : Algebra (adjoin F S) (IntermediateField.adjoin F S) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin F S)).toRingHom.toAlgebra
  haveI : IsScalarTower (adjoin F S) (IntermediateField.adjoin F S) E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact Algebra.IsAlgebraic.extendScalars (R := adjoin F S) (Subalgebra.inclusion_injective _)

theorem finite_of_isTranscendenceBasis_of_algebraic_adjoin [DecidableEq ι] [Nontrivial R]
    [NoZeroDivisors A] (x : ι → A) (y : ι' → A)
    (hx : IsTranscendenceBasis R x)
    (hy : AlgebraicIndependent R y) (i : ι') :
    ∃ j : ι, Algebra.IsAlgebraic (adjoin R (range (Function.update x j (y i)))) A := by
  obtain ⟨P, hP₁, hP₂⟩ := (isAlgebraic_adjoin_range_left_iff rfl).1 (hx.isAlgebraic.1 (y i))
  obtain ⟨j, hj⟩ : ∃ j, (aeval fun o ↦ o.elim (Polynomial.C (y i))
      fun k ↦ update (Polynomial.C ∘ x) j Polynomial.X k) P ≠ 0 := by
    rw [algebraicIndependent_iff] at hy
    have := hx.1
    sorry
  use j
  let M : Subalgebra R A := (aeval (Function.update x j (y i))).range
  let N : Subalgebra R A := (aeval x).range
  let O : Subalgebra R A := (aeval (fun o => Option.elim o (y i) x)).range
  have hMO : M ≤ O := by
      simp only [M, O]
      rw [← adjoin_range_eq_range_aeval R, ← adjoin_range_eq_range_aeval R]
      apply Algebra.adjoin_mono
      rintro _ ⟨_, rfl⟩
      simp [Function.update, Option.exists]
      split_ifs <;> simp_all
  have hNO : N ≤ O := by
      simp only [N, O]
      rw [← adjoin_range_eq_range_aeval R, ← adjoin_range_eq_range_aeval R]
      apply Algebra.adjoin_mono
      rintro _ ⟨k, rfl⟩
      exact Set.mem_range.2 ⟨some k, by simp⟩
  let i1 : Algebra M O := RingHom.toAlgebra (Subalgebra.inclusion hMO).toRingHom
  have i2 : IsScalarTower M O A := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  let i3 : Algebra N O := RingHom.toAlgebra (Subalgebra.inclusion hNO).toRingHom
  have i4 : IsScalarTower N O A := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  let i5 : Algebra M A := RingHom.toAlgebra (Subalgebra.val _).toRingHom
  rw [adjoin_range_eq_range_aeval] at hx ⊢
  have h1 : Algebra.IsAlgebraic O A :=
    ⟨fun a => IsAlgebraic.extendScalars
      (Set.inclusion_injective (by exact hNO))
      (hx.isAlgebraic a)⟩
  let f : O →ₐ[M] A := AlgHom.mk (Subalgebra.val _).toRingHom (fun _ => rfl)
  have hf : Function.Injective f := Subtype.val_injective
  have hfr : f.range.restrictScalars R = O := by ext; simp [O, f]
  have hxjO : x j ∈ O := (AlgHom.mem_range _).2 ⟨MvPolynomial.X (some j), by simp⟩
  have h : (⊤ : Subalgebra M O) = Algebra.adjoin M {⟨x j, hxjO⟩} :=
    Subalgebra.map_injective hf <| by
    simp only [AlgHom.toRingHom_eq_coe, Algebra.map_top, AlgHom.map_adjoin_singleton, AlgHom.coe_mk,
      RingHom.coe_coe, coe_val, O, M]
    apply Subalgebra.restrictScalars_injective R
    rw [restrictScalars_adjoin, adjoin_union, adjoin_eq, hfr]
    simp only [O, Option.range_eq, ← adjoin_range_eq_range_aeval, Function.comp_def,
      Set.insert_eq, Algebra.adjoin_union]
    simp only [← adjoin_union, f]
    congr 1
    ext a
    simp only [Option.elim_none, Option.elim_some, singleton_union, mem_insert_iff, mem_range,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_mk, RingHom.coe_coe, coe_val, union_singleton, update,
      eq_rec_constant, dite_eq_ite, O, M, f]
    by_cases hay : a = y i
    · subst a; simp only [true_or, ite_eq_left_iff, true_iff, M, O, f]
      exact Or.inr ⟨j, by simp⟩
    · by_cases hax : a = x j
      · subst a; simp
      · simp only [hay, false_or, hax, M, O, f]
        refine exists_congr fun k => ?_
        split_ifs <;> aesop
  let OM : Subalgebra M A :=
      { O with algebraMap_mem' := fun r => hMO <| by simp [RingHom.algebraMap_toAlgebra] }
  have h2 : Algebra.IsAlgebraic M O := by
    refine ⟨fun a => ?_⟩
    rw [← isAlgebraic_algHom_iff f hf]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_mk, RingHom.coe_coe, coe_val, f]
    have haT : a ∈ (⊤ : Subalgebra M O) := mem_top
    erw [← @isAlgebraic_iff_isAlgebraic_val M A _ _ _ OM ⟨a, a.2⟩,
      ← @isAlgebraic_iff_isAlgebraic_val M O _ _ _ ⊤ ⟨⟨a, a.2⟩, haT⟩]
    suffices (adjoin M ({⟨x j, hxjO⟩} : Set O)).IsAlgebraic by
      { rw [← h] at this
        simp [Subalgebra.IsAlgebraic] at this
        convert this a a.2
        cases a; simp }
    rw [isAlgebraic_adjoin_singleton_iff, isAlgebraic_iff_isAlgebraic_val (R := M) (S := OM)]
    refine (isAlgebraic_adjoin_range_left_iff (adjoin_range_eq_range_aeval R _).symm).2 ?_
    use P.rename (fun o : Option ι => o.elim (some j) (Function.update some j none))
    refine ⟨?_, ?_⟩
    · convert hj using 1
      rw [aeval_rename]
      congr; ext o; cases o <;> simp [update]; split_ifs <;> simp_all
    · rw [← hP.2, aeval_rename]
      simp only [comp_def, O, i5, f, M, update]
      congr; ext o; cases o <;> simp [update]; split_ifs <;> simp_all
  refine IsAlgebraic.trans' M (S := O) Subtype.val_injective
