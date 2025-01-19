/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Matroid.IndepAxioms
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
  have ⟨s, hs⟩ := exists_maximal_algebraicIndependent ∅ _ (subset_univ _)
    ((algebraicIndependent_empty_iff R A).mpr h)
  simp_rw [subset_univ, and_true] at hs
  exact ⟨s, isTranscendenceBasis_iff_maximal.mpr hs.2⟩

/-- `Type` version of `exists_isTranscendenceBasis`. -/
theorem exists_isTranscendenceBasis' (R : Type u) {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] (h : Injective (algebraMap R A)) :
    ∃ (ι : Type v) (x : ι → A), IsTranscendenceBasis R x :=
  have ⟨s, h⟩ := exists_isTranscendenceBasis R h
  ⟨s, Subtype.val, h⟩

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

theorem AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic
    [Nontrivial R] (ind : AlgebraicIndependent R x) :
    IsTranscendenceBasis R x ↔ Algebra.IsAlgebraic (adjoin R (range x)) A := by
  refine ⟨(·.isAlgebraic), fun alg ↦ ⟨ind, fun s ind_s hxs ↦ of_not_not fun hxs' ↦ ?_⟩⟩
  have : ¬ s ⊆ range x := (hxs' <| hxs.antisymm ·)
  have ⟨a, has, hax⟩ := not_subset.mp this
  rw [show range x = Subtype.val '' range (Set.inclusion hxs) by
    rw [← range_comp, val_comp_inclusion, Subtype.range_val]] at alg
  refine ind_s.transcendental_adjoin (s := range (inclusion hxs)) (i := ⟨a, has⟩) ?_ (alg.1 _)
  simpa using hax

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

section Matroid

variable [NoZeroDivisors A] (inj : Injective (algebraMap R A))

/-- If `R` is a commutative ring and `A` is a commutative `R`-algebra with injective algebra map
and no zero divisors, then the `R`-algebraic independent subsets of `A` form a `IndepMatroid`. -/
def IndepMatroid.algebraicIndependent : IndepMatroid A where
  E := univ
  Indep s := AlgebraicIndependent R ((↑) : s → A)
  indep_empty := (algebraicIndependent_empty_iff ..).mpr inj
  indep_subset _ _ := (·.mono)
  indep_aug I B I_ind h B_base := by
    contrapose! h
    rw [← isTranscendenceBasis_iff_maximal] at B_base ⊢
    cases subsingleton_or_nontrivial R
    · rw [isTranscendenceBasis_iff_of_subsingleton] at B_base ⊢
      contrapose! h
      have ⟨b, hb⟩ := B_base
      exact ⟨b, ⟨hb, fun hbI ↦ h ⟨b, hbI⟩⟩, algebraicIndependent_of_subsingleton⟩
    rw [I_ind.isTranscendenceBasis_iff_isAlgebraic]
    replace B_base := B_base.isAlgebraic
    rw [Subtype.range_val] at B_base ⊢
    set RI := adjoin R I
    set RB := adjoin R B
    let RIB := adjoin RI B
    let _ : Algebra RB RIB := (Subalgebra.inclusion
      (T := RIB.restrictScalars R) <| adjoin_le_iff.mpr <| by apply subset_adjoin).toAlgebra
    have : IsScalarTower RB RIB A := .of_algebraMap_eq fun ⟨a, _⟩ ↦ show a = _ from rfl
    have : Algebra.IsAlgebraic RIB A := .extendScalars (R := RB) (Subalgebra.inclusion_injective _)
    have : Algebra.IsAlgebraic RI RIB := by
      have : Injective (algebraMap RI A) := Subtype.val_injective
      have := (isDomain_iff_noZeroDivisors_and_nontrivial RI).mpr ⟨this.noZeroDivisors _
        (map_zero _) (map_mul _), (Subtype.range_val ▸ I_ind.aevalEquiv).symm.nontrivial⟩
      rw [← Subalgebra.isAlgebraic_iff, isAlgebraic_adjoin_iff]
      intro x hB
      by_cases hI : x ∈ I
      · exact isAlgebraic_algebraMap (⟨x, subset_adjoin hI⟩ : RI)
      contrapose! h
      exact ⟨x, ⟨hB, hI⟩, (insert_iff hI).mpr ⟨I_ind, h⟩⟩
    exact IsAlgebraic.trans' (R := RI) (S := RIB) Subtype.val_injective
  indep_maximal X _ I ind hIX := exists_maximal_algebraicIndependent I X hIX ind
  subset_ground _ _ := subset_univ _

instance : (IndepMatroid.algebraicIndependent inj).matroid.Finitary where
  indep_of_forall_finite := algebraicIndependent_of_finite

section exchange_lemmas

variable [DecidableEq ι] {y : A} [NoZeroDivisors A]

open Algebra Set Function

theorem Algebra.IsAlgebraic.exchange_lemma
    (hx : Algebra.IsAlgebraic (adjoin R (range x)) A) (hy : Transcendental R y) :
    ∃ i : ι, Algebra.IsAlgebraic (adjoin R (range (update x i y))) A := by
  let xy (o : Option ι) := o.elim y x
  have : ¬ AlgebraicIndependent R xy := fun h ↦ by
    have := h.transcendental_adjoin (s := range some) (i := none) (by simp)
    rw [← range_comp] at this
    exact this (hx.1 y)
  have := mt (algebraicIndependent_of_set_of_finite {none} <|
    (algebraicIndependent_singleton_iff ⟨_, rfl⟩).mpr hy) this
  simp_rw [Transcendental] at this; push_neg at this
  obtain ⟨t, fin, ind, _|i, hi, hit, alg⟩ := this
  · exact (hi rfl).elim
  let Rxyi := adjoin R (range (update x i y))
  let _ : Algebra (adjoin R (xy '' t)) Rxyi := by
    refine (Subalgebra.inclusion <| adjoin_mono ?_).toAlgebra
    rintro _ ⟨_|j, hjt, rfl⟩
    · exact ⟨i, update_self ..⟩
    obtain rfl | ne := eq_or_ne j i
    exacts [(hit hjt).elim, ⟨j, update_of_ne ne ..⟩]
  have : IsScalarTower (adjoin R (xy '' t)) Rxyi A :=
    .of_algebraMap_eq fun ⟨a, _⟩ ↦ show a = _ from rfl
  have : IsAlgebraic Rxyi (x i) := alg.extendScalars <| by apply Subalgebra.inclusion_injective
  rw [← Algebra.isAlgebraic_adjoin_singleton_iff, Subalgebra.isAlgebraic_iff] at this
  set Rx := adjoin R (range x)
  set Rxy := adjoin Rxyi {x i}
  let _ : Algebra Rx Rxy := by
    refine (Subalgebra.inclusion (T := Rxy.restrictScalars R) ?_).toAlgebra
    refine adjoin_le_iff.mpr fun x ↦ ?_
    rintro ⟨j, rfl⟩; obtain rfl | ne := eq_or_ne j i
    · rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
      exact subset_adjoin rfl
    exact Subalgebra.algebraMap_mem _ (⟨_, subset_adjoin ⟨j, update_of_ne ne ..⟩⟩ : Rxyi)
  let _ : SMul Rx Rxy := Algebra.toSMul
  have : IsScalarTower Rx Rxy A :=
    .of_algebraMap_eq fun ⟨a, _⟩ ↦ show a = _ from rfl
  have : Algebra.IsAlgebraic Rxy A := .extendScalars (R := Rx) (Subalgebra.inclusion_injective _)
  let _ : Algebra Rxyi Rxy := inferInstance
  let _ : SMul Rxyi Rxy := Algebra.toSMul
  have : IsScalarTower Rxyi Rxy A := .of_algebraMap_eq fun ⟨a, _⟩ ↦ show a = _ from rfl
  exact ⟨i, Algebra.IsAlgebraic.trans' _ (S := Rxy) Subtype.val_injective⟩

theorem IsTranscendenceBasis.exchange_lemma
    (hx : IsTranscendenceBasis R x) (hy : Transcendental R y) :
    ∃ i : ι, IsTranscendenceBasis R (update x i y) := by
  cases subsingleton_or_nontrivial R
  · simp_rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢
    exact ⟨Classical.arbitrary _, hx⟩
  have ⟨i, hi⟩ := hx.isAlgebraic.exchange_lemma hy
  have : AlgebraicIndependent R (update x i y) := by
    rw [iff_transcendental_adjoin_image i]
    sorry
  exact ⟨i, this.isTranscendenceBasis_iff_isAlgebraic.mpr hi⟩

end exchange_lemmas
