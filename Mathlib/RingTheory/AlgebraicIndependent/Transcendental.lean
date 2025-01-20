/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.RingTheory.Algebraic.MvPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Algebraic Independence

This file relates algebraic independence and transcendence (or algebraicity) of elements.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## Tags
transcendence

-/

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u v

variable {ι ι' R : Type*} {S : Type u} {A : Type v} {x : ι → A}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- A one-element family `x` is algebraically independent if and only if
its element is transcendental. -/
@[simp]
theorem algebraicIndependent_unique_type_iff [Unique ι] :
    AlgebraicIndependent R x ↔ Transcendental R (x default) := by
  rw [transcendental_iff_injective, algebraicIndependent_iff_injective_aeval]
  let i := (renameEquiv R (Equiv.equivPUnit.{_, 1} ι)).trans (pUnitAlgEquiv R)
  have key : aeval (R := R) x = (Polynomial.aeval (R := R) (x default)).comp i := by
    ext y
    simp [i, Subsingleton.elim y default]
  simp [key]

theorem algebraicIndependent_singleton_iff [Subsingleton ι] (i : ι) :
    AlgebraicIndependent R x ↔ Transcendental R (x i) :=
  letI := uniqueOfSubsingleton i
  algebraicIndependent_unique_type_iff

/-- The one-element family `![x]` is algebraically independent if and only if
`x` is transcendental. -/
theorem algebraicIndependent_iff_transcendental {x : A} :
    AlgebraicIndependent R ![x] ↔ Transcendental R x := by
  simp

namespace AlgebraicIndependent

variable (hx : AlgebraicIndependent R x)
include hx

/-- If a family `x` is algebraically independent, then any of its element is transcendental. -/
theorem transcendental (i : ι) : Transcendental R (x i) := by
  have := hx.comp ![i] (Function.injective_of_subsingleton _)
  have : AlgebraicIndependent R ![x i] := by rwa [← FinVec.map_eq] at this
  rwa [← algebraicIndependent_iff_transcendental]

/-- If `A/R` is algebraic, then all algebraically independent families are empty. -/
theorem isEmpty_of_isAlgebraic [Algebra.IsAlgebraic R A] : IsEmpty ι := by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i⟩⟩
  · exact h
  exact False.elim (hx.transcendental i (Algebra.IsAlgebraic.isAlgebraic _))

end AlgebraicIndependent

theorem trdeg_eq_zero_of_isAlgebraic [Algebra.IsAlgebraic R A] : trdeg R A = 0 :=
  bot_unique <| ciSup_le' fun s ↦ have := s.2.isEmpty_of_isAlgebraic; (Cardinal.mk_eq_zero _).le

open AlgebraicIndependent

theorem AlgebraicIndependent.option_iff (hx : AlgebraicIndependent R x) (a : A) :
    AlgebraicIndependent R (fun o : Option ι ↦ o.elim a x) ↔
      Transcendental (adjoin R (range x)) a := by
  rw [algebraicIndependent_iff_injective_aeval, transcendental_iff_injective,
    ← AlgHom.coe_toRingHom, ← hx.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin,
    RingHom.coe_comp]
  exact Injective.of_comp_iff' (Polynomial.aeval a)
    (mvPolynomialOptionEquivPolynomialAdjoin hx).bijective

theorem AlgebraicIndependent.optionElim_iff {a : A} :
    AlgebraicIndependent R (fun o : Option ι ↦ o.elim a x) ↔
      AlgebraicIndependent R x ∧ Transcendental (adjoin R (range x)) a :=
  ⟨fun h ↦ have := h.comp _ (Option.some_injective _); ⟨this, (this.option_iff _).mp h⟩,
    fun h ↦ (h.1.option_iff _).mpr h.2⟩

theorem AlgebraicIndependent.insert_iff {s : Set A} {a : A} (h : a ∉ s) :
    AlgebraicIndependent R ((↑) : ↥(insert a s) → A) ↔
      AlgebraicIndependent R ((↑) : s → A) ∧ Transcendental (adjoin R s) a := by
  classical rw [← algebraicIndependent_equiv (subtypeInsertEquivOption h).symm]
  convert optionElim_iff (a := a) using 2
  · ext (_|_) <;> rfl
  · rw [Subtype.range_val]

theorem algebraicIndependent_of_set_of_finite (s : Set ι)
    (ind : AlgebraicIndependent R fun i : s ↦ x i)
    (H : ∀ t : Set ι, t.Finite → AlgebraicIndependent R (fun i : t ↦ x i) →
      ∀ i ∉ s, i ∉ t → Transcendental (adjoin R (x '' t)) (x i)) :
    AlgebraicIndependent R x := by
  classical
  refine algebraicIndependent_of_finite_type fun t hfin ↦ ?_
  suffices AlgebraicIndependent R fun i : ↥(t ∩ s ∪ t \ s) ↦ x i from
    this.comp (Equiv.Set.ofEq (t.inter_union_diff s).symm) (Equiv.injective _)
  refine hfin.diff.induction_on_subset _ (ind.comp (inclusion <| by simp) (inclusion_injective _))
    fun {a u} ha hu ha' h ↦ ?_
  have : a ∉ t ∩ s ∪ u := (·.elim (ha.2 ·.2) ha')
  convert (((image_eq_range _ _ ▸ h.option_iff <| x a).2 <| H _ (hfin.subset (union_subset
    inter_subset_left <| hu.trans diff_subset)) h a ha.2 this).comp _ (subtypeInsertEquivOption
    this).injective).comp (Equiv.Set.ofEq union_insert) (Equiv.injective _) with x
  by_cases h : ↑x = a <;> simp [h, Set.subtypeInsertEquivOption]

/-- Variant of `algebraicIndependent_of_finite_type` using `Transcendental`. -/
theorem algebraicIndependent_of_finite_type'
    (hinj : Injective (algebraMap R A))
    (H : ∀ t : Set ι, t.Finite → AlgebraicIndependent R (fun i : t ↦ x i) →
      ∀ i ∉ t, Transcendental (adjoin R (x '' t)) (x i)) :
    AlgebraicIndependent R x :=
  algebraicIndependent_of_set_of_finite ∅ (algebraicIndependent_empty_type_iff.mpr hinj)
    fun t ht ind i _ ↦ H t ht ind i

/-- Variant of `algebraicIndependent_of_finite` using `Transcendental`. -/
theorem algebraicIndependent_of_finite' (s : Set A)
    (hinj : Injective (algebraMap R A))
    (H : ∀ t ⊆ s, t.Finite → AlgebraicIndependent R ((↑) : t → A) →
      ∀ a ∈ s, a ∉ t → Transcendental (adjoin R t) a) :
    AlgebraicIndependent R ((↑) : s → A) :=
  algebraicIndependent_of_finite_type' hinj fun t hfin h i hi ↦ H _
    (by rintro _ ⟨x, _, rfl⟩; exact x.2) (hfin.image _) h.image _ i.2
    (mt Subtype.val_injective.mem_set_image.mp hi)

namespace AlgebraicIndependent

theorem sumElim_iff {ι'} {y : ι' → A} : AlgebraicIndependent R (Sum.elim y x) ↔
    AlgebraicIndependent R x ∧ AlgebraicIndependent (adjoin R (range x)) y := by
  by_cases hx : AlgebraicIndependent R x; swap
  · exact ⟨fun h ↦ (hx <| by apply h.comp _ Sum.inr_injective).elim, fun h ↦ (hx h.1).elim⟩
  let e := (sumAlgEquiv R ι' ι).trans (mapAlgEquiv _ hx.aevalEquiv)
  have : aeval (Sum.elim y x) = ((aeval y).restrictScalars R).comp e.toAlgHom := by
    ext (_|_) <;> simp [e, algebraMap_aevalEquiv]
  simp_rw [hx, AlgebraicIndependent, this]; simp

theorem iff_adjoin_image (s : Set ι) :
    AlgebraicIndependent R x ↔ AlgebraicIndependent R (fun i : s ↦ x i) ∧
      AlgebraicIndependent (adjoin R (x '' s)) fun i : ↥sᶜ ↦ x i := by
  rw [show x '' s = range fun i : s ↦ x i by ext; simp]
  convert ← sumElim_iff
  classical apply algebraicIndependent_equiv' ((Equiv.sumComm ..).trans (Equiv.Set.sumCompl ..))
  ext (_|_) <;> rfl

theorem iff_adjoin_image_compl (s : Set ι) :
    AlgebraicIndependent R x ↔ AlgebraicIndependent R (fun i : ↥sᶜ ↦ x i) ∧
      AlgebraicIndependent (adjoin R (x '' sᶜ)) fun i : s ↦ x i := by
  convert ← iff_adjoin_image _ <;> apply compl_compl

theorem iff_transcendental_adjoin_image (i : ι) :
    AlgebraicIndependent R x ↔ AlgebraicIndependent R (fun j : {j // j ≠ i} ↦ x j) ∧
      Transcendental (adjoin R (x '' {i}ᶜ)) (x i) :=
  (iff_adjoin_image_compl _).trans <| and_congr_right
    fun _ ↦ algebraicIndependent_unique_type_iff (ι := {j // j = i})

variable (hx : AlgebraicIndependent R x)
include hx

theorem sumElim {ι'} {y : ι' → A} (hy : AlgebraicIndependent (adjoin R (range x)) y) :
    AlgebraicIndependent R (Sum.elim y x) :=
  sumElim_iff.mpr ⟨hx, hy⟩

theorem sumElim_of_tower {ι'} {y : ι' → A} (hxS : range x ⊆ range (algebraMap S A))
    (hy : AlgebraicIndependent S y) : AlgebraicIndependent R (Sum.elim y x) := by
  let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R S A) hy.algebraMap_injective
  set Rx := adjoin R (range x)
  let _ : Algebra Rx S :=
    (e.symm.toAlgHom.comp <| Subalgebra.inclusion <| adjoin_le hxS).toAlgebra
  have : IsScalarTower Rx S A := .of_algebraMap_eq fun x ↦ show _ = (e (e.symm _)).1 by simp; rfl
  refine hx.sumElim (hy.restrictScalars (e.symm.injective.comp ?_))
  simpa only [AlgHom.coe_toRingHom] using Subalgebra.inclusion_injective _

omit hx in
theorem sumElim_comp {ι'} {x : ι → S} {y : ι' → A} (hx : AlgebraicIndependent R x)
    (hy : AlgebraicIndependent S y) : AlgebraicIndependent R (Sum.elim y (algebraMap S A ∘ x)) :=
  (hx.map' (f := IsScalarTower.toAlgHom R S A) hy.algebraMap_injective).sumElim_of_tower
    (range_comp_subset_range ..) hy

theorem adjoin_of_disjoint {s t : Set ι} (h : Disjoint s t) :
    AlgebraicIndependent (adjoin R (x '' s)) fun i : t ↦ x i :=
  ((iff_adjoin_image s).mp hx).2.comp (inclusion _) (inclusion_injective h.subset_compl_left)

theorem adjoin_iff_disjoint [Nontrivial A] {s t : Set ι} :
    (AlgebraicIndependent (adjoin R (x '' s)) fun i : t ↦ x i) ↔ Disjoint s t := by
  refine ⟨fun ind ↦ of_not_not fun ndisj ↦ ?_, adjoin_of_disjoint hx⟩
  have ⟨i, hs, ht⟩ := Set.not_disjoint_iff.mp ndisj
  refine ind.transcendental ⟨i, ht⟩ (isAlgebraic_algebraMap (⟨_, subset_adjoin ?_⟩ : adjoin R _))
  exact ⟨i, hs, rfl⟩

theorem transcendental_adjoin {s : Set ι} {i : ι} (hi : i ∉ s) :
    Transcendental (adjoin R (x '' s)) (x i) := by
  convert ← hx.adjoin_of_disjoint (Set.disjoint_singleton_right.mpr hi)
  rw [algebraicIndependent_singleton_iff ⟨i, rfl⟩]

theorem transcendental_adjoin_iff [Nontrivial A] {s : Set ι} {i : ι} :
    Transcendental (adjoin R (x '' s)) (x i) ↔ i ∉ s := by
  rw [← Set.disjoint_singleton_right]
  convert ← hx.adjoin_iff_disjoint (t := {i})
  rw [algebraicIndependent_singleton_iff ⟨i, rfl⟩]

end AlgebraicIndependent

open Cardinal in
theorem lift_trdeg_add_le [Nontrivial R]
    (hRS : Injective (algebraMap R S)) (hSA : Injective (algebraMap S A)) :
    lift.{v} (trdeg R S) + lift.{u} (trdeg S A) ≤ lift.{u} (trdeg R A) := by
  simp_rw [trdeg, lift_iSup (bddAbove_range _)]
  have := hRS.nonempty_algebraicIndependent
  have := hSA.nonempty_algebraicIndependent
  simp_rw [Cardinal.ciSup_add_ciSup _ (bddAbove_range _) _ (bddAbove_range _),
    add_comm (lift.{v, u} _), ← mk_sum]
  refine ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦ ?_
  have := hs.sumElim_comp ht
  refine le_ciSup_of_le (bddAbove_range _) ⟨_, this.to_subtype_range⟩ ?_
  rw [← lift_umax, mk_range_eq_of_injective this.injective, lift_id']

theorem trdeg_add_le [Nontrivial R] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] (hRS : Injective (algebraMap R S)) (hSA : Injective (algebraMap S A)) :
    trdeg R S + trdeg S A ≤ trdeg R A := by
  rw [← (trdeg R S).lift_id, ← (trdeg S A).lift_id, ← (trdeg R A).lift_id]
  exact lift_trdeg_add_le hRS hSA

/-- If for each `i : ι`, `f_i : R[X]` is transcendental over `R`, then `{f_i(X_i) | i : ι}`
in `MvPolynomial ι R` is algebraically independent over `R`. -/
theorem MvPolynomial.algebraicIndependent_polynomial_aeval_X
    (f : ι → Polynomial R) (hf : ∀ i, Transcendental R (f i)) :
    AlgebraicIndependent R fun i ↦ Polynomial.aeval (X i : MvPolynomial ι R) (f i) := by
  set x := fun i ↦ Polynomial.aeval (X i : MvPolynomial ι R) (f i)
  refine algebraicIndependent_of_finite_type' (C_injective _ _) fun t _ _ i hi ↦ ?_
  have hle : adjoin R (x '' t) ≤ supported R t := by
    rw [Algebra.adjoin_le_iff, Set.image_subset_iff]
    intro _ h
    rw [Set.mem_preimage]
    refine Algebra.adjoin_mono ?_ (Polynomial.aeval_mem_adjoin_singleton R _)
    simp_rw [singleton_subset_iff, Set.mem_image_of_mem _ h]
  exact (transcendental_supported_polynomial_aeval_X R hi (hf i)).of_tower_top_of_subalgebra_le hle

/-- If `{x_i : A | i : ι}` is algebraically independent over `R`, and for each `i`,
`f_i : R[X]` is transcendental over `R`, then `{f_i(x_i) | i : ι}` is also
algebraically independent over `R`. -/
theorem AlgebraicIndependent.polynomial_aeval_of_transcendental
    (hx : AlgebraicIndependent R x)
    {f : ι → Polynomial R} (hf : ∀ i, Transcendental R (f i)) :
    AlgebraicIndependent R fun i ↦ Polynomial.aeval (x i) (f i) := by
  convert aeval_of_algebraicIndependent hx (algebraicIndependent_polynomial_aeval_X _ hf)
  rw [← AlgHom.comp_apply]
  congr 1; ext1; simp
