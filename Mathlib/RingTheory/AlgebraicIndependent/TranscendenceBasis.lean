/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Matroid.Finitary
import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Transcendence basis

This file defines the transcendence basis as a maximal algebraically independent subset.

## Main results

* `exists_isTranscendenceBasis`: a ring extension has a transcendence basis
* `IsTranscendenceBasis.lift_cardinalMk_eq`: any two transcendence bases of a domain have the
  same cardinality.

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

universe u u' v w

variable {ι : Type u} {ι' : Type u'} (R : Type*) {S : Type v} {A : Type w}
variable {x : ι → A} {y : ι' → A}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

open AlgebraicIndependent

variable {R} in
theorem exists_isTranscendenceBasis_superset {s : Set A}
    (hs : AlgebraicIndependent R ((↑) : s → A)) :
    ∃ t, s ⊆ t ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  simpa only [subset_univ, and_true, ← isTranscendenceBasis_iff_maximal]
    using exists_maximal_algebraicIndependent s _ (subset_univ _) hs

theorem exists_isTranscendenceBasis (h : Injective (algebraMap R A)) :
    ∃ s : Set A, IsTranscendenceBasis R ((↑) : s → A) := by
  simpa only [empty_subset, true_and] using
    exists_isTranscendenceBasis_superset ((algebraicIndependent_empty_iff R A).mpr h)

/-- `Type` version of `exists_isTranscendenceBasis`. -/
theorem exists_isTranscendenceBasis' (R : Type u) {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] (h : Injective (algebraMap R A)) :
    ∃ (ι : Type v) (x : ι → A), IsTranscendenceBasis R x :=
  have ⟨s, h⟩ := exists_isTranscendenceBasis R h
  ⟨s, Subtype.val, h⟩

open Cardinal in
theorem trdeg_eq_iSup_cardinalMk_isTranscendenceBasis :
    trdeg R A = ⨆ ι : { s : Set A // IsTranscendenceBasis R ((↑) : s → A) }, #ι.1 := by
  refine (ciSup_le' fun s ↦ ?_).antisymm
    (ciSup_le' fun s ↦ le_ciSup_of_le (bddAbove_range _) ⟨s, s.2.1⟩ le_rfl)
  choose t ht using exists_isTranscendenceBasis_superset s.2
  exact le_ciSup_of_le (bddAbove_range _) ⟨t, ht.2⟩ (mk_le_mk_of_subset ht.1)

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

theorem isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic [Nontrivial R] :
    IsTranscendenceBasis R x ↔
      AlgebraicIndependent R x ∧ Algebra.IsAlgebraic (adjoin R (range x)) A :=
  ⟨fun h ↦ ⟨h.1, h.1.isTranscendenceBasis_iff_isAlgebraic.mp h⟩,
    fun ⟨ind, alg⟩ ↦ ind.isTranscendenceBasis_iff_isAlgebraic.mpr alg⟩

theorem IsTranscendenceBasis.sumElim_comp [NoZeroDivisors A] {x : ι → S} {y : ι' → A}
    (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis S y) :
    IsTranscendenceBasis R (Sum.elim y (algebraMap S A ∘ x)) := by
  cases subsingleton_or_nontrivial R
  · rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢; infer_instance
  rw [(hx.1.sumElim_comp hy.1).isTranscendenceBasis_iff_isAlgebraic]
  set Rx := adjoin R (range x)
  let Rxy := adjoin Rx (range y)
  rw [show adjoin R (range <| Sum.elim y (algebraMap S A ∘ x)) = Rxy.restrictScalars R by
    rw [← adjoin_algebraMap_image_union_eq_adjoin_adjoin, Sum.elim_range, union_comm, range_comp]]
  show Algebra.IsAlgebraic Rxy A
  have := hx.1.algebraMap_injective.nontrivial
  have := hy.1.algebraMap_injective.nontrivial
  have := hy.isAlgebraic
  set Sy := adjoin S (range y)
  let _ : Algebra Rxy Sy := by
    refine (Subalgebra.inclusion (T := Sy.restrictScalars Rx) <| adjoin_le ?_).toAlgebra
    rintro _ ⟨i, rfl⟩; exact subset_adjoin (s := range y) ⟨i, rfl⟩
  have : IsScalarTower Rxy Sy A := .of_algebraMap_eq fun ⟨a, _⟩ ↦ show a = _ from rfl
  have : IsScalarTower Rx Rxy Sy := .of_algebraMap_eq fun ⟨a, _⟩ ↦ Subtype.ext rfl
  have : Algebra.IsAlgebraic Rxy Sy := by
    refine ⟨fun ⟨a, ha⟩ ↦ adjoin_induction ?_ (fun _ ↦ .extendScalars (R := Rx) ?_ ?_)
      (fun _ _ _ _ ↦ IsAlgebraic.add) (fun _ _ _ _ ↦ IsAlgebraic.mul) ha⟩
    · rintro _ ⟨i, rfl⟩; exact isAlgebraic_algebraMap (⟨y i, subset_adjoin ⟨i, rfl⟩⟩ : Rxy)
    · exact fun _ _ ↦ (Subtype.ext <| hy.1.algebraMap_injective <| Subtype.ext_iff.mp ·)
    · exact (hx.isAlgebraic.1 _).algHom (IsScalarTower.toAlgHom Rx S Sy)
  exact .trans' _ (S := Sy) Subtype.val_injective

/-- If `s ⊆ t` are subsets in an `R`-algebra `A` such that `s` is algebraically independent over
`R`, and `A` is algebraic over the `R`-algebra generated by `t`, then there is a transcendence
basis of `A` over `R` between `s` and `t`, provided that `A` is a domain.

This may fail if only `R` is assumed to be a domain but `A` is not, because of failure of
transitivity of algebraicity: there may exist `a : A` such that `S := R[a]` is algebraic over
`R` and `A` is algebraic over `S`, but `A` nonetheless contains a transcendental element over `R`.
The only `R`-algebraically independent subset of `{a}` is `∅`, which is not a transcendence basis.
See the docstring of `IsAlgebraic.restrictScalars_of_isIntegral` for an example. -/
theorem exists_isTranscendenceBasis_between [NoZeroDivisors A] (s t : Set A) (hst : s ⊆ t)
    (hs : AlgebraicIndependent R ((↑) : s → A)) [ht : Algebra.IsAlgebraic (adjoin R t) A] :
    ∃ u, s ⊆ u ∧ u ⊆ t ∧ IsTranscendenceBasis R ((↑) : u → A) := by
  have ⟨u, hu⟩ := exists_maximal_algebraicIndependent s t hst hs
  refine ⟨u, hu.1, hu.2.1.2, ?_⟩
  have := ht.nontrivial
  have := Module.nontrivial R (adjoin R t)
  rw [hu.2.1.1.isTranscendenceBasis_iff_isAlgebraic, Subtype.range_val]
  rw [← union_diff_cancel hu.2.1.2, adjoin_union_eq_adjoin_adjoin] at ht
  set Ru := adjoin R u
  set Rt := adjoin Ru (t \ u)
  change Algebra.IsAlgebraic Rt A at ht
  have : Algebra.IsAlgebraic Ru Rt := by
    have := ht.nontrivial
    have := (isDomain_iff_noZeroDivisors_and_nontrivial Ru).mpr
      ⟨inferInstance, Module.nontrivial Ru Rt⟩
    rw [← Subalgebra.isAlgebraic_iff, isAlgebraic_adjoin_iff]
    exact fun a ha ↦ of_not_not fun (hua : Transcendental _ _) ↦ ha.2 (hu.2.2 ⟨(insert_iff ha.2).mpr
      ⟨hu.2.1.1, hua⟩, insert_subset ha.1 hu.2.1.2⟩ (subset_insert ..) (mem_insert ..))
  exact .trans' _ (S := Rt) Subtype.val_injective

theorem exists_isTranscendenceBasis_subset [NoZeroDivisors A] (inj : Injective (algebraMap R A))
    (s : Set A) [Algebra.IsAlgebraic (adjoin R s) A] :
    ∃ t, t ⊆ s ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  have ⟨t, _, ht⟩ := exists_isTranscendenceBasis_between ∅ s (empty_subset _)
    ((algebraicIndependent_empty_iff ..).mpr inj)
  exact ⟨t, ht⟩

theorem isAlgebraic_iff_exists_isTranscendenceBasis_subset
    [Nontrivial R] [NoZeroDivisors A] (inj : Injective (algebraMap R A)) {s : Set A} :
    Algebra.IsAlgebraic (adjoin R s) A ↔ ∃ t, t ⊆ s ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  refine ⟨fun h ↦ exists_isTranscendenceBasis_subset inj s, fun ⟨t, hts, ht⟩ ↦ ?_⟩
  let _ : Algebra (adjoin R t) (adjoin R s) := (Subalgebra.inclusion <| adjoin_mono hts).toAlgebra
  have : IsScalarTower (adjoin R t) (adjoin R s) A :=
    .of_algebraMap_eq fun ⟨a, _⟩ ↦ show a = _ from rfl
  have : Algebra.IsAlgebraic (adjoin R t) A := by apply Subtype.range_val ▸ ht.isAlgebraic
  exact .extendScalars (R := adjoin R t) (Subalgebra.inclusion_injective _)

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

namespace AlgebraicIndependent

variable [NoZeroDivisors A] (inj : Injective (algebraMap R A))

private def indepMatroid : IndepMatroid A where
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
      (T := RIB.restrictScalars R) <| adjoin_le <| by apply subset_adjoin).toAlgebra
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
    exact .trans' (R := RI) (S := RIB) Subtype.val_injective
  indep_maximal X _ I ind hIX := exists_maximal_algebraicIndependent I X hIX ind
  subset_ground _ _ := subset_univ _

/-- If `R` is a commutative ring and `A` is a commutative `R`-algebra with injective algebra map
and no zero-divisors, then the `R`-algebraic independent subsets of `A` form a matroid. -/
def matroid : Matroid A := (indepMatroid inj).matroid

instance : (matroid inj).Finitary where
  indep_of_forall_finite := algebraicIndependent_of_finite

theorem matroid_indep_iff {s : Set A} :
    (matroid inj).Indep s ↔ AlgebraicIndependent R ((↑) : s → A) := Iff.rfl

theorem matroid_base_iff {s : Set A} :
    (matroid inj).Base s ↔ IsTranscendenceBasis R ((↑) : s → A) := by
  rw [Matroid.base_iff_maximal_indep, isTranscendenceBasis_iff_maximal]; rfl

end AlgebraicIndependent

open Cardinal AlgebraicIndependent

namespace IsTranscendenceBasis

variable [Nontrivial R] [NoZeroDivisors A]

/-- Any two transcendence bases of a domain `A` have the same cardinality.
May fail if `A` is not a domain; see https://mathoverflow.net/a/144580. -/
@[stacks 030F]
theorem lift_cardinalMk_eq (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis R y) :
    lift.{u'} #ι = lift.{u} #ι' := by
  have inj := hx.1.algebraMap_injective
  replace hx' := hx.to_subtype_range
  replace hy' := hy.to_subtype_range
  rw [← matroid_base_iff inj] at hx' hy'
  have := hx'.cardinalMk_eq_of_finitary hy'
  rwa [← lift_inj.{_, max u u'}, ← lift_lift.{u, u'}, ← lift_lift.{u', u},
    ← lift_mk_eq'.mpr ⟨.ofInjective _ hx.1.injective⟩, lift_lift,
    ← lift_mk_eq'.mpr ⟨.ofInjective _ hy.1.injective⟩, lift_lift,
    ← lift_lift.{u', w}, ← lift_lift.{u, w}, lift_inj] at this

theorem lift_cardinalMk_eq_trdeg (hx : IsTranscendenceBasis R x) :
    lift.{w} #ι = lift.{u} (trdeg R A) := by
  rw [trdeg_eq_iSup_cardinalMk_isTranscendenceBasis, lift_iSup (bddAbove_range _)]
  exact (le_ciSup_of_le (bddAbove_range _) ⟨_, hx.to_subtype_range⟩
      (lift_mk_eq'.mpr ⟨.ofInjective _ hx.1.injective⟩).le).antisymm
    (ciSup_le' fun s ↦ (lift_cardinalMk_eq s.2 hx).le)

@[stacks 030F] theorem cardinalMk_eq {ι' : Type u} {y : ι' → A}
    (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis R y) :
    #ι = #ι' := by
  rw [← lift_id #ι, lift_cardinalMk_eq hx hy, lift_id]

theorem cardinalMk_eq_trdeg {ι : Type w} {x : ι → A} (hx : IsTranscendenceBasis R x) :
    #ι = trdeg R A := by
  rw [← lift_id #ι, lift_cardinalMk_eq_trdeg hx, lift_id]

end IsTranscendenceBasis

namespace Algebra.IsAlgebraic

variable (R x)

lemma notrivial_of_adjoin_range [Algebra.IsAlgebraic (adjoin R (range x)) A] : Nontrivial R :=
  have := Algebra.IsAlgebraic.nontrivial (adjoin R (range x)) A
  Module.nontrivial R (adjoin R (range x))

variable [NoZeroDivisors A]

theorem lift_trdeg_le_cardinalMk [alg : Algebra.IsAlgebraic (adjoin R (range x)) A] :
    lift.{u} (trdeg R A) ≤ lift.{w} #ι := by
  by_cases h : Injective (algebraMap R A)
  on_goal 2 => simp [trdeg_eq_zero_of_not_injective h]
  have := notrivial_of_adjoin_range R x
  have ⟨t, htx, ht⟩ := (isAlgebraic_iff_exists_isTranscendenceBasis_subset h).mp alg
  rw [← ht.cardinalMk_eq_trdeg]
  exact (lift_le.mpr <| mk_le_mk_of_subset htx).trans mk_range_le_lift

theorem trdeg_le_cardinalMk {ι : Type w} (x : ι → A) [Algebra.IsAlgebraic (adjoin R (range x)) A] :
    trdeg R A ≤ #ι := by
  rw [← (trdeg R A).lift_id, ← (#ι).lift_id]; exact lift_trdeg_le_cardinalMk R x

variable (inj : Injective (algebraMap R A))
include inj

theorem lift_cardinalMk_eq_trdeg_iff_of_finite
    [Finite ι] [alg : Algebra.IsAlgebraic (adjoin R (range x)) A] :
    lift.{w} #ι = lift.{u} (trdeg R A) ↔ IsTranscendenceBasis R x := by
  have := notrivial_of_adjoin_range R x
  simp_rw [le_antisymm_iff, lift_trdeg_le_cardinalMk R x,
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic, alg, and_true]
  refine ⟨fun le ↦ ?_, (·.lift_cardinalMk_le_trdeg)⟩
  have ⟨s, hsx, hs⟩ := exists_isTranscendenceBasis_subset inj (range x)
  rw [← hs.cardinalMk_eq_trdeg] at le
  obtain rfl := (finite_range x).eq_of_subset_of_encard_le hsx
    (toENat.monotone' <| lift_le.{u}.mp <| mk_range_le_lift.trans le)
  have ⟨_, inj⟩ := lift_mk_le'.mp le
  have := surjective_onto_range.bijective_of_nat_card_le (Nat.card_le_card_of_injective _ inj)
  exact .of_subtype_range (fun _ _ ↦ (this.1 <| Subtype.ext ·)) hs.1

theorem cardinalMk_eq_trdeg_iff_of_finite {ι : Type w} [Finite ι] (x : ι → A)
    [Algebra.IsAlgebraic (adjoin R (range x)) A] :
    #ι = trdeg R A ↔ IsTranscendenceBasis R x := by
  rw [← lift_cardinalMk_eq_trdeg_iff_of_finite R x inj, lift_id, lift_id]

theorem lift_cardinalMk_eq_trdeg_iff [Algebra.IsAlgebraic (adjoin R (range x)) A]
    (fin : trdeg R A < ℵ₀) : lift.{w} #ι = lift.{u} (trdeg R A) ↔ IsTranscendenceBasis R x := by
  have := notrivial_of_adjoin_range R x
  refine ⟨fun h ↦ ?_, (·.lift_cardinalMk_eq_trdeg)⟩
  have := mk_lt_aleph0_iff.mp (lift_lt_aleph0.mp (lift_aleph0 ▸ h ▸ lift_lt.{_, u}.mpr fin))
  exact (lift_cardinalMk_eq_trdeg_iff_of_finite R x inj).mp h

theorem cardinalMk_eq_trdeg_iff {ι : Type w} (x : ι → A)
    [Algebra.IsAlgebraic (adjoin R (range x)) A] (fin : trdeg R A < ℵ₀) :
    #ι = trdeg R A ↔ IsTranscendenceBasis R x := by
  rw [← lift_cardinalMk_eq_trdeg_iff R x inj fin, lift_id, lift_id]

end Algebra.IsAlgebraic

namespace AlgebraicIndependent

variable [Nontrivial R] [NoZeroDivisors A]

theorem lift_cardinalMk_eq_trdeg_iff_of_finite [Finite ι] (hx : AlgebraicIndependent R x) :
    lift.{w} #ι = lift.{u} (trdeg R A) ↔ IsTranscendenceBasis R x := by
  have ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset hx.to_subtype_range
  refine ⟨fun h ↦ ?_, (·.lift_cardinalMk_eq_trdeg)⟩
  rw [← hs.cardinalMk_eq_trdeg, ← mk_range_eq_of_injective hx.injective, lift_inj] at h
  obtain rfl := (finite_range x).eq_of_subset_of_encard_le' hxs (toENat.monotone' h.ge)
  exact .of_subtype_range hx.injective hs

theorem cardinalMk_eq_trdeg_iff_of_finite {ι : Type w} [Finite ι] {x : ι → A}
    (hx : AlgebraicIndependent R x) : #ι = trdeg R A ↔ IsTranscendenceBasis R x := by
  rw [← lift_cardinalMk_eq_trdeg_iff_of_finite hx, lift_id, lift_id]

theorem lift_cardinalMk_eq_trdeg_iff (hx : AlgebraicIndependent R x) (fin : trdeg R A < ℵ₀) :
    lift.{w} #ι = lift.{u} (trdeg R A) ↔ IsTranscendenceBasis R x := by
  refine ⟨fun h ↦ ?_, (·.lift_cardinalMk_eq_trdeg)⟩
  have := mk_lt_aleph0_iff.mp (lift_lt_aleph0.mp (lift_aleph0 ▸ h ▸ lift_lt.{_, u}.mpr fin))
  exact (lift_cardinalMk_eq_trdeg_iff_of_finite hx).mp h

theorem cardinalMk_eq_trdeg_iff {ι : Type w} {x : ι → A} (hx : AlgebraicIndependent R x)
    (fin : trdeg R A < ℵ₀) : #ι = trdeg R A ↔ IsTranscendenceBasis R x := by
  rw [← lift_cardinalMk_eq_trdeg_iff hx fin, lift_id, lift_id]

end AlgebraicIndependent

@[stacks 030H] theorem lift_trdeg_add_eq [Nontrivial R] [NoZeroDivisors A]
    (hRS : Injective (algebraMap R S)) (hSA : Injective (algebraMap S A)) :
    lift.{w} (trdeg R S) + lift.{v} (trdeg S A) = lift.{v} (trdeg R A) := by
  have ⟨s, hs⟩ := exists_isTranscendenceBasis _ hRS
  have ⟨t, ht⟩ := exists_isTranscendenceBasis _ hSA
  have := hSA.noZeroDivisors _ (map_zero _) (map_mul _)
  have := hRS.nontrivial
  rw [← hs.cardinalMk_eq_trdeg, ← ht.cardinalMk_eq_trdeg, ← lift_umax.{w}, add_comm,
    ← (hs.sumElim_comp ht).lift_cardinalMk_eq_trdeg, mk_sum, lift_add, lift_lift, lift_lift]

@[stacks 030H] theorem trdeg_add_eq [Nontrivial R] {A : Type v} [CommRing A] [NoZeroDivisors A]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    (hRS : Injective (algebraMap R S)) (hSA : Injective (algebraMap S A)) :
    trdeg R S + trdeg S A = trdeg R A := by
  rw [← (trdeg R S).lift_id, ← (trdeg S A).lift_id, ← (trdeg R A).lift_id]
  exact lift_trdeg_add_eq hRS hSA
