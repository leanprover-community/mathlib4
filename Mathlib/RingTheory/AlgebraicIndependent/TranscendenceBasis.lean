/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matroid.Rank.Cardinal
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
    (hs : AlgebraicIndepOn R id s) :
    ∃ t, s ⊆ t ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  simpa [← isTranscendenceBasis_iff_maximal]
    using exists_maximal_algebraicIndependent s _ (subset_univ _) hs

variable (A)
theorem exists_isTranscendenceBasis [FaithfulSMul R A] :
    ∃ s : Set A, IsTranscendenceBasis R ((↑) : s → A) := by
  simpa using exists_isTranscendenceBasis_superset
    ((algebraicIndependent_empty_iff R A).mpr (FaithfulSMul.algebraMap_injective R A))

/-- `Type` version of `exists_isTranscendenceBasis`. -/
theorem exists_isTranscendenceBasis' [FaithfulSMul R A] :
    ∃ (ι : Type w) (x : ι → A), IsTranscendenceBasis R x :=
  have ⟨s, h⟩ := exists_isTranscendenceBasis R A
  ⟨s, Subtype.val, h⟩

variable {A}

open Cardinal in
theorem trdeg_eq_iSup_cardinalMk_isTranscendenceBasis :
    trdeg R A = ⨆ ι : { s : Set A // IsTranscendenceBasis R ((↑) : s → A) }, #ι.1 := by
  refine (ciSup_le' fun s ↦ ?_).antisymm
    (ciSup_le' fun s ↦ le_ciSup_of_le (bddAbove_range _) ⟨s, s.2.1⟩ le_rfl)
  choose t ht using exists_isTranscendenceBasis_superset s.2
  exact le_ciSup_of_le (bddAbove_range _) ⟨t, ht.2⟩ (mk_le_mk_of_subset ht.1)

variable {R}

theorem AlgebraicIndependent.isTranscendenceBasis_iff [Nontrivial R]
    (i : AlgebraicIndependent R x) :
    IsTranscendenceBasis R x ↔
      ∀ (κ : Type w) (w : κ → A) (_ : AlgebraicIndependent R w) (j : ι → κ) (_ : w ∘ j = x),
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
  rw [← not_iff_comm.1 (hx.1.option_iff_transcendental _).symm]
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

lemma IsTranscendenceBasis.algebraMap_comp
    [Nontrivial R] [NoZeroDivisors S] [Algebra.IsAlgebraic S A] [FaithfulSMul S A]
    {x : ι → S} (hx : IsTranscendenceBasis R x) : IsTranscendenceBasis R (algebraMap S A ∘ x) := by
  let f := IsScalarTower.toAlgHom R S A
  refine hx.1.map (f := f) (FaithfulSMul.algebraMap_injective S A).injOn
    |>.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  rw [Set.range_comp, ← AlgHom.map_adjoin]
  set Rx := adjoin R (range x)
  let e := Rx.equivMapOfInjective f (FaithfulSMul.algebraMap_injective S A)
  letI := e.toRingHom.toAlgebra
  haveI : IsScalarTower Rx (Rx.map f) A := .of_algebraMap_eq fun x ↦ rfl
  have : Algebra.IsAlgebraic Rx S := hx.isAlgebraic
  have : Algebra.IsAlgebraic Rx A := .trans _ S _
  exact .extendScalars e.injective

lemma IsTranscendenceBasis.isAlgebraic_iff [IsDomain S] [NoZeroDivisors A]
    {ι : Type*} {v : ι → A} (hv : IsTranscendenceBasis R v) :
    Algebra.IsAlgebraic S A ↔ ∀ i, IsAlgebraic S (v i) := by
  refine ⟨fun _ i ↦ Algebra.IsAlgebraic.isAlgebraic (v i), fun H ↦ ?_⟩
  let Rv := adjoin R (range v)
  let Sv := adjoin S (range v)
  have : Algebra.IsAlgebraic S Sv := by
    simpa [Sv, ← Subalgebra.isAlgebraic_iff, isAlgebraic_adjoin_iff]
  have le : Rv ≤ Sv.restrictScalars R := by
    rw [Subalgebra.restrictScalars_adjoin]; exact le_sup_right
  letI : Algebra Rv Sv := (Subalgebra.inclusion le).toAlgebra
  have : IsScalarTower Rv Sv A := .of_algebraMap_eq fun x ↦ rfl
  have := (algebraMap R S).domain_nontrivial
  have := hv.isAlgebraic
  have : Algebra.IsAlgebraic Sv A := .extendScalars (Subalgebra.inclusion_injective le)
  exact .trans _ Sv _

variable (ι R)

theorem IsTranscendenceBasis.mvPolynomial [Nontrivial R] :
    IsTranscendenceBasis R (X (R := R) (σ := ι)) := by
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨algebraicIndependent_X .., ?_⟩
  rw [adjoin_range_X]
  set A := MvPolynomial ι R
  have := Algebra.isIntegral_of_surjective (R := (⊤ : Subalgebra R A)) (B := A) (⟨⟨·, ⟨⟩⟩, rfl⟩)
  infer_instance

theorem IsTranscendenceBasis.mvPolynomial' [Nonempty ι] :
    IsTranscendenceBasis R (X (R := R) (σ := ι)) := by nontriviality R; exact .mvPolynomial ι R

theorem IsTranscendenceBasis.polynomial [Nonempty ι] [Subsingleton ι] :
    IsTranscendenceBasis R fun _ : ι ↦ (.X : Polynomial R) := by
  nontriviality R
  have := (nonempty_unique ι).some
  refine (isTranscendenceBasis_equiv (Equiv.equivPUnit.{_, 1} _).symm).mp <|
    (MvPolynomial.pUnitAlgEquiv R).symm.isTranscendenceBasis_iff.mp ?_
  convert IsTranscendenceBasis.mvPolynomial PUnit R
  ext; simp

variable {ι R}

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
  change Algebra.IsAlgebraic Rxy A
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
      (fun _ _ _ _ ↦ .add) (fun _ _ _ _ ↦ .mul) ha⟩
    · rintro _ ⟨i, rfl⟩; exact isAlgebraic_algebraMap (⟨y i, subset_adjoin ⟨i, rfl⟩⟩ : Rxy)
    · exact fun _ _ ↦ (Subtype.ext <| hy.1.algebraMap_injective <| Subtype.ext_iff.mp ·)
    · exact (hx.isAlgebraic.1 _).algHom (IsScalarTower.toAlgHom Rx S Sy)
  exact .trans _ Sy _

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

variable (R A) [FaithfulSMul R A]

section

variable [NoZeroDivisors A]

private def indepMatroid : IndepMatroid A where
  E := univ
  Indep := AlgebraicIndepOn R id
  indep_empty := (algebraicIndependent_empty_iff ..).mpr (FaithfulSMul.algebraMap_injective R A)
  indep_subset _ _ := (·.mono)
  indep_aug I B I_ind h B_base := by
    contrapose! h
    rw [← isTranscendenceBasis_iff_maximal] at B_base ⊢
    cases subsingleton_or_nontrivial R
    · rw [isTranscendenceBasis_iff_of_subsingleton] at B_base ⊢
      contrapose! h
      have ⟨b, hb⟩ := B_base
      exact ⟨b, ⟨hb, fun hbI ↦ h ⟨b, hbI⟩⟩, .of_subsingleton⟩
    apply I_ind.isTranscendenceBasis_iff_isAlgebraic.mpr
    replace B_base := B_base.isAlgebraic
    simp_rw [id_eq]
    rw [Subtype.range_val] at B_base ⊢
    refine ⟨fun a ↦ (B_base.1 a).adjoin_of_forall_isAlgebraic fun x hx ↦ ?_⟩
    contrapose! h
    exact ⟨x, hx, I_ind.insert <| by rwa [image_id]⟩
  indep_maximal X _ I ind hIX := exists_maximal_algebraicIndependent I X hIX ind
  subset_ground _ _ := subset_univ _

/-- If `R` is a commutative ring and `A` is a commutative `R`-algebra with injective algebra map
and no zero-divisors, then the `R`-algebraic independent subsets of `A` form a matroid. -/
def matroid : Matroid A := (indepMatroid R A).matroid.copyBase univ
  (fun s ↦ IsTranscendenceBasis R ((↑) : s → A)) rfl
  (fun B ↦ by simp_rw [Matroid.isBase_iff_maximal_indep, isTranscendenceBasis_iff_maximal]; rfl)

instance : (matroid R A).Finitary where
  indep_of_forall_finite := algebraicIndependent_of_finite

@[simp] theorem matroid_e : (matroid R A).E = univ := rfl

theorem matroid_cRank_eq : (matroid R A).cRank = trdeg R A :=
  (trdeg_eq_iSup_cardinalMk_isTranscendenceBasis _).symm

variable {R A}

theorem matroid_indep_iff {s : Set A} :
    (matroid R A).Indep s ↔ AlgebraicIndepOn R id s := Iff.rfl

theorem matroid_isBase_iff {s : Set A} :
    (matroid R A).IsBase s ↔ IsTranscendenceBasis R ((↑) : s → A) := Iff.rfl

end

variable {R A}

theorem matroid_isBasis_iff [IsDomain A] {s t : Set A} : (matroid R A).IsBasis s t ↔
    AlgebraicIndepOn R id s ∧ s ⊆ t ∧ ∀ a ∈ t, IsAlgebraic (adjoin R s) a := by
  rw [Matroid.IsBasis, maximal_iff_forall_insert fun s t h hst ↦ ⟨h.1.subset hst, hst.trans h.2⟩]
  simp_rw [matroid_indep_iff, ← and_assoc, matroid_e, subset_univ, and_true]
  exact and_congr_right fun h ↦ ⟨fun max a ha ↦ of_not_not fun tr ↦ max _
    (fun ha ↦ tr (isAlgebraic_algebraMap (⟨a, subset_adjoin ha⟩ : adjoin R s)))
      ⟨.insert h.1 (by rwa [image_id]), insert_subset ha h.2⟩,
    fun alg a ha h ↦ ((AlgebraicIndepOn.insert_iff ha).mp h.1).2 <| by
      rw [image_id]; exact alg _ <| h.2 <| mem_insert ..⟩

open Subsingleton in
theorem matroid_isBasis_iff_of_subsingleton [Subsingleton A] {s t : Set A} :
    (matroid R A).IsBasis s t ↔ s = t := by
  have := (FaithfulSMul.algebraMap_injective R A).subsingleton
  simp_rw [Matroid.IsBasis, matroid_indep_iff, of_subsingleton, true_and,
    matroid_e, subset_univ, and_true, ← le_iff_subset, maximal_le_iff]

theorem isAlgebraic_adjoin_iff_of_matroid_isBasis [NoZeroDivisors A] {s t : Set A} {a : A}
    (h : (matroid R A).IsBasis s t) : IsAlgebraic (adjoin R s) a ↔ IsAlgebraic (adjoin R t) a := by
  cases subsingleton_or_nontrivial A
  · apply iff_of_false <;> apply is_transcendental_of_subsingleton
  have := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨(·.adjoin_of_forall_isAlgebraic fun x hx ↦ (hx.2 <| h.1.1.2 hx.1).elim),
    (·.adjoin_of_forall_isAlgebraic fun x hx ↦ (matroid_isBasis_iff.mp h).2.2 _ hx.1)⟩

theorem matroid_closure_eq [IsDomain A] {s : Set A} :
    (matroid R A).closure s = algebraicClosure (adjoin R s) A := by
  have ⟨B, hB⟩ := (matroid R A).exists_isBasis s
  simp_rw [← hB.closure_eq_closure, hB.1.1.1.closure_eq_setOf_isBasis_insert, Set.ext_iff,
    mem_setOf, matroid_isBasis_iff, ← matroid_indep_iff, hB.1.1.1, subset_insert, true_and,
    SetLike.mem_coe, mem_algebraicClosure, ← isAlgebraic_adjoin_iff_of_matroid_isBasis hB,
    forall_mem_insert]
  exact fun _ ↦ and_iff_left fun x hx ↦ isAlgebraic_algebraMap (⟨x, subset_adjoin hx⟩ : adjoin R B)

theorem matroid_isFlat_iff [IsDomain A] {s : Set A} :
    (matroid R A).IsFlat s ↔ ∃ S : Subalgebra R A, S = s ∧ ∀ a : A, IsAlgebraic S a → a ∈ s := by
  rw [Matroid.isFlat_iff_closure_eq, matroid_closure_eq]
  set S := algebraicClosure (adjoin R s) A
  refine ⟨fun eq ↦ ⟨S.restrictScalars R, eq, fun a (h : IsAlgebraic S _) ↦ ?_⟩, ?_⟩
  · rw [← eq]; exact h.restrictScalars (adjoin R s)
  rintro ⟨s, rfl, hs⟩
  refine Set.ext fun a ↦ ⟨(hs _ <| adjoin_eq s ▸ ·), fun h ↦ ?_⟩
  exact isAlgebraic_algebraMap (A := A) (by exact (⟨a, subset_adjoin h⟩ : adjoin R s))

theorem matroid_spanning_iff [IsDomain A] {s : Set A} :
    (matroid R A).Spanning s ↔ Algebra.IsAlgebraic (adjoin R s) A := by
  simp_rw [Matroid.spanning_iff, matroid_e, subset_univ, and_true, eq_univ_iff_forall,
    matroid_closure_eq, SetLike.mem_coe, mem_algebraicClosure, Algebra.isAlgebraic_def]

open Subsingleton -- brings the Subsingleton.to_noZeroDivisors instance into scope

theorem matroid_isFlat_of_subsingleton [Subsingleton A] (s : Set A) : (matroid R A).IsFlat s := by
  simp_rw [Matroid.isFlat_iff, matroid_e, subset_univ,
    and_true, matroid_isBasis_iff_of_subsingleton]
  exact fun I X hIs hIX ↦ (hIX.symm.trans hIs).subset

theorem matroid_closure_of_subsingleton [Subsingleton A] (s : Set A) :
    (matroid R A).closure s = s := by
  simp_rw [Matroid.closure, matroid_isFlat_of_subsingleton, true_and, matroid_e, inter_univ]
  exact subset_antisymm (sInter_subset_of_mem <| subset_refl s) (subset_sInter fun _ ↦ id)

theorem matroid_spanning_iff_of_subsingleton [Subsingleton A] {s : Set A} :
    (matroid R A).Spanning s ↔ s = univ := by
  simp_rw [Matroid.spanning_iff, matroid_closure_of_subsingleton, matroid_e, subset_univ, and_true]

end AlgebraicIndependent

/-- If `s ⊆ t` are subsets in an `R`-algebra `A` such that `s` is algebraically independent over
`R`, and `A` is algebraic over the `R`-algebra generated by `t`, then there is a transcendence
basis of `A` over `R` between `s` and `t`, provided that `A` is a domain.

This may fail if only `R` is assumed to be a domain but `A` is not, because of failure of
transitivity of algebraicity: there may exist `a : A` such that `S := R[a]` is algebraic over
`R` and `A` is algebraic over `S`, but `A` nonetheless contains a transcendental element over `R`.
The only `R`-algebraically independent subset of `{a}` is `∅`, which is not a transcendence basis.
See the docstring of `IsAlgebraic.restrictScalars_of_isIntegral` for an example. -/
theorem exists_isTranscendenceBasis_between [NoZeroDivisors A] (s t : Set A) (hst : s ⊆ t)
    (hs : AlgebraicIndepOn R id s) [ht : Algebra.IsAlgebraic (adjoin R t) A] :
    ∃ u, s ⊆ u ∧ u ⊆ t ∧ IsTranscendenceBasis R ((↑) : u → A) := by
  have := ht.nontrivial
  have := Subtype.val_injective (p := (· ∈ adjoin R t)).nontrivial
  have := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hs.algebraMap_injective
  rw [← matroid_spanning_iff] at ht
  rw [← matroid_indep_iff] at hs
  have ⟨B, base, hsB, hBt⟩ := hs.exists_isBase_subset_spanning ht hst
  exact ⟨B, hsB, hBt, base⟩

theorem exists_isTranscendenceBasis_subset [NoZeroDivisors A] [FaithfulSMul R A]
    (s : Set A) [Algebra.IsAlgebraic (adjoin R s) A] :
    ∃ t, t ⊆ s ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  have ⟨t, _, ht⟩ := exists_isTranscendenceBasis_between ∅ s (empty_subset _)
    ((algebraicIndependent_empty_iff ..).mpr <| FaithfulSMul.algebraMap_injective R A)
  exact ⟨t, ht⟩

theorem isAlgebraic_iff_exists_isTranscendenceBasis_subset
    [IsDomain A] [FaithfulSMul R A] {s : Set A} :
    Algebra.IsAlgebraic (adjoin R s) A ↔ ∃ t, t ⊆ s ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  simp_rw [← matroid_spanning_iff, ← matroid_isBase_iff, and_comm (a := _ ⊆ _)]
  exact Matroid.spanning_iff_exists_isBase_subset (subset_univ _)

open Cardinal AlgebraicIndependent

namespace IsTranscendenceBasis

variable [Nontrivial R] [NoZeroDivisors A]

theorem lift_cardinalMk_eq_trdeg (hx : IsTranscendenceBasis R x) :
    lift.{w} #ι = lift.{u} (trdeg R A) := by
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hx.1.algebraMap_injective
  rw [← matroid_cRank_eq, ← ((matroid_isBase_iff).mpr hx.to_subtype_range).cardinalMk_eq_cRank,
    lift_mk_eq'.mpr ⟨.ofInjective _ hx.1.injective⟩]

theorem cardinalMk_eq_trdeg {ι : Type w} {x : ι → A} (hx : IsTranscendenceBasis R x) :
    #ι = trdeg R A := by
  rw [← lift_id #ι, lift_cardinalMk_eq_trdeg hx, lift_id]

/-- Any two transcendence bases of a domain `A` have the same cardinality.
May fail if `A` is not a domain; see https://mathoverflow.net/a/144580. -/
@[stacks 030F]
theorem lift_cardinalMk_eq (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis R y) :
    lift.{u'} #ι = lift.{u} #ι' := by
  rw [← lift_inj.{_, w}, lift_lift, lift_lift, ← lift_lift.{w, u'}, hx.lift_cardinalMk_eq_trdeg,
    ← lift_lift.{w, u}, hy.lift_cardinalMk_eq_trdeg, lift_lift, lift_lift]

@[stacks 030F] theorem cardinalMk_eq {ι' : Type u} {y : ι' → A}
    (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis R y) :
    #ι = #ι' := by
  rw [← lift_id #ι, lift_cardinalMk_eq hx hy, lift_id]

end IsTranscendenceBasis

-- TODO: generalize to Nontrivial S
@[simp]
theorem MvPolynomial.trdeg_of_isDomain [IsDomain S] : trdeg S (MvPolynomial ι S) = lift.{v} #ι := by
  have := (IsTranscendenceBasis.mvPolynomial ι S).lift_cardinalMk_eq_trdeg.symm
  rwa [lift_id', ← lift_lift.{u}, lift_id] at this

-- TODO: generalize to Nontrivial R
@[simp]
theorem Polynomial.trdeg_of_isDomain [IsDomain R] : trdeg R (Polynomial R) = 1 := by
  simpa using (IsTranscendenceBasis.polynomial Unit R).lift_cardinalMk_eq_trdeg.symm

-- TODO: generalize to Nontrivial S
theorem trdeg_lt_aleph0 [IsDomain R] [fin : FiniteType R S] : trdeg R S < ℵ₀ :=
  have ⟨n, f, surj⟩ := FiniteType.iff_quotient_mvPolynomial''.mp fin
  lift_lt.mp <| (lift_trdeg_le_of_surjective f surj).trans_lt <| by
    simpa using Cardinal.nat_lt_aleph0 _

namespace Algebra.IsAlgebraic

variable (R x) (s : Set A)

variable [NoZeroDivisors A]

lemma isDomain_of_adjoin_range [Algebra.IsAlgebraic (adjoin R s) A] : IsDomain A :=
  have := Algebra.IsAlgebraic.nontrivial (adjoin R s) A
  (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr
    ⟨‹_›, (Subtype.val_injective (p := (· ∈ adjoin R s))).nontrivial⟩

theorem trdeg_le_cardinalMk [alg : Algebra.IsAlgebraic (adjoin R s) A] : trdeg R A ≤ #s := by
  by_cases h : Injective (algebraMap R A)
  on_goal 2 => simp [trdeg_eq_zero_of_not_injective h]
  have := isDomain_of_adjoin_range R s
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr h
  rw [← matroid_spanning_iff, ← matroid_cRank_eq] at *
  exact alg.cRank_le_cardinalMk

variable [FaithfulSMul R A]

theorem isTranscendenceBasis_of_lift_le_trdeg_of_finite
    [Finite ι] [alg : Algebra.IsAlgebraic (adjoin R (range x)) A]
    (le : lift.{w} #ι ≤ lift.{u} (trdeg R A)) : IsTranscendenceBasis R x := by
  have ⟨_, h⟩ := lift_mk_le'.mp (le.trans <| lift_le.mpr <| trdeg_le_cardinalMk R (range x))
  have := surjective_onto_range.bijective_of_nat_card_le (Nat.card_le_card_of_injective _ h)
  refine .of_subtype_range (fun _ _ ↦ (this.1 <| Subtype.ext ·)) ?_
  have := isDomain_of_adjoin_range R (range x)
  rw [← matroid_spanning_iff, ← matroid_cRank_eq] at *
  exact alg.isBase_of_le_cRank_of_finite (lift_le.mp <| mk_range_le_lift.trans le) (finite_range x)

theorem isTranscendenceBasis_of_le_trdeg_of_finite {ι : Type w} [Finite ι] (x : ι → A)
    [Algebra.IsAlgebraic (adjoin R (range x)) A] (le : #ι ≤ trdeg R A) :
    IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_le_trdeg_of_finite R x (by rwa [lift_id, lift_id])

theorem isTranscendenceBasis_of_lift_le_trdeg [Algebra.IsAlgebraic (adjoin R (range x)) A]
    (fin : trdeg R A < ℵ₀) (le : lift.{w} #ι ≤ lift.{u} (trdeg R A)) :
    IsTranscendenceBasis R x :=
  have := mk_lt_aleph0_iff.mp (lift_lt.mp <| le.trans_lt <| (lift_lt.mpr fin).trans_eq <| by simp)
  isTranscendenceBasis_of_lift_le_trdeg_of_finite R x le

theorem isTranscendenceBasis_of_le_trdeg {ι : Type w} (x : ι → A)
    [Algebra.IsAlgebraic (adjoin R (range x)) A] (fin : trdeg R A < ℵ₀)
    (le : #ι ≤ trdeg R A) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_le_trdeg R x fin (by rwa [lift_id, lift_id])

end Algebra.IsAlgebraic

namespace AlgebraicIndependent

variable [Nontrivial R] [NoZeroDivisors A]

theorem isTranscendenceBasis_of_lift_trdeg_le (hx : AlgebraicIndependent R x)
    (fin : trdeg R A < ℵ₀) (le : lift.{u} (trdeg R A) ≤ lift.{w} #ι) :
    IsTranscendenceBasis R x := by
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hx.algebraMap_injective
  rw [← matroid_cRank_eq, ← Matroid.rankFinite_iff_cRank_lt_aleph0] at fin
  exact .of_subtype_range hx.injective <| matroid_indep_iff.mpr hx.to_subtype_range
    |>.isBase_of_cRank_le <| lift_le.mp <| (matroid_cRank_eq R A ▸ le).trans_eq
      (mk_range_eq_of_injective hx.injective).symm

theorem isTranscendenceBasis_of_trdeg_le {ι : Type w} {x : ι → A} (hx : AlgebraicIndependent R x)
    (fin : trdeg R A < ℵ₀) (le : trdeg R A ≤ #ι) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_trdeg_le hx fin (by rwa [lift_id, lift_id])

theorem isTranscendenceBasis_of_lift_trdeg_le_of_finite [Finite ι] (hx : AlgebraicIndependent R x)
    (le : lift.{u} (trdeg R A) ≤ lift.{w} #ι) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_trdeg_le hx
    (lift_lt.mp <| le.trans_lt <| by simp) le

theorem isTranscendenceBasis_of_trdeg_le_of_finite {ι : Type w} [Finite ι] {x : ι → A}
    (hx : AlgebraicIndependent R x) (le : trdeg R A ≤ #ι) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_trdeg_le_of_finite hx (by rwa [lift_id, lift_id])

end AlgebraicIndependent

variable (R S A)

@[stacks 030H] theorem lift_trdeg_add_eq [Nontrivial R] [NoZeroDivisors A] [FaithfulSMul R S]
    [FaithfulSMul S A] : lift.{w} (trdeg R S) + lift.{v} (trdeg S A) = lift.{v} (trdeg R A) := by
  have ⟨s, hs⟩ := exists_isTranscendenceBasis R S
  have ⟨t, ht⟩ := exists_isTranscendenceBasis S A
  have := (FaithfulSMul.algebraMap_injective S A).noZeroDivisors _ (map_zero _) (map_mul _)
  have := (FaithfulSMul.algebraMap_injective R S).nontrivial
  rw [← hs.cardinalMk_eq_trdeg, ← ht.cardinalMk_eq_trdeg, ← lift_umax.{w}, add_comm,
    ← (hs.sumElim_comp ht).lift_cardinalMk_eq_trdeg, mk_sum, lift_add, lift_lift, lift_lift]

@[stacks 030H] theorem trdeg_add_eq [Nontrivial R] {A : Type v} [CommRing A] [NoZeroDivisors A]
    [Algebra R A] [Algebra S A] [FaithfulSMul R S] [FaithfulSMul S A] [IsScalarTower R S A] :
    trdeg R S + trdeg S A = trdeg R A := by
  rw [← (trdeg R S).lift_id, ← (trdeg S A).lift_id, ← (trdeg R A).lift_id]
  exact lift_trdeg_add_eq R S A
