/-
Copyright (c) 2025 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent, Jarod Alper
-/

import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Embedding Dimension

This file defines the embedding dimension of a commutative noetherian local ring and
proves properties about it.

## Main results

* `IsLocalRing.embDim`: definition of embedding dimension
* `IsLocalRing.embDim_eq_spanFinrank_maximalIdeal`: the embedding dimension is equal
to the minimum number of generators of `m`.
* `IsLocalRing.embDim_Quotient_span_singleton`: if `x ∈ m \ m²` then
`embDim R = embDim R ⧸ x + 1`

-/

local notation3:max "maxl" A => (IsLocalRing.maximalIdeal A)
open IsLocalRing
open Submodule
open Cardinal

/-- The embedding dimension of a local ring `R` with maximal ideal `m` is
the dimension of `m ⧸ m²`. -/
noncomputable def IsLocalRing.embDim (R : Type*) [CommRing R] [IsLocalRing R]
    : ℕ :=
  Module.finrank (ResidueField R) (CotangentSpace R)

lemma Module.Finrank_eq_spanFinrankOfTop
    (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Module.finrank k V = (⊤ : Submodule k V).spanFinrank := by
  have rank_eq_spanRank : Module.rank k V = (⊤ : Submodule k V).spanRank :=
    Submodule.rank_eq_spanRank_of_free
  have spanrank_eq_spanFinrank : (⊤ : Submodule k V).spanRank=(⊤ : Submodule k V).spanFinrank :=
    Submodule.fg_iff_spanRank_eq_spanFinrank.mpr (IsNoetherian.noetherian (⊤ : Submodule k V))
  have finrank_eq_rank : Module.finrank k V = Module.rank k V := Module.finrank_eq_rank k V
  rw [rank_eq_spanRank, spanrank_eq_spanFinrank, Nat.cast_inj] at finrank_eq_rank
  exact finrank_eq_rank

lemma Submodule.finrank_eq_spanFinrank_of_free
    (R : Type*) [Semiring R] [StrongRankCondition R]
    (V : Type*) [AddCommMonoid V] [Module R V] [Module.Free R V] :
    Module.finrank R V = (⊤ : Submodule R V).spanFinrank := by
  rw [Module.finrank, Submodule.rank_eq_spanRank_of_free, spanFinrank]

lemma Submodule.le_spanRank_restrictScalars
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {V : Type*} [AddCommMonoid V] [Module R V] [Module S V] [IsScalarTower R S V]
    (p : Submodule S V) :
    p.spanRank ≤ (p.restrictScalars R).spanRank := by
  refine le_ciInf fun ⟨s, hs⟩ ↦ (ciInf_le' _ ⟨s, ?_⟩).trans le_rfl
  exact le_antisymm (span_le.mpr (subset_span.trans hs.le))
    (hs.ge.trans (span_le_restrictScalars R S s))

lemma Submodule.spanRank_restrictScalars
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {V : Type*} [AddCommMonoid V] [Module R V] [Module S V] [IsScalarTower R S V]
    (p : Submodule S V) (H : Function.Surjective (algebraMap R S)) :
    (p.restrictScalars R).spanRank = p.spanRank := by
  refine p.le_spanRank_restrictScalars.antisymm'
    (le_ciInf fun ⟨s, hs⟩ ↦ (ciInf_le' _ ⟨s, ?_⟩).trans le_rfl)
  rw [← hs, Submodule.restrictScalars_span _ _ H]

lemma Submodule.le_spanFinrank_restrictScalars
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {V : Type*} [AddCommMonoid V] [Module R V] [Module S V] [IsScalarTower R S V]
    (p : Submodule S V) (hp : (p.restrictScalars R).FG) :
    p.spanFinrank ≤ (p.restrictScalars R).spanFinrank :=
  Cardinal.toNat_le_toNat p.le_spanRank_restrictScalars (by simpa)

lemma Submodule.spanFinrank_restrictScalars
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {V : Type*} [AddCommMonoid V] [Module R V] [Module S V] [IsScalarTower R S V]
    (p : Submodule S V) (H : Function.Surjective (algebraMap R S)) :
    (p.restrictScalars R).spanFinrank = p.spanFinrank := by
  rw [spanFinrank, spanFinrank, Submodule.spanRank_restrictScalars p H]

lemma lift_spanRank_map_le.{u, v}
    {R : Type*} {M : Type u} {N : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (σ : M →ₗ[R] N) (p : Submodule R M) :
    Cardinal.lift.{u} (p.map σ).spanRank ≤ Cardinal.lift p.spanRank := by
  obtain ⟨s, hs, rfl⟩ := exists_span_set_card_eq_spanRank p
  rw [Submodule.map_span, ← hs]
  exact (Cardinal.lift_monotone (spanRank_span_le_card _)).trans Cardinal.mk_image_le_lift

lemma lift_spanRank_map.{u, v}
    {R : Type*} {M : Type u} {N : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (σ : M →ₗ[R] N) (hσ : Function.Injective σ) (p : Submodule R M) :
    Cardinal.lift.{u} (p.map σ).spanRank = Cardinal.lift p.spanRank := by
  refine (lift_spanRank_map_le σ p).antisymm ?_
  obtain ⟨s, hs, hsp⟩ := exists_span_set_card_eq_spanRank (p.map σ)
  choose! v hv e using subset_span.trans hsp.le
  have : span R (v '' s) = p := by
    apply Submodule.map_injective_of_injective hσ
    rw [Submodule.map_span, ← hsp, ← Set.image_comp, Set.EqOn.image_eq_self]
    aesop
  rw [← hs, ← this]
  exact (Cardinal.lift_monotone (spanRank_span_le_card _)).trans Cardinal.mk_image_le_lift

lemma spanRank_map.{u}
    {R : Type*} {M N : Type u} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (σ : M →ₗ[R] N) (hσ : Function.Injective σ) (p : Submodule R M) :
    (p.map σ).spanRank = p.spanRank := by
  simpa using lift_spanRank_map σ hσ p

lemma spanFinrank_map_le
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (σ : M →ₗ[R] N) (p : Submodule R M) (hp : p.FG) :
    (map σ p).spanFinrank ≤ p.spanFinrank := by
  simpa using Cardinal.toNat_le_toNat (lift_spanRank_map_le σ p) (by simpa)

lemma spanFinrank_map
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (σ : M →ₗ[R] N)
    (hσ : Function.Injective σ) (p : Submodule R M) :
    (map σ p).spanFinrank = p.spanFinrank := by
  simpa using congr($(lift_spanRank_map σ hσ p).toNat)

lemma spanRank_eq_spanRank_top {R M : Type*} [Semiring R]
    [AddCommGroup M] [Module R M] (N : Submodule R M) :
    N.spanRank = (⊤ : Submodule R N).spanRank := by
  rw [← spanRank_map N.subtype Subtype.val_injective, Submodule.map_top, range_subtype]

lemma spanFinrank_eq_spanFinrank_top {R M : Type*} [Semiring R]
    [AddCommGroup M] [Module R M] (N : Submodule R M) :
    N.spanFinrank = (⊤ : Submodule R N).spanFinrank := by
  rw [spanFinrank, spanRank_eq_spanRank_top, spanFinrank]

open TensorProduct in
noncomputable
def Ideal.cotangentEquivTensorProduct {R : Type*} [CommRing R] (I : Ideal R) :
    I.Cotangent ≃ₗ[R ⧸ I] (R ⧸ I) ⊗[R] I :=
  (LinearEquiv.ofLinear
    (Submodule.liftQ _ (TensorProduct.mk _ _ _ 1) (by
      simp +contextual [Submodule.smul_le, TensorProduct.smul_tmul', Algebra.smul_def,
        Ideal.Quotient.eq_zero_iff_mem.mpr]))
    (TensorProduct.lift (Submodule.liftQ _ (.toSpanSingleton _ _ I.toCotangent) (fun x hx ↦ by
      ext a
      simp only [LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, ← map_smul,
        LinearMap.zero_apply, Ideal.toCotangent_eq_zero, pow_two, SetLike.val_smul, smul_eq_mul]
      exact Ideal.mul_mem_mul hx a.2)))
    (by ext x; show 1 ⊗ₜ (1 • x) = 1 ⊗ₜ[R] x; rw [one_smul]) (by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
      show (1 : R ⧸ I) • I.toCotangent x = I.toCotangent x
      rw [one_smul]) : I.Cotangent ≃ₗ[R] (R ⧸ I) ⊗[R] I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

open TensorProduct in
@[simp]
lemma Ideal.cotangentEquivTensorProduct_symm_tmul {R : Type*} [CommRing R] (I : Ideal R)
    (x : R ⧸ I) (y : I) :
    I.cotangentEquivTensorProduct.symm (x ⊗ₜ y) = x • I.toCotangent y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

lemma Set.ncard_image {α β : Type*} (f : α → β) {s : Set α} (hs : s.Finite) :
    (f '' s).ncard ≤ s.ncard := by
  classical
  lift s to Finset α using hs
  rw [← Finset.coe_image, ncard_coe_Finset, ncard_coe_Finset]
  exact Finset.card_image_le

lemma Set.ncard_range {α β : Type*} (f : α → β) [Finite α] :
    (Set.range f).ncard ≤ Nat.card α := by
  rw [← Set.image_univ, ← Set.ncard_univ]
  exact Set.ncard_image _ Set.finite_univ

/-- the embedding dimension of `R` is equal to the minimum number of generators of `m`. -/
theorem IsLocalRing.embDim_eq_spanFinrank_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsLocalRing.embDim R = (maxl R).spanFinrank := by
  rw [embDim, spanFinrank_eq_spanFinrank_top (maximalIdeal R)]
  apply le_antisymm
  · rw [Submodule.finrank_eq_spanFinrank_of_free]
    refine (Submodule.le_spanFinrank_restrictScalars (R := R) _
      (Module.finite_def.mp inferInstance)).trans ?_
    refine le_trans ?_ (spanFinrank_map_le (Ideal.toCotangent _) _ ?_)
    · simp [LinearMap.range_eq_top.mpr (Ideal.toCotangent_surjective _)]
    · exact Module.finite_def.mp inferInstance
  · let I := Module.Free.ChooseBasisIndex (ResidueField R) (CotangentSpace R)
    let b : Basis I (ResidueField R) (CotangentSpace R) := Module.Free.chooseBasis _ _
    choose x hx using fun i ↦ Ideal.toCotangent_surjective _ (b i)
    have := IsLocalRing.span_eq_top_of_tmul_eq_basis x
      (b.map (Ideal.cotangentEquivTensorProduct (maximalIdeal R)))
      (by simp [← LinearEquiv.symm_apply_eq, ResidueField, hx, CotangentSpace])
    rw [← this]
    refine (spanFinrank_span_le_ncard_of_finite (Set.finite_range x)).trans ?_
    rw [Module.finrank_eq_card_basis b, ← Nat.card_eq_fintype_card]
    exact Set.ncard_range _

theorem Ideal.toCotangent_out {R : Type*} [CommRing R] (I : Ideal R) (x : I.Cotangent) :
    I.toCotangent (Quotient.out x) = x := by
  rw[Ideal.toCotangent_apply I, ← Submodule.Quotient.mk''_eq_mk, Quotient.out_eq']

theorem IsLocalRing.ContangentSpace_extend_singleton_basis
    {R : Type*} {x : R} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hx1 : x ∈ (maxl R)) (hx2 : x ∉ ((maxl R)^2)) :
    ∃ s : Set R, span R s = (maxl R) ∧ #s = (maxl R).spanRank ∧ x ∈ s := by
  let x' : Subtype ((maxl R) : Set R) := ⟨x, hx1⟩
  have : (maxl R).toCotangent x' ≠ 0 := by
    by_contra hc
    exact hx2 ((@Ideal.mem_toCotangent_ker R _ (maxl R) x').mp hc)
  let s' : Set ((maxl R).Cotangent) := {(maxl R).toCotangent x'}
  have t : (maxl R).toCotangent x' ∈ s' := rfl
  have li : LinearIndepOn (ResidueField R) id s' := LinearIndepOn.id_singleton (ResidueField R) this
  let B := Basis.extend li
  let S := Set.range (DFunLike.coe B)
  have Srw := Basis.range_extend li
  change S = li.extend (Set.subset_univ s') at Srw
  have s'sub := Basis.subset_extend li
  rw[← Srw] at s'sub
  have hxS : (maxl R).toCotangent x' ∈ S := s'sub t
  have Sspan : span (ResidueField R) S = ⊤ := Basis.span_eq B
  have Scard := Basis.mk_eq_rank'' B
  have a := IsLocalRing.embDim_eq_spanFinrank_maximalIdeal R
  unfold embDim at a
  have b : Module.rank (ResidueField R) (maxl R).Cotangent =
    Module.finrank (ResidueField R) (maxl R).Cotangent :=
    Eq.symm (Module.finrank_eq_rank (ResidueField R) (maxl R).Cotangent)
  rw[b, a, ← Srw] at Scard
  have c : spanRank (maxl R) = spanFinrank (maxl R) := by
    apply Submodule.fg_iff_spanRank_eq_spanFinrank.mpr
    exact IsNoetherian.noetherian maxl R
  rw[← c] at Scard
  clear a b c Srw t s'sub
  let S' := S \ {(maxl R).toCotangent x'}
  have a : S = S' ∪ {(maxl R).toCotangent x'} := by simp_all only [ne_eq, Basis.coe_extend,
  Subtype.range_coe_subtype, Set.setOf_mem_eq, mk_fintype, Set.union_singleton,
  Set.insert_diff_singleton, Set.insert_eq_of_mem, x', S, s', B, S']
  have S'card : #S = #S' + 1 := by
    have b := mk_singleton ((maxl R).toCotangent x')
    rw[← b, a]
    refine Cardinal.mk_union_of_disjoint ?_
    exact Set.disjoint_sdiff_left
  let s'' : Set (maxl R) := Quotient.out '' S'
  let s : Set (maxl R) := s'' ∪ {x'}
  have a : #s'' = #S' := Cardinal.mk_image_eq Quotient.out_injective
  have scard : #s = #s'' + 1 := by
    have b := mk_singleton x'
    rw[← b]
    refine Cardinal.mk_union_of_disjoint ?_
    have d : x' ∉ s'' := by
      by_contra hc
      have b : (maxl R).toCotangent '' s'' = S' := by
        have l : s'' = Quotient.out '' S' := rfl
        rw[l]
        refine Function.LeftInverse.image_image ?_ S'
        exact Ideal.toCotangent_out (maxl R)
      have a : ((maxl R).toCotangent x') ∈ (maxl R).toCotangent '' s'' :=
        Set.mem_image_of_mem (⇑(maxl R).toCotangent) hc
      rw[b] at a
      have c : ((maxl R).toCotangent x') ∉ S \ {(maxl R).toCotangent x'} :=
        Set.notMem_diff_of_mem rfl
      exact c a
    exact Set.disjoint_singleton_right.mpr d
  rw[a, ← S'card, Scard] at scard
  clear a
  have sim : (maxl R).toCotangent '' s = S := by
    have a := Set.image_union (maxl R).toCotangent s'' {x'}
    have b : (maxl R).toCotangent '' s'' = S' := by
      have l : s'' = Quotient.out '' S' := rfl
      rw[l]
      refine Function.LeftInverse.image_image ?_ S'
      exact Ideal.toCotangent_out (maxl R)
    rw[b] at a
    have c : S' ∪ ⇑(maxl R).toCotangent '' {x'} = S := by simp_all only [ne_eq, Basis.coe_extend,
      Subtype.range_coe_subtype, Set.setOf_mem_eq, mk_fintype, Set.union_singleton,
      Set.insert_diff_singleton, Set.insert_eq_of_mem, Set.image_singleton,
      s', S', x', S, B, s, s'']
    rw[c] at a
    exact a
  have sspan : span R s = ⊤ := by
    apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
    rw[sim]
    exact Sspan
  use (maxl R).subtype '' s
  constructor
  · have a := Submodule.map_span (maxl R).subtype s
    rw[sspan, map_subtype_top maxl R] at a
    rw[← a]
  constructor
  · rw[@Cardinal.mk_image_eq (maxl R) R (maxl R).subtype s (injective_subtype maxl R)]
    exact scard
  simp_all only [ne_eq, Basis.coe_extend, Subtype.range_coe_subtype, Set.setOf_mem_eq, mk_fintype,
    Set.union_singleton, Set.insert_diff_singleton, Set.insert_eq_of_mem, subtype_apply,
    Set.mem_image, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff, exists_eq_or_imp,
    exists_exists_and_eq_and, true_or, S, B, s', S', s'', x', s]

theorem IsLocalRing.embDim_quot_singleton
{R : Type*} {x : R} [CommRing R] [IsLocalRing R] [Nontrivial (R ⧸ Ideal.span {x})] :
    (maxl R).spanRank ≤ (maxl (R ⧸ Ideal.span {x})).spanRank + 1 := by
  obtain ⟨s, hs1, hs2⟩ := Submodule.exists_span_set_card_eq_spanRank (maxl (R ⧸ Ideal.span {x}))
  let s' : Set R := Quotient.out '' s
  have ims' : Ideal.Quotient.mk (Ideal.span {x}) '' s' = s := by
    simp_all only [Ideal.submodule_span_eq, s']
    ext x_1 : 1
    simp_all only [Set.mem_image, exists_exists_and_eq_and, Ideal.Quotient.mk_out, exists_eq_right]
  have mapsp := Ideal.map_span (Ideal.Quotient.mk (Ideal.span {x})) s'
  rw[ims'] at mapsp
  have : Ideal.span s = Submodule.span (R ⧸ Ideal.span {x}) s := rfl
  rw[← this] at hs2
  rw[hs2] at mapsp
  have comapmap := Ideal.comap_map_of_surjective'
    (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective (Ideal.span s')
  rw[mapsp, (IsLocalRing.Quotient_comap_maximalIdeal (Ideal.span {x})), Ideal.mk_ker,
    ← Ideal.span_union] at comapmap
  have a : #(s' ∪ {x} : Set R) ≤ #s' + 1 := by
    have a := Cardinal.mk_union_le s' {x}
    have : #({x} : Set R) = 1 := mk_singleton x
    rw[this] at a
    exact a
  have ss' : #s' ≤ #s := mk_image_le
  have srle := @Submodule.spanRank_span_le_card R R _ _ _ (s' ∪ {x})
  have : Ideal.span (s' ∪ {x}) = span R (s' ∪ {x}) := rfl
  rw[this] at comapmap
  rw[← comapmap] at srle
  rw[← hs1]
  have b := Preorder.le_trans (spanRank maxl R) #(s' ∪ {x} : Set R) (#s' + 1) srle a
  have : #s' + 1 ≤ #s + 1 :=
    @add_le_add_right Cardinal _ _ _ #s' #s ss' 1
  exact Preorder.le_trans (spanRank maxl R) (#s' + 1) (#s + 1) b this

lemma IsLocalRing.embDim_quot_singleton'
{R : Type*} {x : R} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
[Nontrivial (R ⧸ Ideal.span {x})] (hx1 : x ∈ (maxl R)) (hx2 : x ∉ ((maxl R)^2)) :
    (maxl (R ⧸ Ideal.span {x})).spanRank + 1 ≤ (maxl R).spanRank := by
  obtain ⟨s, hs⟩ := IsLocalRing.ContangentSpace_extend_singleton_basis hx1 hx2
  let s' : Set R := s \ {x}
  have scup : s = s' ∪ {x} := by
    simp_all only [mem_maximalIdeal, mem_nonunits_iff, Ideal.submodule_span_eq,
    Set.union_singleton, Set.insert_diff_singleton, Set.insert_eq_of_mem, s']
  have ss' : #s = #s' + 1 := by
    rw[scup]
    have : #({x} : Set R) = 1 := mk_singleton x
    rw[← this]
    refine Cardinal.mk_union_of_disjoint ?_
    exact Set.disjoint_sdiff_left
  have mapeq : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span s) = Ideal.map
    (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span s') := by
    apply (Ideal.map_eq_iff_sup_ker_eq_of_surjective (Ideal.Quotient.mk (Ideal.span {x}))
      Ideal.Quotient.mk_surjective).mpr
    rw[Ideal.mk_ker, ← Ideal.span_union, ← Ideal.span_union]
    have : s ∪ {x} = s' ∪ {x} := by
      rw[scup]
      simp only [Set.union_singleton, Set.mem_insert_iff, true_or, Set.insert_eq_of_mem, s']
    rw[this]
  have mapsp := Ideal.map_span (Ideal.Quotient.mk (Ideal.span {x})) s'
  have : Ideal.span s = span R s := rfl
  rw[this, hs.1, IsLocalRing.Quotient_map_maximalIdeal (Ideal.span {x}), mapsp] at mapeq
  clear mapsp
  let s'' : Set (R ⧸ Ideal.span {x}) := (Ideal.Quotient.mk (Ideal.span {x})) '' s'
  have ds'' : (Ideal.Quotient.mk (Ideal.span {x})) '' s' = s'' := rfl
  have cds'' : #s'' ≤ #s' := mk_image_le
  have a := @Submodule.spanRank_span_le_card (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) _ _ _ s''
  rw[ds''] at mapeq
  have : span (R ⧸ Ideal.span {x}) s'' = Ideal.span s'' := rfl
  rw[this, ← mapeq] at a
  have := Preorder.le_trans (spanRank maxl R ⧸ Ideal.span {x}) #s'' #s' a cds''
  have := @add_le_add_right Cardinal _ _ _ (spanRank maxl R ⧸ Ideal.span {x}) #s' this 1
  rw[← ss'] at this
  rw[← hs.2.1]
  exact this

lemma IsNoetherianRing.Ideal_spanRank_eq_spanFinrank
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    I.spanRank = I.spanFinrank :=
  Submodule.fg_iff_spanRank_eq_spanFinrank.mpr (IsNoetherian.noetherian I)

/-- if `x ∈ m \ m²` then `embDim R = embDim R ⧸ x + 1` -/
theorem IsLocalRing.embDim_Quotient_span_singleton.{u}
{R : Type u} {x : R} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
[Nontrivial (R ⧸ Ideal.span {x})] (hx1 : x ∈ (maxl R)) (hx2 : x ∉ ((maxl R)^2)) :
    (IsLocalRing.embDim R) = IsLocalRing.embDim (R ⧸ Ideal.span {x}) + 1 := by

  rw[IsLocalRing.embDim_eq_spanFinrank_maximalIdeal, IsLocalRing.embDim_eq_spanFinrank_maximalIdeal]
  have sreq : (maxl R).spanRank = (maxl (R ⧸ Ideal.span {x})).spanRank + 1 :=
    le_antisymm_iff.mpr
      ⟨IsLocalRing.embDim_quot_singleton , IsLocalRing.embDim_quot_singleton' hx1 hx2⟩

  rw[IsNoetherianRing.Ideal_spanRank_eq_spanFinrank (maxl R),
  IsNoetherianRing.Ideal_spanRank_eq_spanFinrank (maxl R ⧸ Ideal.span {x})] at sreq
  apply @Nat.cast_injective Cardinal.{u} _ _
  simp only [Nat.cast_add, Nat.cast_one]
  exact sreq
