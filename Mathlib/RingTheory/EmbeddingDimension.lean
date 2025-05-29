/-
Copyright (c) 2025 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent, Jarod Alper
-/
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Embedding Dimension

This file defines the embedding dimension of a commutative noetherian local ring and
proves properties about it.

## Main results

* `IsLocalRing.EmbDim`: definition of embedding dimension
* `IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal`: the embedding dimension is equal
to the minimum number of generators of `m`.
* `IsLocalRing.Embdim_Quotient_span_singleton`: if `x ∈ m \ m²` then
`EmbDim R = EmbDim R ⧸ x + 1`

-/

local notation3:max "maxl" A => (IsLocalRing.maximalIdeal A)
open IsLocalRing
open Submodule
open Cardinal

/-- The embedding dimension of a local ring `R` with maximal ideal `m` is
the dimension of `m ⧸ m²`. -/
noncomputable def IsLocalRing.EmbDim (R : Type*) [CommRing R] [IsLocalRing R]
    : ℕ :=
  Module.finrank (ResidueField R) (CotangentSpace R)

instance {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} [Nontrivial (R ⧸ I)] :
    IsLocalRing (R ⧸ I) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

theorem IsLocalRing.Quotient_comap_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)] :
    Ideal.comap (Ideal.Quotient.mk I) (maxl (R ⧸ I)) = (maxl R) := by
  have : Ideal.IsMaximal (Ideal.comap (Ideal.Quotient.mk I) (maxl (R ⧸ I))) :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact IsLocalRing.eq_maximalIdeal this

theorem IsLocalRing.Quotient_map_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)] :
    Ideal.map (Ideal.Quotient.mk I) (maxl R) = (maxl (R ⧸ I)) := by
  have := Ideal.map_comap_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (maxl (R ⧸ I))
  rw[IsLocalRing.Quotient_comap_maximalIdeal] at this
  exact this

lemma Submodule.spanRank_injective_map_le.{u} {R : Type*} [CommRing R] {M : Type u} {N : Type u}
[AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (σ : M →ₗ[R] N) (p : Submodule R M)
(hσ : Function.Injective σ) :
    (map σ p).spanRank ≤ p.spanRank := by
  obtain ⟨s, hs1, hs2⟩ := Submodule.exists_span_set_card_eq_spanRank p
  let s' : Set N := σ '' s
  have : #s = #s' := Eq.symm (mk_image_eq hσ)
  have a := Submodule.map_span σ s
  rw[hs2] at a
  rw[← hs1]
  have b := @Submodule.spanRank_span_le_card R N _ _ _ s'
  rw[← a] at b
  rw[this]
  exact b

lemma Submodule.spanRank_injective_map_le'.{u} {R : Type*} [CommRing R] {M : Type u} {N : Type u}
[AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (σ : M →ₗ[R] N) (p : Submodule R M)
(hσ : Function.Injective σ) :
    p.spanRank ≤ (map σ p).spanRank := by
  obtain ⟨s, hs1, hs2⟩ := Submodule.exists_span_set_card_eq_spanRank (map σ p)
  let s' : Set M := σ⁻¹' s
  have hss' : σ '' s' = s := by
    ext x
    constructor
    · rintro ⟨a, ⟨ha1, ha2⟩ ⟩
      rw [← ha2]
      exact ha1
    · intro hx
      have a : x ∈ span R s := mem_span.mpr fun p a ↦ a hx
      rw[hs2] at a
      obtain ⟨y, hy1, hy2⟩ := Submodule.mem_map.mp a
      have : y ∈ s' := by
        refine Set.mem_preimage.mpr ?_
        rw[hy2]
        exact hx
      use y
  have s's : #s' = #s := by
    rw[← hss']
    exact Eq.symm (mk_image_eq hσ)
  have b := @Submodule.spanRank_span_le_card R M _ _ _ s'
  have a := Submodule.map_span σ s'
  rw[hss', hs2] at a
  rw[Submodule.map_injective_of_injective hσ a] at b
  rw[s's, hs1] at b
  exact b

theorem Submodule.spanRank_injective_map.{u} {R : Type*} [CommRing R] {M : Type u} {N : Type u}
[AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (σ : M →ₗ[R] N) (p : Submodule R M)
(hσ : Function.Injective σ) :
    p.spanRank = (map σ p).spanRank :=
  le_antisymm_iff.mpr
    ⟨Submodule.spanRank_injective_map_le' σ p hσ, Submodule.spanRank_injective_map_le σ p hσ⟩

lemma Submodule.spanRank_eq_spanRank_Top {R : Type*} [CommRing R] {M : Type*}
[AddCommGroup M] [Module R M] (N : Submodule R M) :
    Submodule.spanRank N = (⊤ : Submodule R N).spanRank := by
  have h1 := Submodule.map_subtype_top N
  have h2 := Submodule.spanRank_injective_map N.subtype
    (⊤ : Submodule R N) (Submodule.injective_subtype N)
  rw[h2]
  rw[h1]

lemma Submodule.SpanFinRankOfSubmodule_eq_spanFinrankOfTop
    (R : Type*) [CommRing R] [IsNoetherianRing R] (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M) :
    Submodule.spanFinrank N = (⊤ : Submodule R N).spanFinrank := by
  have a : N.FG := IsNoetherian.noetherian N
  have b : (⊤ : Submodule R N).FG := IsNoetherian.noetherian ⊤
  have : @Nat.cast Cardinal.{u_2} instNatCast N.spanFinrank =
      @Nat.cast Cardinal.{u_2} instNatCast (⊤ : Submodule R N).spanFinrank := by
    rw[← Submodule.fg_iff_spanRank_eq_spanFinrank.mpr a]
    rw[← Submodule.fg_iff_spanRank_eq_spanFinrank.mpr b]
    exact spanRank_eq_spanRank_Top N
  exact Nat.cast_injective this

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

/-- the embedding dimension of `R` is equal to the minimum number of generators of `m`. -/
theorem IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsLocalRing.EmbDim R = (maxl R).spanFinrank := by
  rw [Nat.eq_iff_le_and_ge]
  constructor
  · have h1 : ∃ s : Set (maxl R),
        s.encard = ↑(Submodule.spanFinrank maxl R) ∧ Submodule.span R s = ⊤ := by
      have : (⊤ : Submodule R (maxl R)).FG := Module.Finite.fg_top
      have := Submodule.FG.exists_span_set_encard_eq_spanFinrank this
      rw[SpanFinRankOfSubmodule_eq_spanFinrankOfTop]
      exact this
    obtain ⟨m_gens, m_gens_card, hm_gens_span⟩ := h1
    have m_gens_finite : m_gens.Finite := Set.finite_of_encard_eq_coe m_gens_card
    have m_gens_card2 : m_gens.ncard = (maxl R).spanFinrank := by
      rw [← (Set.Finite.cast_ncard_eq m_gens_finite)] at m_gens_card
      exact Eq.symm ((fun {a b} ↦ ENat.coe_inj.mp) (id (Eq.symm m_gens_card)))
    rw [← m_gens_card2]
    rw [EmbDim]
    let im_m_gens := ⇑(maxl R).toCotangent '' m_gens
    let subspace := Submodule.span (ResidueField R) im_m_gens
    have hm_gens_cot_span : subspace = ⊤ :=
      IsLocalRing.CotangentSpace.span_image_eq_top_iff.mpr hm_gens_span
    have h1 : im_m_gens.ncard ≤ m_gens.ncard := by
      exact Set.ncard_image_le m_gens_finite
    have h2 : im_m_gens.Finite := Set.Finite.image (⇑(maxl R).toCotangent) m_gens_finite
    have h3 : subspace.spanFinrank ≤ im_m_gens.ncard :=
      Submodule.spanFinrank_span_le_ncard_of_finite h2
    have h4 : subspace.spanFinrank ≤ m_gens.ncard := Nat.le_trans h3 h1
    clear h1 h3
    have h5 : subspace.spanRank  = Module.rank (ResidueField R) (CotangentSpace R) := by
      rw [hm_gens_cot_span]
      have : Module.Free (ResidueField R) (CotangentSpace R) :=
        Module.Free.of_divisionRing (ResidueField R) (CotangentSpace R)
      exact Eq.symm Submodule.rank_eq_spanRank_of_free
    rw [← Module.finrank_eq_rank (ResidueField R) (CotangentSpace R)] at h5
    have subspace_fg : subspace.FG := by
      exact IsNoetherian.noetherian subspace
    rw [← @Submodule.fg_iff_spanRank_eq_spanFinrank (ResidueField R)
      (CotangentSpace R) _ _ _ subspace] at subspace_fg
    rw [subspace_fg] at h5
    have h6 : subspace.spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R) :=
      Nat.cast_inj.mp h5
    rw [← h6]
    exact h4
  · unfold EmbDim
    let res := ResidueField R
    let cot := CotangentSpace R
    have cot_fg : Module.Finite res cot :=
      instFiniteDimensionalResidueFieldCotangentSpaceOfIsNoetherianRing R
    have cot_fg' : (⊤ : Submodule res cot).FG :=
      IsNoetherian.noetherian (⊤ : Submodule res cot)
    obtain ⟨s, s_card, s_span⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank cot_fg'
    have s_finite : s.Finite := Set.finite_of_encard_eq_coe s_card
    let p := ⇑(maxl R).toCotangent
    have p_surj : Function.Surjective p := Ideal.toCotangent_surjective maxl R
    let p_has_right_inv := p_surj.hasRightInverse
    obtain ⟨p_inv, hp_inv⟩ := p_has_right_inv
    clear p_surj
    change cot → ↥maxl R at p_inv
    let sinv := p_inv '' s
    have im_of_sinv_eq_s : (p '' sinv) = s := Function.LeftInverse.image_image hp_inv s
    have nakayama : Submodule.span (ResidueField R) (⇑(maxl R).toCotangent '' sinv) = ⊤
      ↔ Submodule.span R sinv = ⊤ := IsLocalRing.CotangentSpace.span_image_eq_top_iff
    rw [im_of_sinv_eq_s] at nakayama
    have inequality2 : sinv.ncard ≤ s.ncard := Set.ncard_image_le s_finite
    rw [nakayama] at s_span
    have sinv_finite : sinv.Finite := Set.Finite.image p_inv s_finite
    have inequality1 : (Submodule.spanFinrank maxl R) ≤ sinv.ncard := by
      have h1 := (@Submodule.spanFinrank_span_le_ncard_of_finite R (maxl R) _ _ _ sinv) sinv_finite
      have h2 : (Submodule.span R sinv).spanFinrank = (Submodule.spanFinrank maxl R) := by
        rw [s_span, ← SpanFinRankOfSubmodule_eq_spanFinrankOfTop]
      linarith
    have equality3 : s.ncard = Module.finrank res cot := by
      rw [Module.Finrank_eq_spanFinrankOfTop]
      rw [← Set.Finite.cast_ncard_eq s_finite] at s_card
      exact Eq.symm ((fun {a b} ↦ ENat.coe_inj.mp) (id (Eq.symm s_card)))
    linarith

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
  have a := IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal R
  unfold EmbDim at a
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

theorem IsLocalRing.EmbDim_quot_singleton
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

lemma IsLocalRing.EmbDim_quot_singleton'
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

/-- if `x ∈ m \ m²` then `EmbDim R = EmbDim R ⧸ x + 1` -/
theorem IsLocalRing.Embdim_Quotient_span_singleton.{u}
{R : Type u} {x : R} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
[Nontrivial (R ⧸ Ideal.span {x})] (hx1 : x ∈ (maxl R)) (hx2 : x ∉ ((maxl R)^2)) :
    (IsLocalRing.EmbDim R) = IsLocalRing.EmbDim (R ⧸ Ideal.span {x}) + 1 := by

  rw[IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal, IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal]
  have sreq : (maxl R).spanRank = (maxl (R ⧸ Ideal.span {x})).spanRank + 1 :=
    le_antisymm_iff.mpr
      ⟨IsLocalRing.EmbDim_quot_singleton , IsLocalRing.EmbDim_quot_singleton' hx1 hx2⟩

  rw[IsNoetherianRing.Ideal_spanRank_eq_spanFinrank (maxl R),
  IsNoetherianRing.Ideal_spanRank_eq_spanFinrank (maxl R ⧸ Ideal.span {x})] at sreq
  apply @Nat.cast_injective Cardinal.{u} _ _
  simp only [Nat.cast_add, Nat.cast_one]
  exact sreq
