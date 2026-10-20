/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen,
Kim Morrison, Chris Hughes, Anne Baanen, Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Dimension of vector spaces

In this file we provide results about `Module.rank` and `Module.finrank` of vector spaces
over division rings.

## Main statements

For vector spaces (i.e. modules over a division ring), we have

* `rank_quotient_add_rank_of_divisionRing`: if `V₁` is a submodule of `V`, then
  `Module.rank (V/V₁) + Module.rank V₁ = Module.rank V`.
* `DivisionRing.hasRankNullity`: The rank-nullity theorem for division rings.
* `Submodule.rank_span_le_rank`: The `K`-rank of the `K`-span of an `R`-submodule `M` of `V`
  is at most the `R`-rank of `M`.

See also `Mathlib/LinearAlgebra/Dimension/ErdosKaplansky.lean` for the Erdős-Kaplansky theorem.

-/

public section

noncomputable section

universe u₀ u v

variable {K : Type u} {V V₁ V₂ V₃ : Type v}

open Cardinal Submodule Function Set Module

section Module

section DivisionRing

variable [DivisionRing K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup V₁] [Module K V₁]

/-- If a vector space has a finite dimension, the index set of `Basis.ofVectorSpace` is finite. -/
theorem Module.Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0 (h : Module.rank K V < ℵ₀) :
    (Basis.ofVectorSpaceIndex K V).Finite :=
  (Basis.ofVectorSpace K V).setFinite_index_of_rank_lt_aleph0 h

/-- Also see `rank_quotient_add_rank`. -/
theorem rank_quotient_add_rank_of_divisionRing (p : Submodule K V) :
    Module.rank K (V ⧸ p) + Module.rank K p = Module.rank K V := by
  let ⟨f⟩ := quotient_prod_linearEquiv p
  exact rank_prod'.symm.trans f.rank_eq

instance DivisionRing.hasRankNullity : HasRankNullity.{u₀} K where
  rank_quotient_add_rank := rank_quotient_add_rank_of_divisionRing
  exists_set_linearIndependent V _ _ := by
    let b := Module.Free.chooseBasis K V
    refine ⟨range b, ?_, b.linearIndependent.linearIndepOn_id⟩
    rw [← lift_injective.eq_iff, mk_range_eq_of_injective b.injective,
      Module.Free.rank_eq_card_chooseBasisIndex]

section

variable [AddCommGroup V₂] [Module K V₂]
variable [AddCommGroup V₃] [Module K V₃]

open LinearMap

/-- This is mostly an auxiliary lemma for `Submodule.rank_sup_add_rank_inf_eq`. -/
theorem rank_add_rank_split (db : V₂ →ₗ[K] V) (eb : V₃ →ₗ[K] V) (cd : V₁ →ₗ[K] V₂)
    (ce : V₁ →ₗ[K] V₃) (hde : ⊤ ≤ LinearMap.range db ⊔ LinearMap.range eb) (hgd : ker cd = ⊥)
    (eq : db.comp cd = eb.comp ce) (eq₂ : ∀ d e, db d = eb e → ∃ c, cd c = d ∧ ce c = e) :
    Module.rank K V + Module.rank K V₁ = Module.rank K V₂ + Module.rank K V₃ := by
  have hf : Surjective (coprod db eb) := by
    rwa [← range_eq_top, range_coprod, eq_top_iff]
  conv =>
    rhs
    rw [← rank_prod', rank_eq_of_surjective hf]
  congr 1
  apply LinearEquiv.rank_eq
  let L : V₁ →ₗ[K] ker (coprod db eb) :=
    LinearMap.codRestrict _ (prod cd (-ce)) <| by
      simpa [add_eq_zero_iff_eq_neg] using LinearMap.ext_iff.1 eq
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · rw [← ker_eq_bot, ker_codRestrict, ker_prod, hgd, bot_inf_eq]
  · rw [← range_eq_top, eq_top_iff, LinearMap.range_codRestrict, ← map_le_iff_le_comap,
      Submodule.map_top, range_subtype]
    rintro ⟨d, e⟩
    have h := eq₂ d (-e)
    simp only [add_eq_zero_iff_eq_neg, LinearMap.prod_apply, mem_ker,
      Prod.mk_inj, coprod_apply, map_neg, neg_apply, LinearMap.mem_range,
      Function.prod_apply] at h ⊢
    grind

end

namespace Submodule

variable {R : Type*} [CommRing R] [Nontrivial R]
variable [SMulWithZero R K] [FaithfulSMul R K] [IsScalarTower R K K]
variable [Module R V] [IsScalarTower R K V]
variable (M : Submodule R V)

/-- The `K`-rank of the `K`-span of an `R`-submodule `M` of `V` is at most the `R`-rank of `M`. -/
theorem rank_span_le_rank : Module.rank K (span K (M : Set V)) ≤ Module.rank R M := by
  obtain ⟨b, hbM, hbspan, hbli⟩ := exists_linearIndependent K (M : Set V)
  rw [← hbspan, rank_span_set hbli]
  exact LinearIndependent.cardinal_le_rank (v := Set.inclusion hbM)
    (.of_comp M.subtype (hbli.restrict_scalars' R))

/-- The `K`-rank of the `K`-span of a set `s` in `V` is at most the `R`-rank of the `R`-span
of `s`. -/
theorem rank_span_le_rank_span (s : Set V) :
    Module.rank K (span K s) ≤ Module.rank R (span R s) :=
  span_span_of_tower R K s ▸ rank_span_le_rank (span R s)

/-- The `K`-rank of the `K`-span of a finitely generated `R`-submodule `M` of `V` is at most
the `R`-rank of `M`.

This is the `Module.finrank` version of `Submodule.rank_span_le_rank`; see also
`Submodule.finrank_span_eq_finrank` for an equality in a different setting. -/
theorem finrank_span_le_finrank (h : M.FG) : finrank K (span K (M : Set V)) ≤ finrank R M := by
  apply finrank_le_of_rank_le
  have : Module.Finite R M := Module.Finite.of_fg h
  rw [finrank_eq_rank]
  exact rank_span_le_rank M

/-- The `K`-rank of the `K`-span of a finite set `s` in `V` is at most the `R`-rank of the
`R`-span of `s`.

This is the `Module.finrank` version of `Submodule.rank_span_le_rank_span`; see also
`Submodule.finrank_span_eq_finrank_span` for an equality in a different setting. -/
theorem finrank_span_le_finrank_span {s : Set V} (hs : s.Finite) :
    finrank K (span K s) ≤ finrank R (span R s) :=
  span_span_of_tower R K s ▸ finrank_span_le_finrank _ (Submodule.fg_span hs)

end Submodule

section Quotient

variable {K V : Type* } [DivisionRing K] [AddCommGroup V] [Module K V]

lemma Submodule.elem_of_quot_rank_pos (p : Submodule K V) (h : 0 < Module.rank K (V ⧸ p)) :
    ∃ x : V, x ∉ p := by
  obtain ⟨y,hy⟩ := rank_pos_iff_exists_ne_zero.mp h
  obtain ⟨x,hx⟩ := (Submodule.Quotient.mk_surjective p) y
  use x
  apply (Submodule.Quotient.mk_eq_zero p (x:=x)).not.mp
  simpa [hx] using hy

/-If the quotient of `V` by a submodule `p` has rank 1 then evey submodule containing `p` is `⊤`-/
theorem Submodule.isCoatom_of_quot_rank_eq_one
      (p : Submodule K V) (h : Module.rank K (V ⧸ p) = 1) :
      IsCoatom p := by
    obtain ⟨x,xnotinp⟩:= Submodule.elem_of_quot_rank_pos p
      (Cardinal.one_le_iff_pos.mp (Std.le_of_eq (id (Eq.symm h))))
    constructor
    · exact Ne.symm (ne_of_mem_of_not_mem' trivial (a := x) xnotinp)
    · intro q hq
      let f := Submodule.mapQ p q LinearMap.id (Std.le_of_lt hq)
      have fsur : Function.Surjective f := by
        intro u
        obtain ⟨d,hd⟩ := Submodule.Quotient.mk_surjective q u
        simp only [← hd, f]
        use (Quotient.mk (p:=p) d)
        simp [mapQ_apply p q LinearMap.id]
      have :=  LinearMap.rank_le_of_surjective f fsur
      rw [h] at this
      have oneorzero := Cardinal.le_one_iff.mp this
      have rankne1 : Module.rank K (V ⧸ q) = 0 := by
        apply Or.resolve_right oneorzero
        intro h1
        have := LinearMap.rank_range_add_rank_ker f
        have finr : Module.rank K ↥f.range = 1 := by
          rw [LinearMap.range_eq_top_of_surjective f fsur, rank_top]
          exact h1
        rw [h,finr] at this
        have : Module.rank K ↥f.ker + 1 = 0 + 1 := by
          simpa [add_comm]
        simp only [Cardinal.add_one_inj] at this
        have bintop : q ≤ p := by
          intro _ hz
          apply (Submodule.Quotient.mk_eq_zero p).mp
          apply_fun f
          · rw [mapQ_apply p q LinearMap.id]
            simpa only [LinearMap.id_coe, id_eq, map_zero, Quotient.mk_eq_zero] using hz
          · exact LinearMap.ker_eq_bot.mp (subsingleton_iff_eq_bot.mp (rank_zero_iff.mp this))
        exact (LT.lt.not_ge hq) bintop
      apply (Submodule.Quotient.subsingleton_iff).mp
      have := Module.Free.of_divisionRing K (V ⧸ q)
      exact Module.subsingleton_of_rank_zero rankne1

/-If the quotient of `V` by a submodule `p` has rank 1 then there exists
    a non-zero element in `V` such that `p` is in direct sum with `K • x`-/
theorem Submodule.compl_span_singleton_of_quot_rank_one
    (p : Submodule K V) (h : Module.rank K (V ⧸ p) = 1) :
    ∃ x : V, x ≠ 0 ∧ IsCompl p (Submodule.span K {x}) := by
  obtain ⟨x,xnotinp⟩:= Submodule.elem_of_quot_rank_pos p
    (Cardinal.one_le_iff_pos.mp (Std.le_of_eq (id (Eq.symm h))))
  use x
  constructor
  · exact fun hx0 => xnotinp (hx0 ▸ Submodule.zero_mem p)
  · exact Submodule.isCompl_span_singleton_of_isCoatom_of_notMem
      (Submodule.isCoatom_of_quot_rank_eq_one (K:=K) (V:=V) p h) xnotinp

end Quotient

end DivisionRing

end Module
