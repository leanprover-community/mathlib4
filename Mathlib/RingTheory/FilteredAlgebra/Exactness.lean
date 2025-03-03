/-
Copyright (c) 2025 Huanyu Zheng, Weichen Jiao, Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng, Weichen Jiao, Yi Yuan
-/
import Mathlib.RingTheory.FilteredAlgebra.FilteredRingHom
import Mathlib.Algebra.Exact
/-!

-/

section ExhaustiveFiltration

variable {ι A σ : Type*} [Preorder ι] [SetLike σ A]

/-- -/
class IsExhaustiveFiltration (F : ι → σ) (F_lt : ι → σ) [IsFiltration F F_lt] : Prop where
  exhaustive : ⋃ i, (F i : Set A) = Set.univ

end ExhaustiveFiltration



section exactness

variable {ι R S T σR σS σT : Type*} [DecidableEq ι] [OrderedAddCommMonoid ι]

variable [Ring R] [SetLike σR R] [AddSubgroupClass σR R]

variable [Ring S] [SetLike σS S] [AddSubgroupClass σS S]

variable [Ring T] [SetLike σT T] [AddSubgroupClass σT T]

variable {FR : ι → σR} {FS : ι → σS} {FT : ι → σT}

variable {FR_lt: outParam <| ι → σR} {FS_lt: outParam <| ι → σS} {FT_lt: outParam <| ι → σT}

variable [IsRingFiltration FS FS_lt]

variable (f : FilteredRingHom FR FR_lt FS FS_lt) (g : FilteredRingHom FS FS_lt FT FT_lt)

open DirectSum DFinsupp FilteredAddGroupHom
open scoped FilteredRingHom

omit [DecidableEq ι] in
lemma exact_component_of_strict_exact_component (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (fgexact : Function.Exact f.toAddMonoidHom g.toAddMonoidHom) :
    ∀ p : ι, ∀ x : GradedPiece FS FS_lt p, Gr(p)[g] x = 0 → ∃ y : FR p, Gr(p)[f] ⟦y⟧ = x := by
  intro p x₀ xto0
  obtain⟨x, hx⟩ : ∃ x, GradedPiece.mk FS FS_lt x = x₀:= Quotient.exists_rep x₀
  rw[← hx] at xto0 ⊢
  obtain⟨x', xin, geq⟩ : g.toRingHom x ∈ g.toRingHom '' (FS_lt p) := by
    apply gstrict.strict_lt
    · rw [GradedPieceHom_apply_mk_eq_mk_piece_wise_hom, GradedPiece.mk_eq,
          QuotientAddGroup.eq_zero_iff] at xto0
      exact xto0
    · simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Set.mem_range,
      exists_apply_eq_apply]
  obtain⟨y, yin, feq⟩ : x - x' ∈ f.toRingHom '' (FR p) := by
    apply_fun (fun m ↦ m - g.toRingHom x') at geq
    rw [sub_self, ← map_sub] at geq
    have sub_mem_mp : x.1 - x' ∈ FS p :=
      sub_mem (SetLike.coe_mem x) <| (IsFiltration.lt_le FS FS_lt p) xin
    have : (x - x' : S) ∈ (g.toAddMonoidHom).ker := geq.symm
    rw[Function.Exact.addMonoidHom_ker_eq fgexact] at this
    apply fstrict.strict sub_mem_mp this
  use ⟨y, yin⟩
  rw[← GradedPiece.mk_eq, GradedPieceHom_apply_mk_eq_mk_piece_wise_hom]
  simp only [GradedPiece.mk_eq]
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : (toFilteredHom.piece_wise_hom p ⟨y, yin⟩ : FS p) = f.toRingHom y := rfl
  simp [this, feq, xin]

variable  [hasGMul FR FR_lt] [hasGMul FS FS_lt] [hasGMul FT FT_lt]

theorem exact_of_strict_exact (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toRingHom g.toRingHom) : Function.Exact Gr[f] Gr[g] := by
  intro m
  constructor
  · intro h
    have (i : ι) : ∃ y, Gr(i)[f] ⟦y⟧ = m i := by
      apply exact_component_of_strict_exact_component f g fstrict gstrict exact i
      have : (Gr[g] m) i = 0 := by simp [h]
      simpa
    set component_2 := fun (i : support m) ↦
      (⟦Classical.choose (this i)⟧ : GradedPiece FR FR_lt i) with hc
    set s : AssociatedGraded FR FR_lt := DirectSum.mk
      (fun i ↦ GradedPiece FR FR_lt i) (support m) component_2 with hs
    have : Gr[f] s = m := by
      apply AssociatedGraded.ext_iff.mpr
      intro j
      simp only [FilteredRingHom.AssociatedGradedRingHom_apply]
      by_cases nh : j ∈ support m
      · rw [mk_apply_of_mem nh, hc, Classical.choose_spec (this j)]
      · rw [hs, mk_apply_of_not_mem nh, map_zero]
        rw [mem_support_toFun, ne_eq, not_not] at nh
        rw [nh]
    rw [← this]
    exact Set.mem_range_self s
  · rintro ⟨l, hl⟩
    rw [← hl]
    show (Gr[g].comp Gr[f]) l = 0
    rw [FilteredRingHom.AssociatedGradedRingHom_comp_eq_comp g f]
    ext i
    obtain⟨k, hk⟩ : ∃ k, GradedPiece.mk FR FR_lt k = l i := Quotient.exists_rep (l i)
    have : ((g.comp f).piece_wise_hom i) k = 0 :=
      ZeroMemClass.coe_eq_zero.mp (Function.Exact.apply_apply_eq_zero exact k)
    simp [← hk, this]

end exactness
