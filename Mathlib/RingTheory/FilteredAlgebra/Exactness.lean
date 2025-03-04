/-
Copyright (c) 2025 Huanyu Zheng, Weichen Jiao, Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng, Weichen Jiao, Yi Yuan
-/
import Mathlib.Algebra.Exact
import Mathlib.RingTheory.FilteredAlgebra.FilteredRingHom

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
    (fgexact : Function.Exact f.toAddMonoidHom g.toAddMonoidHom) (i : ι)
    (x : GradedPiece FS FS_lt i) : Gr(i)[g] x = 0 ↔ x ∈ Set.range Gr(i)[f] :=
    QuotientAddGroup.induction_on x <| fun s ↦ by
  refine ⟨fun h ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · simp only [← GradedPiece.mk_eq, FilteredRingHom.GradedPieceHom_apply_mk_eq_mk_piece_wise_hom]
    have : ((g.piece_wise_hom i) s).1 ∈ FT_lt i := by
      simp only [← GradedPiece.mk_eq, GradedPieceHom_apply_mk_eq_mk_piece_wise_hom] at h
      simpa [GradedPiece.mk] using h
    rcases gstrict.strict_lt this (Set.mem_range_self s.1) with ⟨s', hs', eqs⟩
    have := g.toAddMonoidHom.eq_iff.mp eqs.symm
    rw [Function.Exact.addMonoidHom_ker_eq fgexact] at this
    have mem := (add_mem (neg_mem (IsFiltration.F_lt_le_F FS FS_lt i hs')) s.2)
    rcases fstrict.strict mem this with ⟨r, hr, eq⟩
    have : f.toFun r + s' = s := by rw [eq, neg_add_cancel_comm]
    use GradedPiece.mk FR FR_lt ⟨r, hr⟩
    rw [GradedPieceHom_apply_mk_eq_mk_piece_wise_hom]
    simp only [GradedPiece.mk, QuotientAddGroup.mk'_eq_mk']
    use ⟨s', IsFiltration.F_lt_le_F FS FS_lt i hs'⟩
    exact ⟨hs', SetCoe.ext this⟩
  · induction y using QuotientAddGroup.induction_on
    rename_i z
    rw [← hy, FilteredRingHom.GradedPieceHom_comp_apply]
    exact congrArg (GradedPiece.mk FT FT_lt) (SetCoe.ext (fgexact.apply_apply_eq_zero z.1))

variable  [hasGMul FR FR_lt] [hasGMul FS FS_lt] [hasGMul FT FT_lt]

theorem exact_of_strict_exact (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toRingHom g.toRingHom) : Function.Exact Gr[f] Gr[g] := by
  intro m
  have iff1 : Gr[g] m = 0 ↔ ∀ i : ι, Gr(i)[g] (m i) = 0 := by
    refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
    · rw [← FilteredRingHom.AssociatedGradedRingHom_apply, h, DirectSum.zero_apply]
    · ext i
      simp [h i]
  have iff2 : m ∈ Set.range Gr[f] ↔ ∀ i : ι, m i ∈ Set.range Gr(i)[f] := by
    refine ⟨fun ⟨l, hl⟩ i ↦ ?_, fun h ↦ ?_⟩
    · rw [← hl, FilteredRingHom.AssociatedGradedRingHom_apply]
      use l i
    · use DirectSum.mk (GradedPiece FR FR_lt) (support m) (fun i ↦ Classical.choose (h i))
      ext i
      rw [FilteredRingHom.AssociatedGradedRingHom_apply]
      by_cases mem : i ∈ support m
      · rw [mk_apply_of_mem mem, Classical.choose_spec (h i)]
      · rw [mk_apply_of_not_mem mem, not_mem_support_iff.mp mem, map_zero]
  rw [iff1, iff2]
  exact forall_congr'
    (fun i ↦ exact_component_of_strict_exact_component f g fstrict gstrict exact i (m i))

end exactness
