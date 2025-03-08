/-
Copyright (c) 2025 Huanyu Zheng, Weichen Jiao, Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng, Weichen Jiao, Yi Yuan
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Exact
import Mathlib.RingTheory.FilteredAlgebra.FilteredHom
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The property of exactness om AssociatedGradedRingHom

In this file, we define the concept of exhaustive filtrations.

We also prove a AssociatedGradedRingHom sequence is exact iff each GradedPieceHom is exact.

And when a sequence is strict exact, the corresponding AssociatedGradedRingHom sequence is also
exact.

# Main definitions

* `IsExhaustiveFiltration` : `F`, `F_lt` is a filtration of `A`, `F` is exhaustive if `A = ⋃ F n`
-/

section ExhaustiveFiltration

variable {ι A σ : Type*} [Preorder ι] [SetLike σ A]

/-- `F`, `F_lt` is a filtration of `A`, `F` is exhaustive if `A = ⋃ F n`-/
class IsExhaustiveFiltration (F : ι → σ) (F_lt : ι → σ) [IsFiltration F F_lt] : Prop where
  exhaustive : ⋃ i, (F i : Set A) = Set.univ

end ExhaustiveFiltration



variable {ι R S T σR σS σT : Type*} [DecidableEq ι] [OrderedAddCommMonoid ι]

variable [Ring R] [SetLike σR R] [AddSubgroupClass σR R]

variable [Ring S] [SetLike σS S] [AddSubgroupClass σS S]

variable [Ring T] [SetLike σT T] [AddSubgroupClass σT T]

variable {FR : ι → σR} {FS : ι → σS} {FT : ι → σT}

variable {FR_lt: outParam <| ι → σR} {FS_lt: outParam <| ι → σS} {FT_lt: outParam <| ι → σT}

variable (f : FilteredRingHom FR FR_lt FS FS_lt) (g : FilteredRingHom FS FS_lt FT FT_lt)

open scoped FilteredRingHom

variable [hasGMul FR FR_lt] [hasGMul FS FS_lt] [hasGMul FT FT_lt]



section AssociatedGradedRingHom_ext

open DirectSum

theorem AssociatedGradedRingHom_eq_zero_iff_GradedPieceHom_eq_zero (x : AssociatedGraded FS FS_lt) :
    Gr[g] x = 0 ↔ ∀ i : ι, Gr(i)[g] (x i) = 0 :=
  mem_map_ker_iff (fun i ↦ Gr(i)[g]) x

theorem GradedPieceHom_eq_zero_iff_AssociatedGradedRingHom_of_eq_zero {i : ι}
    (u : GradedPiece FS FS_lt i): Gr(i)[g] u = 0 ↔ Gr[g] (of (GradedPiece FS FS_lt) i u) = 0 :=
  of_mem_map_ker_iff (fun i ↦ Gr(i)[g]) i u

theorem AssociatedGradedRingHom_in_range_iff_GradedPieceHom_in_range
    (m : AssociatedGraded FS FS_lt) : m ∈ Gr[f].range ↔ ∀ i : ι, m i ∈ Set.range Gr(i)[f] :=
  mem_map_range_iff (fun i ↦ Gr(i)[f]) m

theorem GradedPieceHom_in_range_iff_AssociatedGradedRingHom_of_in_range {i : ι}
    (u : GradedPiece FS FS_lt i) : u ∈ Gr(i)[f].range ↔
    (of (GradedPiece FS FS_lt) i u) ∈ Gr[f].range := by
  convert (of_mem_map_range_iff (fun i ↦ Gr(i)[f]) i u).symm

theorem GradedPieceHom_ker_eq_GradedPieceHom_range (i : ι) (Gexact : Function.Exact Gr[f] Gr[g]) :
    Gr(i)[g].ker = Gr(i)[f].range := by
  ext u
  apply Iff.trans (GradedPieceHom_eq_zero_iff_AssociatedGradedRingHom_of_eq_zero g u)
  rw [Gexact ((of (GradedPiece FS FS_lt) i) u)]
  exact (GradedPieceHom_in_range_iff_AssociatedGradedRingHom_of_in_range f u).symm

theorem GradedPieceHom_exact_of_AssociatedGradedRingHom_exact :
    Function.Exact Gr[f] Gr[g] → ∀ i, Function.Exact Gr(i)[f] Gr(i)[g] :=
  fun h i ↦ AddMonoidHom.exact_iff.mpr
    (GradedPieceHom_ker_eq_GradedPieceHom_range f g i h)

end AssociatedGradedRingHom_ext

section exactness

open FilteredAddGroupHom

variable [IsRingFiltration FS FS_lt]

omit [hasGMul FR FR_lt] [hasGMul FS FS_lt] [hasGMul FT FT_lt] [DecidableEq ι] in
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

theorem exact_of_strict_exact (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toRingHom g.toRingHom) : Function.Exact Gr[f] Gr[g] := by
  intro m
  have : m ∈ Set.range Gr[f] ↔ m ∈ Gr[f].range := Set.mem_def
  rw [AssociatedGradedRingHom_eq_zero_iff_GradedPieceHom_eq_zero, this,
      AssociatedGradedRingHom_in_range_iff_GradedPieceHom_in_range]
  exact forall_congr'
    (fun i ↦ exact_component_of_strict_exact_component f g fstrict gstrict exact i (m i))

end exactness
