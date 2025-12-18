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

* `IsExhaustiveFiltration` : For `IsFiltration F F_lt`,
  the filtration is exhaustive if `Set.univ = ⋃ F i`.
-/

namespace FilteredAddGroupHom

variable {ι A B C σA σB σC : Type*} [SetLike σA A] [SetLike σB B] [SetLike σC C]

variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddSubgroupClass σA A] [AddSubgroupClass σB B] [AddSubgroupClass σC C]

variable {FA : ι → σA} {FA_lt : outParam <| ι → σA}
variable {FB : ι → σB} {FB_lt : outParam <| ι → σB}
variable {FC : ι → σC} {FC_lt : outParam <| ι → σC}
variable (f : FilteredAddGroupHom FA FA_lt FB FB_lt) (g : FilteredAddGroupHom FB FB_lt FC FC_lt)

open scoped FilteredAddGroupHom

open DirectSum

namespace AssociatedGradedAddMonoidHom

theorem mem_ker_iff (x : AssociatedGraded FB FB_lt) :
    x ∈ Gr+[g].ker ↔ ∀ i : ι, x i ∈ Gr+(i)[g].ker  := by
  simp only [AssociatedGradedAddMonoidHom, DirectSum.ker_map, AddSubgroup.mem_comap,
    coeFnAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact ⟨fun a i ↦ a i trivial, fun a i _ ↦ a i⟩

theorem associatedGraded_of_mem_ker_iff {i : ι} [DecidableEq ι] (u : GradedPiece FB FB_lt i) :
    AssociatedGraded.of u ∈ Gr+[g].ker ↔ u ∈ Gr+(i)[g].ker := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [AssociatedGradedAddMonoidHom, AddMonoidHom.mem_ker, AssociatedGraded.of, map_of] at h
    exact DFinsupp.single_eq_zero.mp h
  · simp [AddMonoidHom.mem_ker.mp h]

theorem mem_range_iff (m : AssociatedGraded FB FB_lt) :
    m ∈ Gr+[f].range ↔ ∀ i : ι, m i ∈ Gr+(i)[f].range := by
  simp only [AssociatedGradedAddMonoidHom, DirectSum.range_map, AddSubgroup.mem_comap,
    coeFnAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact ⟨fun a i ↦ a i trivial, fun a i a_1 ↦ a i⟩

theorem associatedGraded_of_mem_range_iff {i : ι} [DecidableEq ι] (y : GradedPiece FB FB_lt i) :
    (AssociatedGraded.of y) ∈ Gr+[f].range ↔ y ∈ Gr+(i)[f].range := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · use x i
    rw [← of_eq_same i y, ← hx, AssociatedGradedAddMonoidHom_apply]
  · use AssociatedGraded.of x
    simp [hx]

theorem GradedPieceHom_exact_of_AssociatedGradedAddMonoidHom_exact (i : ι)
    (Gexact : Function.Exact Gr+[f] Gr+[g]) : Function.Exact Gr+(i)[f] Gr+(i)[g] := by
  classical
  rw [AddMonoidHom.exact_iff]
  ext u
  rw [← associatedGraded_of_mem_ker_iff g u, Gexact.addMonoidHom_ker_eq,
    ← associatedGraded_of_mem_range_iff f u]

theorem AssociatedGradedAddMonoidHom_exact_of_GradedPieceHom_exact
    (h : ∀ i, Function.Exact Gr+(i)[f] Gr+(i)[g]) : Function.Exact Gr+[f] Gr+[g] := by
  classical
  rw [AddMonoidHom.exact_iff]
  ext x
  rw [mem_ker_iff, mem_range_iff]
  exact forall_congr' (fun i ↦ h i (x i))

end AssociatedGradedAddMonoidHom

end FilteredAddGroupHom

section ExhaustiveFiltration

variable {ι A σ : Type*} [Preorder ι] [SetLike σ A]

/-- For `IsFiltration F F_lt`, the filtration is exhaustive if `Set.univ = ⋃ F i`. -/
class IsExhaustiveFiltration (F : ι → σ) (F_lt : ι → σ) [IsFiltration F F_lt] : Prop where
  exhaustive : ⋃ i, (F i : Set A) = Set.univ

end ExhaustiveFiltration

section exactness

open FilteredAddGroupHom


variable {ι R S T σR σS σT : Type*}

variable [AddCommGroup R] [SetLike σR R] [AddSubgroupClass σR R]

variable [AddCommGroup S] [SetLike σS S] [AddSubgroupClass σS S]

variable [AddCommGroup T] [SetLike σT T] [AddSubgroupClass σT T]

variable {FR : ι → σR} {FS : ι → σS} {FT : ι → σT}

variable {FR_lt : outParam <| ι → σR} {FS_lt : outParam <| ι → σS} {FT_lt : outParam <| ι → σT}

variable (f : FilteredAddGroupHom FR FR_lt FS FS_lt) (g : FilteredAddGroupHom FS FS_lt FT FT_lt)

open FilteredAddGroupHom AssociatedGradedAddMonoidHom

variable [Preorder ι] [IsFiltration FS FS_lt]

lemma exact_component_of_strict_exact_component (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (fgexact : Function.Exact f.toAddMonoidHom g.toAddMonoidHom) (i : ι)
    (x : GradedPiece FS FS_lt i) : Gr+(i)[g] x = 0 ↔ x ∈ Set.range Gr+(i)[f] :=
    QuotientAddGroup.induction_on x <| fun s ↦ by
  refine ⟨fun h ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · simp only [← GradedPiece.mk_eq, Set.mem_range]
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
    rw [← hy, GradedPieceHom_comp_apply]
    exact congrArg (GradedPiece.mk FT FT_lt) (SetCoe.ext (fgexact.apply_apply_eq_zero z.1))

theorem exact_of_strict_exact (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toAddMonoidHom g.toAddMonoidHom) : Function.Exact Gr+[f] Gr+[g] :=
  AssociatedGradedAddMonoidHom_exact_of_GradedPieceHom_exact f g
    (fun i x ↦ exact_component_of_strict_exact_component f g fstrict gstrict exact i x)

end exactness
