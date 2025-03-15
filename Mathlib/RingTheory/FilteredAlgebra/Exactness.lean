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

variable {ι A B C σA σB σC: Type*} [SetLike σA A] [SetLike σB B] [SetLike σC C]

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
    x ∈ Gr+[g].ker ↔ ∀ i : ι, x i ∈ Gr+(i)[g].ker  :=
  mem_map_ker_iff (fun i ↦ Gr+(i)[g]) x

theorem associatedGraded_of_mem_ker_iff {i : ι} [DecidableEq ι] (u : GradedPiece FB FB_lt i) :
    of (GradedPiece FB FB_lt) i u ∈ Gr+[g].ker ↔ u ∈ Gr+(i)[g].ker :=
  of_mem_map_ker_iff (fun i ↦ Gr+(i)[g]) i u

theorem mem_range_iff [DecidableEq ι]
    (m : AssociatedGraded FB FB_lt) : m ∈ Gr+[f].range ↔ ∀ i : ι, m i ∈ Gr+(i)[f].range :=
  mem_map_range_iff (fun i ↦ Gr+(i)[f]) m

theorem associatedGraded_of_mem_range_iff {i : ι} [DecidableEq ι] (u : GradedPiece FB FB_lt i) :
    (of (GradedPiece FB FB_lt) i u) ∈ Gr+[f].range ↔ u ∈ Gr+(i)[f].range :=
  of_mem_map_range_iff (fun i ↦ Gr+(i)[f]) i u

theorem GradedPieceHom_exact_of_AssociatedGradedAddMonoidHom_exact (i : ι) [DecidableEq ι]
    (Gexact : Function.Exact Gr+[f] Gr+[g]) : Function.Exact Gr+(i)[f] Gr+(i)[g] := by
  rw [AddMonoidHom.exact_iff]
  ext u
  rw [← associatedGraded_of_mem_ker_iff g u, Gexact.addMonoidHom_ker_eq,
    ← associatedGraded_of_mem_range_iff f u]

theorem AssociatedGradedAddMonoidHom_exact_of_GradedPieceHom_exact [DecidableEq ι]
    (h : ∀ i, Function.Exact Gr+(i)[f] Gr+(i)[g]) : Function.Exact Gr+[f] Gr+[g] := by
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




section DiscreteFiltration

variable {ι A σ : Type*} [AddGroup A] [Preorder ι] [SetLike σ A]

/-- For `IsFiltration F F_lt`, the filtration is discrete if `Set.univ = ⋃ F i`. -/
class IsDiscreteFiltration (F : ι → σ) (F_lt : ι → σ) [IsFiltration F F_lt] : Prop where
  discrete : ∃ i : ι, (F i : Set A) = {0}

end DiscreteFiltration



section exactness

open FilteredAddGroupHom


variable {ι R S T σR σS σT : Type*}

variable [AddCommGroup R] [SetLike σR R] [AddSubgroupClass σR R]

variable [AddCommGroup S] [SetLike σS S] [AddSubgroupClass σS S]

variable [AddCommGroup T] [SetLike σT T] [AddSubgroupClass σT T]

variable {FR : ι → σR} {FS : ι → σS} {FT : ι → σT}

variable {FR_lt: outParam <| ι → σR} {FS_lt: outParam <| ι → σS} {FT_lt: outParam <| ι → σT}

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

theorem exact_of_strict_exact [DecidableEq ι] (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toAddMonoidHom g.toAddMonoidHom) : Function.Exact Gr+[f] Gr+[g] :=
  AssociatedGradedAddMonoidHom_exact_of_GradedPieceHom_exact f g
    (fun i x ↦ exact_component_of_strict_exact_component f g fstrict gstrict exact i x)

end exactness





section

open AddSubgroup FilteredAddGroupHom IsFiltration

variable {ι R S T σR σS σT : Type*}

variable [AddCommGroup R] [SetLike σR R] [AddSubgroupClass σR R] {FR : ℤ → σR} {monoR : Monotone FR}

variable [AddCommGroup S] [SetLike σS S] [AddSubgroupClass σS S] {FS : ℤ → σS} {monoS : Monotone FS}

variable [AddCommGroup T] [SetLike σT T] [AddSubgroupClass σT T] {FT : ℤ → σT} {monoT : Monotone FT}

variable (f : FilteredAddGroupHom FR (fun n ↦ FR (n - 1)) FS (fun n ↦ FS (n - 1)))

variable (g : FilteredAddGroupHom FS (fun n ↦ FS (n - 1)) FT (fun n ↦ FT (n - 1)))

lemma shrinking_lemma {monoR : Monotone FR} (S' : AddSubgroup S) {p : ℤ}
    (y : (ofClass (FS p) ⊓ S' : AddSubgroup S))
    (h : ∀ i : ℤ, ofClass (FS i) ⊓ S' ≤ AddSubgroup.map f (ofClass (FR i))) :
    ∀ s : ℕ, ∃ x : FR p, y - (f.toAddMonoidHom x) ∈ ofClass (FS (p - s)) ⊓ S' := by
  intro s
  induction' s with s ih
  · use 0
    simp[AddMonoidHom.map_zero f.toAddMonoidHom]
  · obtain⟨x₀, h₀⟩ := ih
    obtain⟨z, zin, eq⟩ : y - f.toAddMonoidHom x₀ ∈ (map f.toAddMonoidHom (ofClass (FR (p - s)))) :=
      h (p - s) h₀
    have : z ∈ (FR p) := by
      have : FR (p - s) ≤ FR p := by
        apply monoR
        simp
      exact this zin
    use (x₀ + ⟨z , this⟩)
    simp only [Nat.cast_add, Nat.cast_one, AddMemClass.coe_add, AddMonoidHom.map_add]
    simp [eq, AddSubgroup.zero_mem]



theorem exact_of_graded_exact
    (exhaustive : letI := (mk_int FS monoS); IsExhaustiveFiltration FS (fun n ↦ FS (n - 1)))
    (discrete : letI := (mk_int FS monoS); IsDiscreteFiltration FS (fun n ↦ FS (n - 1)))
    (exact : Function.Exact Gr+[f] Gr+[g]) : Function.Exact f.toAddMonoidHom g.toAddMonoidHom := by
  refine Function.Exact.of_comp_of_mem_range ?_ ?_
  · sorry
  · intro y yto0

    have : ∃ p : ℤ, y ∈ ofClass (FS p) ⊓ (AddMonoidHom.ker g.toAddMonoidHom) := by
      refine exists_and_right.mpr ⟨?_, yto0⟩
      have : y ∈ ⋃ i, (FS i : Set S) := by simp only [exhaustive.exhaustive, Set.mem_univ]
      exact Set.mem_iUnion.mp this
    rcases this with ⟨p, hy⟩

    have : ∃ t ≤ p, (FS t : Set S) = {0} := by
      rcases discrete.discrete with ⟨t₀, t₀bot⟩
      refine ⟨min p t₀, ⟨Int.min_le_left p t₀, ?_⟩⟩
      refine (Set.Nonempty.subset_singleton_iff Set.Nonempty.of_subtype).mp ?_
      rw [← t₀bot]
      apply Monotone.imp monoS (Int.min_le_right p t₀)
    rcases this with ⟨t, tlep, tbot⟩

    have : ∀ i : ℤ, (AddMonoidHom.ker g.toAddMonoidHom) ⊓ ofClass (FS i) ≤ AddSubgroup.map f (ofClass (FR i)) := sorry

    rcases Int.eq_ofNat_of_zero_le (Int.sub_nonneg_of_le tlep) with ⟨s, _⟩
    rcases shrinking_lemma f (AddMonoidHom.ker g.toAddMonoidHom) ⟨y, hy⟩ this s with ⟨x, hx⟩
    have eq : p - s = t := by omega
    rw [eq] at hx
    have hx : y - (f.toAddMonoidHom x) ∈ (FS t : Set S) := hx
    rw [tbot] at hx
    exact ⟨x, (eq_of_sub_eq_zero <| Set.mem_singleton_iff.mp hx).symm⟩


end
