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

open AddSubgroup IsFiltration FilteredHom
open FilteredAddGroupHom AssociatedGradedAddMonoidHom

variable {ι R S T σR σS σT : Type*} [DecidableEq ι]

variable [AddCommGroup R] [SetLike σR R] [AddSubgroupClass σR R] {FR : ℤ → σR}

variable [AddCommGroup S] [SetLike σS S] [AddSubgroupClass σS S] {FS : ℤ → σS}

variable [AddCommGroup T] [SetLike σT T] [AddSubgroupClass σT T] {FT : ℤ → σT}

variable (f : FilteredAddGroupHom FR (fun n ↦ FR (n - 1)) FS (fun n ↦ FS (n - 1)))

variable (g : FilteredAddGroupHom FS (fun n ↦ FS (n - 1)) FT (fun n ↦ FT (n - 1)))

open AssociatedGraded in
omit [AddSubgroupClass σR R] in
lemma zero_of_pieces_range {p : ℤ} {y : FS p} (hy : y.1 ∈ Set.range f)
  (comp_eq_zero : g.toAddMonoidHom.comp f.toAddMonoidHom = 0) :
    Gr+[g] (of ((GradedPiece.mk FS fun n ↦ FS (n - 1)) y)) = 0 := by
  have comp_zero (x : R) : (g.toAddMonoidHom.comp f.toAddMonoidHom) x = 0 := by
    simp only [comp_eq_zero, AddMonoidHom.zero_apply]
  obtain ⟨x, hx⟩ := hy
  set yₚ := GradedPiece.mk FS (fun n ↦ FS (n - 1)) (y : ofClass (FS p))
  convert_to of yₚ ∈ Gr+[g].ker
  rw [FilteredAddGroupHom.AssociatedGradedAddMonoidHom.mem_ker_iff]
  intro i
  by_cases h : i = p
  · rw [h]
    convert_to yₚ ∈ Gr+(p)[g].ker
    · exact DirectSum.of_eq_same p yₚ
    · simp only [GradedPieceHom, GradedPiece.mk, QuotientAddGroup.mk'_apply,
        AddMonoidHom.mem_ker, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff, yₚ]
      suffices ((g.piece_wise_hom p) y) = 0 from
        (QuotientAddGroup.eq_zero_iff ((g.piece_wise_hom p) y)).1
          (congrArg QuotientAddGroup.mk this)
      suffices g y = 0 from ZeroMemClass.coe_eq_zero.1 this
      rw [← hx]
      convert_to g (f x) = 0
      exact comp_zero x
  · convert_to 0 ∈ Gr+(i)[g].ker
    · exact AssociatedGraded.of_eq_of_ne p i yₚ fun a ↦ h (id a.symm)
    · simp only [AddMonoidHom.mem_ker, map_zero, yₚ]

theorem strict_of_exhaustive_exact (monoS : Monotone FS) (exact : Function.Exact Gr+[f] Gr+[g])
    (exhaustiveS : letI := (mk_int FS monoS); IsExhaustiveFiltration FS (fun n ↦ FS (n - 1)))
    (comp_eq_zero : g.toAddMonoidHom.comp f.toAddMonoidHom = 0) :
    IsStrict FS (fun n ↦ FS (n - 1)) FT (fun n ↦ FT (n - 1)) g := by
      refine IsStrict_of_Int ?_
      intro p z zp ⟨y₀, gy₀z⟩
      have : ∃ s : ℕ, y₀ ∈ FS (p + s) := by
        have : y₀ ∈ ⋃ i, (FS i : Set S) := by simp only [exhaustiveS.exhaustive, Set.mem_univ]
        rcases Set.mem_iUnion.mp this with ⟨p', y₀p'⟩
        rcases Int.eq_ofNat_of_zero_le (Int.sub_nonneg_of_le (Int.le_max_left p p')) with ⟨s, hs⟩
        exact ⟨s, by simpa only [← hs, add_sub_cancel] using monoS (Int.le_max_right p p') y₀p'⟩
      rcases this with ⟨s, hs⟩
      have (i : ℕ) : ∃ y : FS (p + s - i), g y = z := by
        induction' i with i ih
        · simpa only [Int.Nat.cast_ofNat_Int, Subtype.exists, sub_zero] using ⟨y₀, ⟨hs, gy₀z⟩⟩
        · rcases ih with ⟨y, yeq⟩
          simp only [Subtype.exists, Nat.cast_add, Nat.cast_one, exists_prop]
          have hy : Gr+(p + s - i)[g] (GradedPiece.mk FS (fun n ↦ FS (n - 1)) y) = 0 := sorry
          have iex := GradedPieceHom_exact_of_AssociatedGradedAddMonoidHom_exact f g (p + s - i) exact
          have hy : (GradedPiece.mk FS (fun n ↦ FS (n - 1)) y) ∈ Gr+(p + s - i)[f].range := by
            simpa [← AddMonoidHom.exact_iff.mp iex] using hy
          rcases hy with ⟨xi, fxiy⟩
          set x := xi.out with xxi
          use y - f x
          constructor
          · sorry
          · simp only [map_sub, yeq, sub_eq_self]
            show (g.toAddMonoidHom.comp f.toAddMonoidHom) x = 0
            simp only [comp_eq_zero, AddMonoidHom.zero_apply]

theorem strict_exact_discrete
    (monoS : Monotone FS) (exact : Function.Exact Gr+[f] Gr+[g])
    (discrete : letI := (mk_int FS monoS); IsDiscreteFiltration FS (fun n ↦ FS (n - 1)))
    (comp_eq_zero : g.toAddMonoidHom.comp f.toAddMonoidHom = 0) :
  IsStrict FR (fun n ↦ FR (n - 1)) FS (fun n ↦ FS (n - 1)) f := {
    strict {p y} hp hy := by
      simp only [Set.mem_range, Set.mem_image, SetLike.mem_coe]
      have := discrete.discrete
      set y' := GradedPiece.mk FS (fun n ↦ FS (n - 1)) (⟨y, hp⟩ : ofClass (FS p))
      set yₚ := AssociatedGraded.of y'
      obtain ⟨xₚ, hxₚ⟩ := Set.mem_range.1 <| (exact yₚ).1 (zero_of_pieces_range f g hy comp_eq_zero)

      sorry
    strict_lt := sorry
  }

theorem ker_in_range_of_graded_exact (monoS : Monotone FS)
    (exhaustiveS : letI := (mk_int FS monoS); IsExhaustiveFiltration FS (fun n ↦ FS (n - 1)))
    (discrete : letI := (mk_int FS monoS); IsDiscreteFiltration FS (fun n ↦ FS (n - 1)))
    (exact : Function.Exact Gr+[f] Gr+[g])
    (comp_eq_zero : g.toAddMonoidHom.comp f.toAddMonoidHom = 0) : Function.Exact f g := by
  have comp_zero (x : R) : (g.toAddMonoidHom.comp f.toAddMonoidHom) x = 0 := by simp [comp_eq_zero]
  apply Function.Exact.of_comp_of_mem_range
  · exact funext (fun x ↦ comp_zero x)
  · intro y yto0
    have : y ∈ ⋃ i, (FS i : Set S) := by simp only [exhaustiveS.exhaustive, Set.mem_univ]
    rcases Set.mem_iUnion.mp this with ⟨p, hy⟩
    obtain ⟨t, tlep, tbot⟩ : ∃ t ≤ p, (FS t : Set S) = {0} := by
      rcases discrete.discrete with ⟨t₀, t₀bot⟩
      refine ⟨min p t₀, ⟨Int.min_le_left p t₀, ?_⟩⟩
      rw [← Set.Nonempty.subset_singleton_iff Set.Nonempty.of_subtype, ← t₀bot]
      exact monoS (Int.min_le_right p t₀)
    have (s : ℕ) : ∃ r : R, y - f r ∈ FS (p - s) := by
      induction' s with s ih
      · use 0
        simpa using hy
      · rcases ih with ⟨r, hr⟩
        have : g (y - f r) = 0 := by simpa [yto0] using comp_zero r
        have mem_ker :
          Gr+(p - s)[g] (GradedPiece.mk FS (fun n ↦ FS (n - 1)) ⟨y - f r, hr⟩) = 0 := by
          rw [← map_zero (GradedPiece.mk FT (fun n ↦ FT (n - 1))),
            GradedPieceHom_apply_mk_eq_mk_piece_wise_hom]
          congr
          exact SetCoe.ext this
        rcases ((GradedPieceHom_exact_of_AssociatedGradedAddMonoidHom_exact f g _ exact) _).mp
           mem_ker with ⟨r', hr'⟩
        have : Gr+(p - s)[f] ((GradedPiece.mk FR fun n ↦ FR (n - 1)) r'.out) =
          (GradedPiece.mk FS fun n ↦ FS (n - 1)) ⟨y - f r, hr⟩ := by
          simpa [GradedPiece.mk] using hr'
        simp only [GradedPieceHom_apply_mk_eq_mk_piece_wise_hom, Eq.comm] at this
        use r + r'.out.1
        simpa only [Nat.cast_add, Nat.cast_one, map_add, sub_add_eq_sub_sub] using
          QuotientAddGroup.eq_iff_sub_mem.mp this
    rcases Int.eq_ofNat_of_zero_le (Int.sub_nonneg_of_le tlep) with ⟨s, hs⟩
    rcases this s with ⟨r, hr⟩
    use r
    have : y - f r ∈ (FS t : Set S) := by simpa only [← hs, sub_sub_cancel] using hr
    simp only [tbot, Set.mem_singleton_iff] at this
    rw [← zero_add (f r), ← this, sub_add_cancel]

end
