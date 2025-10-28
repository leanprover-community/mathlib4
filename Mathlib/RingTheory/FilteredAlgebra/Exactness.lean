/-
Copyright (c) 2025 Huanyu Zheng, Weichen Jiao, Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng, Weichen Jiao, Yi Yuan
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Exact
import Mathlib.RingTheory.FilteredAlgebra.FilteredHom
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Tactic.Linarith.Frontend

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
  · exact ⟨x i, by rw [← of_eq_same i y, ← hx, AssociatedGradedAddMonoidHom_apply]⟩
  · exact ⟨AssociatedGraded.of x, by simp [hx]⟩

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
    rw [GradedPieceHom_apply_mk_eq_mk_piece_wise_hom, GradedPiece.mk, QuotientAddGroup.mk'_eq_mk']
    exact ⟨⟨s', IsFiltration.F_lt_le_F FS FS_lt i hs'⟩, ⟨hs', SetCoe.ext this⟩⟩
  · induction y using QuotientAddGroup.induction_on
    rename_i z
    rw [← hy, GradedPieceHom_comp_apply]
    exact congrArg (GradedPiece.mk FT FT_lt) (SetCoe.ext (fgexact.apply_apply_eq_zero z.1))

theorem exact_of_strict_exact (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toAddMonoidHom g.toAddMonoidHom) : Function.Exact Gr+[f] Gr+[g] :=
  AssociatedGradedAddMonoidHom_exact_of_GradedPieceHom_exact f g
    (fun i x ↦ exact_component_of_strict_exact_component f g fstrict gstrict exact i x)

end exactness


section

open AddSubgroup IsFiltration FilteredHom
open FilteredAddGroupHom AssociatedGradedAddMonoidHom

variable {ι R S T σR σS σT : Type*}

variable [AddCommGroup R] [SetLike σR R] [AddSubgroupClass σR R] {FR : ℤ → σR}

variable [AddCommGroup S] [SetLike σS S] [AddSubgroupClass σS S] {FS : ℤ → σS}

variable [AddCommGroup T] [SetLike σT T] [AddSubgroupClass σT T] {FT : ℤ → σT}

variable (f : FilteredAddGroupHom FR (fun n ↦ FR (n - 1)) FS (fun n ↦ FS (n - 1)))

variable (g : FilteredAddGroupHom FS (fun n ↦ FS (n - 1)) FT (fun n ↦ FT (n - 1)))

open AssociatedGraded

omit [AddSubgroupClass σR R] in
variable {f g} in
lemma zero_of_pieces_range {p : ℤ} {y : FS p} (hy : y.1 ∈ Set.range f)
  (comp_eq_zero : g.toAddMonoidHom.comp f.toAddMonoidHom = 0) :
    Gr+[g] (of ((GradedPiece.mk FS fun n ↦ FS (n - 1)) y)) = 0 := by
  obtain ⟨x, hx⟩ := hy
  rw [← AddMonoidHom.mem_ker]
  rw [FilteredAddGroupHom.AssociatedGradedAddMonoidHom.mem_ker_iff]
  intro i
  by_cases h : i = p
  · rw [h, DirectSum.of_eq_same p _]
    simp only [AddMonoidHom.mem_ker, GradedPieceHom_apply_mk_eq_mk_piece_wise_hom]
    have : g.toAddMonoidHom.comp f.toAddMonoidHom x = 0 := by simp [comp_eq_zero]
    have : ((g.piece_wise_hom p) y) = 0 := by
      simpa [← Subtype.val_inj, FilteredHom.piece_wise_hom, ← hx]
    simp [this]
  · simp [of_eq_of_ne p i (GradedPiece.mk FS (fun n ↦ FS (n - 1)) (y : ofClass (FS p))) h]

theorem strict_of_exhaustive_exact (monoS : Monotone FS) (monoT : Monotone FT)
    (exact : Function.Exact Gr+[f] Gr+[g])
    (exhaustiveS : letI := (mk_int FS monoS); IsExhaustiveFiltration FS (fun n ↦ FS (n - 1)))
    (comp_eq_zero : g.toAddMonoidHom.comp f.toAddMonoidHom = 0) :
    IsStrict FS (fun n ↦ FS (n - 1)) FT (fun n ↦ FT (n - 1)) g := by
  apply IsStrict_of_Int
  intro p z zp ⟨y₀, gy₀z⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, y₀ ∈ FS (p + s) := by
    have : y₀ ∈ ⋃ i, (FS i : Set S) := by simp only [exhaustiveS.exhaustive, Set.mem_univ]
    rcases Set.mem_iUnion.mp this with ⟨p', y₀p'⟩
    rcases Int.eq_ofNat_of_zero_le (Int.sub_nonneg_of_le (Int.le_max_left p p')) with ⟨s, hs⟩
    exact ⟨s, by simpa only [← hs, add_sub_cancel] using monoS (Int.le_max_right p p') y₀p'⟩
  have (i : ℕ) : i ≤ s → ∃ y ∈ FS (p + s - i), g y = z := by
    intro h
    induction i
    · simpa using ⟨y₀, ⟨hs, gy₀z⟩⟩
    · rename_i i ih
      rcases ih (Nat.le_of_succ_le h) with ⟨y, ymem, yeq⟩
      simp only [Nat.cast_add, Nat.cast_one]
      have hy : Gr+(p + s - i)[g] (GradedPiece.mk FS (fun n ↦ FS (n - 1)) ⟨y, ymem⟩) = 0 := by
        have zin : z ∈ FT (p + s - i) := by
          rw [← yeq]
          exact SetLike.coe_mem ((g.piece_wise_hom (p + s - i)) ⟨y, ymem⟩)
        have : ((g.piece_wise_hom (p + s - i)) ⟨y, ymem⟩) = (⟨z, zin⟩ : FT (p + s - i)):=
          SetLike.coe_eq_coe.mp yeq
        rw [GradedPieceHom_apply_mk_eq_mk_piece_wise_hom, this, GradedPiece.mk_eq,
          QuotientAddGroup.eq_zero_iff]
        have : p ≤ p + s - i - 1 := by linarith
        exact monoT this zp
      obtain ⟨xi, fxiy⟩ : (GradedPiece.mk FS (fun n ↦ FS (n - 1)) ⟨y, ymem⟩) ∈
          Gr+(p + s - i)[f].range := by
        simpa only [← AddMonoidHom.exact_iff.mp
          (GradedPieceHom_exact_of_AssociatedGradedAddMonoidHom_exact f g (p + s - i) exact)]
          using hy
      induction xi using GradedPiece.induction_on
      rename_i xiout
      rw [GradedPieceHom_apply_mk_eq_mk_piece_wise_hom, GradedPiece.mk_eq,
        GradedPiece.mk_eq, QuotientAddGroup.eq_iff_sub_mem] at fxiy
      use y - f xiout
      constructor
      · have : (p + s - (i + 1)) = p + s - i - 1 := (Int.sub_sub (p + s) i 1).symm
        simpa only [this, ← neg_sub (f xiout) y] using neg_mem fxiy
      · have : (g.toAddMonoidHom.comp f.toAddMonoidHom) xiout = 0 := by simp [comp_eq_zero]
        simpa only [map_sub, yeq, sub_eq_self]
  rcases this s (Nat.le_refl s) with ⟨y, ymem, gyz⟩
  exact ⟨y, ⟨by simpa only [add_sub_cancel_right] using ymem, gyz⟩⟩

theorem strict_of_exact_discrete (monoR : Monotone FR) (monoS : Monotone FS)
    (exact : Function.Exact Gr+[f] Gr+[g])
    (discrete : letI := (mk_int FS monoS); IsDiscreteFiltration FS (fun n ↦ FS (n - 1)))
    (comp_eq_zero : g.toAddMonoidHom.comp f.toAddMonoidHom = 0) :
    IsStrict FR (fun n ↦ FR (n - 1)) FS (fun n ↦ FS (n - 1)) f := by
    refine FilteredHom.IsStrict_of_Int fun {p y} hp ⟨x', hx'⟩ ↦ ?_
    rcases discrete.discrete with ⟨t₀, t₀bot⟩
    have le_zero : ∀ t ≤ t₀, (FS t : Set S) = {0} := fun t ht ↦ (Set.Nonempty.subset_singleton_iff
      Set.Nonempty.of_subtype).mp (le_of_eq_of_le' t₀bot (monoS ht))
    have (s : ℕ) : ∃ r : FR p, y - f r ∈ (f.range : Set S) ∩ FS (p - s) := by
      let yₚ := of (GradedPiece.mk FS (fun n ↦ FS (n - 1)) (⟨y, hp⟩ : ofClass (FS p)))
      obtain ⟨xₚ, hxₚ⟩ := (exact yₚ).1 <| zero_of_pieces_range ⟨x', hx'⟩ comp_eq_zero
      induction s
      · induction xₚ p using GradedPiece.induction_on
        rename_i xₚp
        refine ⟨xₚp, ⟨⟨x' - xₚp, hx' ▸ AddMonoidHom.map_sub f.toAddMonoidHom x' xₚp⟩, ?_⟩⟩
        simp only [Nat.cast_zero, sub_zero, SetLike.mem_coe]
        rw [sub_eq_add_neg, add_comm]
        exact add_mem (neg_mem (FilteredHom.pieces_wise xₚp.2)) hp
      · rename_i s ih
        rcases ih with ⟨r, ⟨hr₁, hr₂⟩⟩
        let yₚₛ :=
          of (GradedPiece.mk FS (fun n ↦ FS (n - 1)) (⟨y - f r, hr₂⟩ : ofClass (FS (p - s))))
        obtain ⟨xₚₛ, hxₚₛ⟩ := (exact yₚₛ).mp (zero_of_pieces_range hr₁ comp_eq_zero)
        induction h : xₚₛ (p - s) using GradedPiece.induction_on
        rename_i xₚₛps
        have ps_mem_p : xₚₛps.val ∈ FR p := monoR (by omega) xₚₛps.2
        let xr := (⟨xₚₛps + r, add_mem ps_mem_p r.2⟩ : FR p)
        refine ⟨xr, ⟨⟨x' - xr, hx' ▸ map_sub f.toAddMonoidHom x' xr⟩, ?_⟩⟩
        apply_fun (· (p - s)) at hxₚₛ
        rw [AssociatedGradedAddMonoidHom_apply, h, DirectSum.of_eq_same,
          GradedPieceHom_apply_mk_eq_mk_piece_wise_hom, GradedPiece.mk_eq, GradedPiece.mk_eq,
          Quotient.eq, QuotientAddGroup.leftRel_apply] at hxₚₛ
        have : y - (f.piece_wise_hom p) (⟨xₚₛps, ps_mem_p⟩ + r) ∈ FS (p - (s + 1)) := by
          rwa [sub_eq_add_neg y, add_comm y, map_add, AddMemClass.coe_add, neg_add_rev,
          add_comm (- ((f.piece_wise_hom p) r).val), add_assoc, add_comm _ y, ← sub_eq_add_neg y,
          sub_add_eq_sub_sub]
        exact this
    obtain ⟨s, hs⟩ : ∃ s : ℕ, p - s ≤ t₀ := by
      have : 0 ≤ - t₀ + t₀.natAbs + p.natAbs := by omega
      rcases Int.eq_ofNat_of_zero_le this with ⟨s, hs⟩
      use s
      rw [← hs]
      omega
    rcases this s with ⟨r, hr⟩
    rw [le_zero (p - s) hs, (Set.inter_eq_right.2 fun x hx ↦ hx.symm ▸ zero_mem f.range),
      Set.mem_singleton_iff, sub_eq_zero] at hr
    exact ⟨r, ⟨r.2, hr.symm⟩⟩

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
      induction s
      · exact ⟨0, by simpa using hy⟩
      · rename_i s ih
        rcases ih with ⟨r, hr⟩
        have : g (y - f r) = 0 := by simpa [yto0] using comp_zero r
        have mem_ker :
          Gr+(p - s)[g] (GradedPiece.mk FS (fun n ↦ FS (n - 1)) ⟨y - f r, hr⟩) = 0 := by
          rw [← map_zero (GradedPiece.mk FT (fun n ↦ FT (n - 1))),
            GradedPieceHom_apply_mk_eq_mk_piece_wise_hom]
          congr
          exact SetCoe.ext this
        rcases ((GradedPieceHom_exact_of_AssociatedGradedAddMonoidHom_exact f g _ exact) _).mp
           mem_ker with ⟨r', hr'⟩
        induction r' using GradedPiece.induction_on
        rename_i r'out
        have : Gr+(p - s)[f] ((GradedPiece.mk FR fun n ↦ FR (n - 1)) r'out) =
            (GradedPiece.mk FS fun n ↦ FS (n - 1)) ⟨y - f r, hr⟩ := by
          simpa using hr'
        simp only [GradedPieceHom_apply_mk_eq_mk_piece_wise_hom, Eq.comm] at this
        use r + r'out
        simpa only [Nat.cast_add, Nat.cast_one, map_add, sub_add_eq_sub_sub] using
          QuotientAddGroup.eq_iff_sub_mem.mp this
    rcases Int.eq_ofNat_of_zero_le (Int.sub_nonneg_of_le tlep) with ⟨s, hs⟩
    rcases this s with ⟨r, hr⟩
    have : y - f r ∈ (FS t : Set S) := by simpa only [← hs, sub_sub_cancel] using hr
    simp only [tbot, Set.mem_singleton_iff] at this
    exact ⟨r, by rw [← zero_add (f r), ← this, sub_add_cancel]⟩

end
