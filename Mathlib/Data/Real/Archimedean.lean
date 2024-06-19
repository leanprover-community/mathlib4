/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Bounds
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Disjoint

#align_import data.real.basic from "leanprover-community/mathlib"@"cb42593171ba005beaaf4549fcfe0dece9ada4c9"

/-!
# The real numbers are an Archimedean floor ring, and a conditionally complete linear order.

-/

open scoped Classical
open Pointwise CauSeq

namespace Real

instance instArchimedean : Archimedean ℝ :=
  archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, _, H⟩ := f.bounded' 0
      ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 <| le_of_lt (abs_lt.1 (H i)).2⟩⟩
#align real.archimedean Real.instArchimedean

noncomputable instance : FloorRing ℝ :=
  Archimedean.floorRing _

theorem isCauSeq_iff_lift {f : ℕ → ℚ} : IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : ℝ) :=
  ⟨fun H ε ε0 =>
    let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => lt_trans (by simpa using (@Rat.cast_lt ℝ _ _ _).2 (hi _ ij)) δε,
    fun H ε ε0 =>
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij =>
      (@Rat.cast_lt ℝ _ _ _).1 <| by simpa using hi _ ij⟩
#align real.is_cau_seq_iff_lift Real.isCauSeq_iff_lift

theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| < ε) :
    ∃ h', Real.mk ⟨f, h'⟩ = x :=
  ⟨isCauSeq_iff_lift.2 (CauSeq.of_near _ (const abs x) h),
    sub_eq_zero.1 <|
      abs_eq_zero.1 <|
        (eq_of_le_of_forall_le_of_dense (abs_nonneg _)) fun _ε ε0 =>
          mk_near_of_forall_near <| (h _ ε0).imp fun _i h j ij => le_of_lt (h j ij)⟩
#align real.of_near Real.of_near

theorem exists_floor (x : ℝ) : ∃ ub : ℤ, (ub : ℝ) ≤ x ∧ ∀ z : ℤ, (z : ℝ) ≤ x → z ≤ ub :=
  Int.exists_greatest_of_bdd
    (let ⟨n, hn⟩ := exists_int_gt x
    ⟨n, fun _ h' => Int.cast_le.1 <| le_trans h' <| le_of_lt hn⟩)
    (let ⟨n, hn⟩ := exists_int_lt x
    ⟨n, le_of_lt hn⟩)
#align real.exists_floor Real.exists_floor

theorem exists_isLUB {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) : ∃ x, IsLUB S x := by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ S, (m : ℝ) ≤ y * d } := by
    cases' exists_int_gt U with k hk
    refine fun d => ⟨k * d, fun z h => ?_⟩
    rcases h with ⟨y, yS, hy⟩
    refine Int.cast_le.1 (hy.trans ?_)
    push_cast
    exact mul_le_mul_of_nonneg_right ((hU yS).trans hk.le) d.cast_nonneg
  choose f hf using fun d : ℕ =>
    Int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, Int.floor_le _⟩
  have hf₁ : ∀ n > 0, ∃ y ∈ S, ((f n / n : ℚ) : ℝ) ≤ y := fun n n0 =>
    let ⟨y, yS, hy⟩ := (hf n).1
    ⟨y, yS, by simpa using (div_le_iff (Nat.cast_pos.2 n0 : (_ : ℝ) < _)).2 hy⟩
  have hf₂ : ∀ n > 0, ∀ y ∈ S, (y - ((n : ℕ) : ℝ)⁻¹) < (f n / n : ℚ) := by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, gt_iff_lt]
    rwa [lt_div_iff (Nat.cast_pos.2 n0 : (_ : ℝ) < _), sub_mul, _root_.inv_mul_cancel]
    exact ne_of_gt (Nat.cast_pos.2 n0)
  have hg : IsCauSeq abs (fun n => f n / n : ℕ → ℚ) := by
    intro ε ε0
    suffices ∀ j ≥ ⌈ε⁻¹⌉₊, ∀ k ≥ ⌈ε⁻¹⌉₊, (f j / j - f k / k : ℚ) < ε by
      refine ⟨_, fun j ij => abs_lt.2 ⟨?_, this _ ij _ le_rfl⟩⟩
      rw [neg_lt, neg_sub]
      exact this _ le_rfl _ ij
    intro j ij k ik
    replace ij := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ij)
    replace ik := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ik)
    have j0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ij)
    have k0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ik)
    rcases hf₁ _ j0 with ⟨y, yS, hy⟩
    refine lt_of_lt_of_le ((@Rat.cast_lt ℝ _ _ _).1 ?_) ((inv_le ε0 (Nat.cast_pos.2 k0)).1 ik)
    simpa using sub_lt_iff_lt_add'.2 (lt_of_le_of_lt hy <| sub_lt_iff_lt_add.1 <| hf₂ _ k0 _ yS)
  let g : CauSeq ℚ abs := ⟨fun n => f n / n, hg⟩
  refine ⟨mk g, ⟨fun x xS => ?_, fun y h => ?_⟩⟩
  · refine le_of_forall_ge_of_dense fun z xz => ?_
    cases' exists_nat_gt (x - z)⁻¹ with K hK
    refine le_mk_of_forall_le ⟨K, fun n nK => ?_⟩
    replace xz := sub_pos.2 xz
    replace hK := hK.le.trans (Nat.cast_le.2 nK)
    have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    refine le_trans ?_ (hf₂ _ n0 _ xS).le
    rwa [le_sub_comm, inv_le (Nat.cast_pos.2 n0 : (_ : ℝ) < _) xz]
  · exact
      mk_le_of_forall_le
        ⟨1, fun n n1 =>
          let ⟨x, xS, hx⟩ := hf₁ _ n1
          le_trans hx (h xS)⟩
#align real.exists_is_lub Real.exists_isLUB

/-- A nonempty, bounded below set of real numbers has a greatest lower bound. -/
theorem exists_isGLB {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddBelow S) : ∃ x, IsGLB S x := by
  have hne' : (-S).Nonempty := Set.nonempty_neg.mpr hne
  have hbdd' : BddAbove (-S) := bddAbove_neg.mpr hbdd
  use -Classical.choose (Real.exists_isLUB hne' hbdd')
  rw [← isLUB_neg]
  exact Classical.choose_spec (Real.exists_isLUB hne' hbdd')

noncomputable instance : SupSet ℝ :=
  ⟨fun S => if h : S.Nonempty ∧ BddAbove S then Classical.choose (exists_isLUB h.1 h.2) else 0⟩

theorem sSup_def (S : Set ℝ) :
    sSup S = if h : S.Nonempty ∧ BddAbove S then Classical.choose (exists_isLUB h.1 h.2) else 0 :=
  rfl
#align real.Sup_def Real.sSup_def

protected theorem isLUB_sSup (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddAbove S) :
    IsLUB S (sSup S) := by
  simp only [sSup_def, dif_pos (And.intro h₁ h₂)]
  apply Classical.choose_spec
#align real.is_lub_Sup Real.isLUB_sSup

noncomputable instance : InfSet ℝ :=
  ⟨fun S => -sSup (-S)⟩

theorem sInf_def (S : Set ℝ) : sInf S = -sSup (-S) :=
  rfl
#align real.Inf_def Real.sInf_def

protected theorem is_glb_sInf (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddBelow S) :
    IsGLB S (sInf S) := by
  rw [sInf_def, ← isLUB_neg', neg_neg]
  exact Real.isLUB_sSup _ h₁.neg h₂.neg
#align real.is_glb_Inf Real.is_glb_sInf

noncomputable instance : ConditionallyCompleteLinearOrder ℝ :=
  { Real.linearOrder, Real.lattice with
    sSup := SupSet.sSup
    sInf := InfSet.sInf
    le_csSup := fun s a hs ha => (Real.isLUB_sSup s ⟨a, ha⟩ hs).1 ha
    csSup_le := fun s a hs ha => (Real.isLUB_sSup s hs ⟨a, ha⟩).2 ha
    csInf_le := fun s a hs ha => (Real.is_glb_sInf s ⟨a, ha⟩ hs).1 ha
    le_csInf := fun s a hs ha => (Real.is_glb_sInf s hs ⟨a, ha⟩).2 ha
    csSup_of_not_bddAbove := fun s hs ↦ by simp [hs, sSup_def]
    csInf_of_not_bddBelow := fun s hs ↦ by simp [hs, sInf_def, sSup_def] }

theorem lt_sInf_add_pos {s : Set ℝ} (h : s.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ s, a < sInf s + ε :=
  exists_lt_of_csInf_lt h <| lt_add_of_pos_right _ hε
#align real.lt_Inf_add_pos Real.lt_sInf_add_pos

theorem add_neg_lt_sSup {s : Set ℝ} (h : s.Nonempty) {ε : ℝ} (hε : ε < 0) :
    ∃ a ∈ s, sSup s + ε < a :=
  exists_lt_of_lt_csSup h <| add_lt_iff_neg_left.2 hε
#align real.add_neg_lt_Sup Real.add_neg_lt_sSup

theorem sInf_le_iff {s : Set ℝ} (h : BddBelow s) (h' : s.Nonempty) {a : ℝ} :
    sInf s ≤ a ↔ ∀ ε, 0 < ε → ∃ x ∈ s, x < a + ε := by
  rw [le_iff_forall_pos_lt_add]
  constructor <;> intro H ε ε_pos
  · exact exists_lt_of_csInf_lt h' (H ε ε_pos)
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    exact csInf_lt_of_lt h x_in hx
#align real.Inf_le_iff Real.sInf_le_iff

theorem le_sSup_iff {s : Set ℝ} (h : BddAbove s) (h' : s.Nonempty) {a : ℝ} :
    a ≤ sSup s ↔ ∀ ε, ε < 0 → ∃ x ∈ s, a + ε < x := by
  rw [le_iff_forall_pos_lt_add]
  refine ⟨fun H ε ε_neg => ?_, fun H ε ε_pos => ?_⟩
  · exact exists_lt_of_lt_csSup h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg)))
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    exact sub_lt_iff_lt_add.mp (lt_csSup_of_lt h x_in hx)
#align real.le_Sup_iff Real.le_sSup_iff

@[simp]
theorem sSup_empty : sSup (∅ : Set ℝ) = 0 :=
  dif_neg <| by simp
#align real.Sup_empty Real.sSup_empty

@[simp] lemma iSup_of_isEmpty {α : Sort*} [IsEmpty α] (f : α → ℝ) : ⨆ i, f i = 0 := by
  dsimp [iSup]
  convert Real.sSup_empty
  rw [Set.range_eq_empty_iff]
  infer_instance
#align real.csupr_empty Real.iSup_of_isEmpty

@[simp]
theorem ciSup_const_zero {α : Sort*} : ⨆ _ : α, (0 : ℝ) = 0 := by
  cases isEmpty_or_nonempty α
  · exact Real.iSup_of_isEmpty _
  · exact ciSup_const
#align real.csupr_const_zero Real.ciSup_const_zero

theorem sSup_of_not_bddAbove {s : Set ℝ} (hs : ¬BddAbove s) : sSup s = 0 :=
  dif_neg fun h => hs h.2
#align real.Sup_of_not_bdd_above Real.sSup_of_not_bddAbove

theorem iSup_of_not_bddAbove {α : Sort*} {f : α → ℝ} (hf : ¬BddAbove (Set.range f)) :
    ⨆ i, f i = 0 :=
  sSup_of_not_bddAbove hf
#align real.supr_of_not_bdd_above Real.iSup_of_not_bddAbove

theorem sSup_univ : sSup (@Set.univ ℝ) = 0 := Real.sSup_of_not_bddAbove not_bddAbove_univ
#align real.Sup_univ Real.sSup_univ

@[simp]
theorem sInf_empty : sInf (∅ : Set ℝ) = 0 := by simp [sInf_def, sSup_empty]
#align real.Inf_empty Real.sInf_empty

@[simp] nonrec lemma iInf_of_isEmpty {α : Sort*} [IsEmpty α] (f : α → ℝ) : ⨅ i, f i = 0 := by
  rw [iInf_of_isEmpty, sInf_empty]
#align real.cinfi_empty Real.iInf_of_isEmpty

@[simp]
theorem ciInf_const_zero {α : Sort*} : ⨅ _ : α, (0 : ℝ) = 0 := by
  cases isEmpty_or_nonempty α
  · exact Real.iInf_of_isEmpty _
  · exact ciInf_const
#align real.cinfi_const_zero Real.ciInf_const_zero

theorem sInf_of_not_bddBelow {s : Set ℝ} (hs : ¬BddBelow s) : sInf s = 0 :=
  neg_eq_zero.2 <| sSup_of_not_bddAbove <| mt bddAbove_neg.1 hs
#align real.Inf_of_not_bdd_below Real.sInf_of_not_bddBelow

theorem iInf_of_not_bddBelow {α : Sort*} {f : α → ℝ} (hf : ¬BddBelow (Set.range f)) :
    ⨅ i, f i = 0 :=
  sInf_of_not_bddBelow hf
#align real.infi_of_not_bdd_below Real.iInf_of_not_bddBelow

/--
As `0` is the default value for `Real.sSup` of the empty set or sets which are not bounded above, it
suffices to show that `S` is bounded below by `0` to show that `0 ≤ sSup S`.
-/
theorem sSup_nonneg (S : Set ℝ) (hS : ∀ x ∈ S, (0 : ℝ) ≤ x) : 0 ≤ sSup S := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
  · exact sSup_empty.ge
  · apply dite _ (fun h => le_csSup_of_le h hy <| hS y hy) fun h => (sSup_of_not_bddAbove h).ge
#align real.Sup_nonneg Real.sSup_nonneg

/--
As `0` is the default value for `Real.sSup` of the empty set or sets which are not bounded above, it
suffices to show that `f i` is nonnegative to show that `0 ≤ ⨆ i, f i`.
-/
protected theorem iSup_nonneg {ι : Sort*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : 0 ≤ ⨆ i, f i :=
  sSup_nonneg _ <| Set.forall_mem_range.2 hf
#align real.supr_nonneg Real.iSup_nonneg

/--
As `0` is the default value for `Real.sSup` of the empty set or sets which are not bounded above, it
suffices to show that all elements of `S` are bounded by a nonnegative number to show that `sSup S`
is bounded by this number.
-/
protected theorem sSup_le {S : Set ℝ} {a : ℝ} (hS : ∀ x ∈ S, x ≤ a) (ha : 0 ≤ a) : sSup S ≤ a := by
  rcases S.eq_empty_or_nonempty with (rfl | hS₂)
  exacts [sSup_empty.trans_le ha, csSup_le hS₂ hS]
#align real.Sup_le Real.sSup_le

protected theorem iSup_le {ι : Sort*} {f : ι → ℝ} {a : ℝ} (hS : ∀ i, f i ≤ a) (ha : 0 ≤ a) :
    ⨆ i, f i ≤ a :=
  Real.sSup_le (Set.forall_mem_range.2 hS) ha
#align real.supr_le Real.iSup_le

/-- As `0` is the default value for `Real.sSup` of the empty set, it suffices to show that `S` is
bounded above by `0` to show that `sSup S ≤ 0`.
-/
theorem sSup_nonpos (S : Set ℝ) (hS : ∀ x ∈ S, x ≤ (0 : ℝ)) : sSup S ≤ 0 :=
  Real.sSup_le hS le_rfl
#align real.Sup_nonpos Real.sSup_nonpos

/-- As `0` is the default value for `Real.sInf` of the empty set, it suffices to show that `S` is
bounded below by `0` to show that `0 ≤ sInf S`.
-/
theorem sInf_nonneg (S : Set ℝ) (hS : ∀ x ∈ S, (0 : ℝ) ≤ x) : 0 ≤ sInf S := by
  rcases S.eq_empty_or_nonempty with (rfl | hS₂)
  exacts [sInf_empty.ge, le_csInf hS₂ hS]
#align real.Inf_nonneg Real.sInf_nonneg

/-- As `0` is the default value for `Real.sInf` of the empty set, it suffices to show that `f i` is
bounded below by `0` to show that `0 ≤ iInf f`.
-/
theorem iInf_nonneg {ι} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : 0 ≤ iInf f :=
  sInf_nonneg _ <| Set.forall_mem_range.2 hf

/--
As `0` is the default value for `Real.sInf` of the empty set or sets which are not bounded below, it
suffices to show that `S` is bounded above by `0` to show that `sInf S ≤ 0`.
-/
theorem sInf_nonpos (S : Set ℝ) (hS : ∀ x ∈ S, x ≤ (0 : ℝ)) : sInf S ≤ 0 := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
  · exact sInf_empty.le
  · apply dite _ (fun h => csInf_le_of_le h hy <| hS y hy) fun h => (sInf_of_not_bddBelow h).le
#align real.Inf_nonpos Real.sInf_nonpos

theorem sInf_le_sSup (s : Set ℝ) (h₁ : BddBelow s) (h₂ : BddAbove s) : sInf s ≤ sSup s := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · rw [sInf_empty, sSup_empty]
  · exact csInf_le_csSup h₁ h₂ hne
#align real.Inf_le_Sup Real.sInf_le_sSup

theorem cauSeq_converges (f : CauSeq ℝ abs) : ∃ x, f ≈ const abs x := by
  let S := { x : ℝ | const abs x < f }
  have lb : ∃ x, x ∈ S := exists_lt f
  have ub' : ∀ x, f < const abs x → ∀ y ∈ S, y ≤ x := fun x h y yS =>
    le_of_lt <| const_lt.1 <| CauSeq.lt_trans yS h
  have ub : ∃ x, ∀ y ∈ S, y ≤ x := (exists_gt f).imp ub'
  refine ⟨sSup S, ((lt_total _ _).resolve_left fun h => ?_).resolve_right fun h => ?_⟩
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine (csSup_le lb (ub' _ ?_)).not_lt (sub_lt_self _ (half_pos ε0))
    refine ⟨_, half_pos ε0, i, fun j ij => ?_⟩
    rw [sub_apply, const_apply, sub_right_comm, le_sub_iff_add_le, add_halves]
    exact ih _ ij
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine (le_csSup ub ?_).not_lt ((lt_add_iff_pos_left _).2 (half_pos ε0))
    refine ⟨_, half_pos ε0, i, fun j ij => ?_⟩
    rw [sub_apply, const_apply, add_comm, ← sub_sub, le_sub_iff_add_le, add_halves]
    exact ih _ ij
#align real.cau_seq_converges Real.cauSeq_converges

instance : CauSeq.IsComplete ℝ abs :=
  ⟨cauSeq_converges⟩

open Set

theorem iInf_Ioi_eq_iInf_rat_gt {f : ℝ → ℝ} (x : ℝ) (hf : BddBelow (f '' Ioi x))
    (hf_mono : Monotone f) : ⨅ r : Ioi x, f r = ⨅ q : { q' : ℚ // x < q' }, f q := by
  refine le_antisymm ?_ ?_
  · have : Nonempty { r' : ℚ // x < ↑r' } := by
      obtain ⟨r, hrx⟩ := exists_rat_gt x
      exact ⟨⟨r, hrx⟩⟩
    refine le_ciInf fun r => ?_
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop
    refine ciInf_set_le hf (hxy.trans ?_)
    exact_mod_cast hyr
  · refine le_ciInf fun q => ?_
    have hq := q.prop
    rw [mem_Ioi] at hq
    obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq
    refine (ciInf_le ?_ ?_).trans ?_
    · refine ⟨hf.some, fun z => ?_⟩
      rintro ⟨u, rfl⟩
      suffices hfu : f u ∈ f '' Ioi x from hf.choose_spec hfu
      exact ⟨u, u.prop, rfl⟩
    · exact ⟨y, hxy⟩
    · refine hf_mono (le_trans ?_ hyq.le)
      norm_cast
#align infi_Ioi_eq_infi_rat_gt Real.iInf_Ioi_eq_iInf_rat_gt

theorem not_bddAbove_coe : ¬ (BddAbove <| range (fun (x : ℚ) ↦ (x : ℝ))) := by
  dsimp only [BddAbove, upperBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_gt _

theorem not_bddBelow_coe : ¬ (BddBelow <| range (fun (x : ℚ) ↦ (x : ℝ))) := by
  dsimp only [BddBelow, lowerBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_lt _

theorem iUnion_Iic_rat : ⋃ r : ℚ, Iic (r : ℝ) = univ := by
  exact iUnion_Iic_of_not_bddAbove_range not_bddAbove_coe
#align real.Union_Iic_rat Real.iUnion_Iic_rat

theorem iInter_Iic_rat : ⋂ r : ℚ, Iic (r : ℝ) = ∅ := by
  exact iInter_Iic_eq_empty_iff.mpr not_bddBelow_coe
#align real.Inter_Iic_rat Real.iInter_Iic_rat

end Real
