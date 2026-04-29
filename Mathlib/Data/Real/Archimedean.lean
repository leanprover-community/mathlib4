/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Disjoint

import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Data.Int.LeastGreatest

import all Mathlib.Data.Real.Basic

/-!
# The real numbers are an Archimedean floor ring, and a conditionally complete linear order.

-/

public section

assert_not_exists Finset

open scoped Pointwise
open CauSeq

namespace Real
variable {ι : Sort*} {f : ι → ℝ} {s : Set ℝ} {a : ℝ}

instance instArchimedean : Archimedean ℝ :=
  archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, _, H⟩ := f.bounded' 0
      ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 <| le_of_lt (abs_lt.1 (H i)).2⟩⟩

noncomputable instance : FloorRing ℝ :=
  Archimedean.floorRing _

private theorem isCauSeq_iff_lift {f : ℕ → ℚ} :
   IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : ℝ) where
  mp H ε ε0 :=
    let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => by dsimp; exact lt_trans (mod_cast hi _ ij) δε
  mpr H ε ε0 :=
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij => by dsimp at hi; exact mod_cast hi _ ij

private theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| < ε) :
    ∃ h', Real.mk ⟨f, h'⟩ = x :=
  ⟨isCauSeq_iff_lift.2 (CauSeq.of_near _ (const abs x) h),
    sub_eq_zero.1 <|
      abs_eq_zero.1 <|
        (eq_of_le_of_forall_lt_imp_le_of_dense (abs_nonneg _)) fun _ε ε0 =>
          mk_near_of_forall_near <| (h _ ε0).imp fun _i h j ij => le_of_lt (h j ij)⟩

@[deprecated _root_.exists_floor (since := "2026-01-29")]
theorem exists_floor (x : ℝ) : ∃ ub : ℤ, (ub : ℝ) ≤ x ∧ ∀ z : ℤ, (z : ℝ) ≤ x → z ≤ ub :=
  ⟨⌊x⌋, Int.floor_le x, fun _ ↦ Int.le_floor.mpr⟩

theorem exists_isLUB (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ x, IsLUB s x := by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ s, (m : ℝ) ≤ y * d } := by
    obtain ⟨k, hk⟩ := exists_int_gt U
    refine fun d => ⟨k * d, fun z h => ?_⟩
    rcases h with ⟨y, yS, hy⟩
    refine Int.cast_le.1 (hy.trans ?_)
    push_cast
    gcongr
    exact (hU yS).trans hk.le
  choose f hf using fun d : ℕ =>
    Int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, Int.floor_le _⟩
  have hf₁ : ∀ n > 0, ∃ y ∈ s, ((f n / n : ℚ) : ℝ) ≤ y := fun n n0 =>
    let ⟨y, yS, hy⟩ := (hf n).1
    ⟨y, yS, by simpa using (div_le_iff₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _)).2 hy⟩
  have hf₂ : ∀ n > 0, ∀ y ∈ s, (y - ((n : ℕ) : ℝ)⁻¹) < (f n / n : ℚ) := by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, gt_iff_lt]
    rwa [lt_div_iff₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _), sub_mul, inv_mul_cancel₀]
    exact (Nat.cast_pos.2 n0).ne'
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
    refine lt_of_lt_of_le ((Rat.cast_lt (K := ℝ)).1 ?_) ((inv_le_comm₀ ε0 (Nat.cast_pos.2 k0)).1 ik)
    simpa using sub_lt_iff_lt_add'.2 (lt_of_le_of_lt hy <| sub_lt_iff_lt_add.1 <| hf₂ _ k0 _ yS)
  let g : CauSeq ℚ abs := ⟨fun n => f n / n, hg⟩
  refine ⟨mk g, ⟨fun x xS => ?_, fun y h => ?_⟩⟩
  · refine le_of_forall_lt_imp_le_of_dense fun z xz => ?_
    obtain ⟨K, hK⟩ := exists_nat_gt (x - z)⁻¹
    refine le_mk_of_forall_le ⟨K, fun n nK => ?_⟩
    replace xz := sub_pos.2 xz
    replace hK := hK.le.trans (Nat.cast_le.2 nK)
    have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    refine le_trans ?_ (hf₂ _ n0 _ xS).le
    rwa [le_sub_comm, inv_le_comm₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _) xz]
  · exact
      mk_le_of_forall_le
        ⟨1, fun n n1 =>
          let ⟨x, xS, hx⟩ := hf₁ _ n1
          le_trans hx (h xS)⟩

/-- A nonempty, bounded below set of real numbers has a greatest lower bound. -/
theorem exists_isGLB (hne : s.Nonempty) (hbdd : BddBelow s) : ∃ x, IsGLB s x := by
  have hne' : (-s).Nonempty := Set.nonempty_neg.mpr hne
  have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hbdd
  use -Classical.choose (Real.exists_isLUB hne' hbdd')
  rw [← isLUB_neg]
  exact Classical.choose_spec (Real.exists_isLUB hne' hbdd')

open scoped Classical in
noncomputable instance : SupSet ℝ :=
  ⟨fun s => if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0⟩

open scoped Classical in
theorem sSup_def (s : Set ℝ) :
    sSup s = if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0 :=
  rfl

protected theorem isLUB_sSup (h₁ : s.Nonempty) (h₂ : BddAbove s) : IsLUB s (sSup s) := by
  simp only [sSup_def, dif_pos (And.intro h₁ h₂)]
  apply Classical.choose_spec

noncomputable instance : InfSet ℝ :=
  ⟨fun s => -sSup (-s)⟩

theorem sInf_def (s : Set ℝ) : sInf s = -sSup (-s) := rfl

protected theorem isGLB_sInf (h₁ : s.Nonempty) (h₂ : BddBelow s) : IsGLB s (sInf s) := by
  rw [sInf_def, ← isLUB_neg', neg_neg]
  exact Real.isLUB_sSup h₁.neg h₂.neg

noncomputable instance : ConditionallyCompleteLinearOrder ℝ where
  __ := Real.linearOrder
  __ := Real.lattice
  isLUB_csSup _ := Real.isLUB_sSup
  isGLB_csInf _ := Real.isGLB_sInf
  csSup_of_not_bddAbove s hs := by simp [hs, sSup_def]
  csInf_of_not_bddBelow s hs := by simp [hs, sInf_def, sSup_def]

theorem lt_sInf_add_pos (h : s.Nonempty) {ε : ℝ} (hε : 0 < ε) : ∃ a ∈ s, a < sInf s + ε :=
  exists_lt_of_csInf_lt h <| lt_add_of_pos_right _ hε

theorem add_neg_lt_sSup (h : s.Nonempty) {ε : ℝ} (hε : ε < 0) : ∃ a ∈ s, sSup s + ε < a :=
  exists_lt_of_lt_csSup h <| add_lt_iff_neg_left.2 hε

theorem sInf_le_iff (h : BddBelow s) (h' : s.Nonempty) :
    sInf s ≤ a ↔ ∀ ε, 0 < ε → ∃ x ∈ s, x < a + ε := by
  rw [le_iff_forall_pos_lt_add]
  constructor <;> intro H ε ε_pos
  · exact exists_lt_of_csInf_lt h' (H ε ε_pos)
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    exact csInf_lt_of_lt h x_in hx

theorem le_sSup_iff (h : BddAbove s) (h' : s.Nonempty) :
    a ≤ sSup s ↔ ∀ ε, ε < 0 → ∃ x ∈ s, a + ε < x := by
  rw [le_iff_forall_pos_lt_add]
  refine ⟨fun H ε ε_neg => ?_, fun H ε ε_pos => ?_⟩
  · exact exists_lt_of_lt_csSup h' (lt_sub_iff_add_lt.mp
      (by simpa [sub_eq_add_neg] using H _ (neg_pos.mpr ε_neg)))
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    exact sub_lt_iff_lt_add.mp (lt_csSup_of_lt h x_in <| by simpa [sub_eq_add_neg] using hx)

@[simp]
theorem sSup_empty : sSup (∅ : Set ℝ) = 0 :=
  dif_neg <| by simp

theorem sInf_univ : sInf (@Set.univ ℝ) = 0 := by
  simp [sInf_def]

@[simp] lemma iSup_of_isEmpty [IsEmpty ι] (f : ι → ℝ) : ⨆ i, f i = 0 := by
  dsimp [iSup]
  convert Real.sSup_empty
  rw [Set.range_eq_empty_iff]
  infer_instance

@[simp]
theorem iSup_const_zero : ⨆ _ : ι, (0 : ℝ) = 0 := by
  cases isEmpty_or_nonempty ι
  · exact Real.iSup_of_isEmpty _
  · exact ciSup_const

lemma sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = 0 := dif_neg fun h => hs h.2
lemma iSup_of_not_bddAbove (hf : ¬BddAbove (Set.range f)) : ⨆ i, f i = 0 := sSup_of_not_bddAbove hf

theorem sSup_univ : sSup (@Set.univ ℝ) = 0 := Real.sSup_of_not_bddAbove not_bddAbove_univ

@[simp]
theorem sInf_empty : sInf (∅ : Set ℝ) = 0 := by simp [sInf_def, sSup_empty]

@[simp] nonrec lemma iInf_of_isEmpty [IsEmpty ι] (f : ι → ℝ) : ⨅ i, f i = 0 := by
  rw [iInf_of_isEmpty, sInf_empty]

@[simp]
theorem iInf_const_zero : ⨅ _ : ι, (0 : ℝ) = 0 := by
  cases isEmpty_or_nonempty ι
  · exact Real.iInf_of_isEmpty _
  · exact ciInf_const

theorem sInf_of_not_bddBelow (hs : ¬BddBelow s) : sInf s = 0 :=
  neg_eq_zero.2 <| sSup_of_not_bddAbove <| mt bddAbove_neg.1 hs

theorem iInf_of_not_bddBelow (hf : ¬BddBelow (Set.range f)) : ⨅ i, f i = 0 :=
  sInf_of_not_bddBelow hf

@[simp]
theorem sSup_neg (s : Set ℝ) : sSup (-s) = -sInf s := by
  obtain rfl | hn := s.eq_empty_or_nonempty; · simp
  by_cases hb : BddBelow s
  · rw [csSup_neg hn hb]
  · rw [csInf_of_not_bddBelow hb, Real.sInf_empty, csSup_of_not_bddAbove (bddAbove_neg.not.2 hb),
      Real.sSup_empty, neg_zero]

@[simp]
theorem sInf_neg (s : Set ℝ) : sInf (-s) = -sSup s := by
  rw [← neg_eq_iff_eq_neg, ← Real.sSup_neg, neg_neg]

/-- As `sSup s = 0` when `s` is an empty set of reals, it suffices to show that all elements of `s`
are at most some nonnegative number `a` to show that `sSup s ≤ a`.

See also `csSup_le`. -/
protected lemma sSup_le (hs : ∀ x ∈ s, x ≤ a) (ha : 0 ≤ a) : sSup s ≤ a := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  exacts [sSup_empty.trans_le ha, csSup_le hs' hs]

/-- As `⨆ i, f i = 0` when the domain of the real-valued function `f` is empty, it suffices to show
that all values of `f` are at most some nonnegative number `a` to show that `⨆ i, f i ≤ a`.

See also `ciSup_le`. -/
protected lemma iSup_le (hf : ∀ i, f i ≤ a) (ha : 0 ≤ a) : ⨆ i, f i ≤ a :=
  Real.sSup_le (Set.forall_mem_range.2 hf) ha

/-- As `sInf s = 0` when `s` is an empty set of reals, it suffices to show that all elements of `s`
are at least some nonpositive number `a` to show that `a ≤ sInf s`.

See also `le_csInf`. -/
protected lemma le_sInf (hs : ∀ x ∈ s, a ≤ x) (ha : a ≤ 0) : a ≤ sInf s := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  exacts [ha.trans_eq sInf_empty.symm, le_csInf hs' hs]

/-- As `⨅ i, f i = 0` when the domain of the real-valued function `f` is empty, it suffices to show
that all values of `f` are at least some nonpositive number `a` to show that `a ≤ ⨅ i, f i`.

See also `le_ciInf`. -/
protected lemma le_iInf (hf : ∀ i, a ≤ f i) (ha : a ≤ 0) : a ≤ ⨅ i, f i :=
  Real.le_sInf (Set.forall_mem_range.2 hf) ha

/-- As `sSup s = 0` when `s` is an empty set of reals, it suffices to show that all elements of `s`
are nonpositive to show that `sSup s ≤ 0`. -/
lemma sSup_nonpos (hs : ∀ x ∈ s, x ≤ 0) : sSup s ≤ 0 := Real.sSup_le hs le_rfl

/-- As `⨆ i, f i = 0` when the domain of the real-valued function `f` is empty,
it suffices to show that all values of `f` are nonpositive to show that `⨆ i, f i ≤ 0`. -/
lemma iSup_nonpos (hf : ∀ i, f i ≤ 0) : ⨆ i, f i ≤ 0 := Real.iSup_le hf le_rfl

/-- As `sInf s = 0` when `s` is an empty set of reals, it suffices to show that all elements of `s`
are nonnegative to show that `0 ≤ sInf s`. -/
lemma sInf_nonneg (hs : ∀ x ∈ s, 0 ≤ x) : 0 ≤ sInf s := Real.le_sInf hs le_rfl

/-- As `⨅ i, f i = 0` when the domain of the real-valued function `f` is empty,
it suffices to show that all values of `f` are nonnegative to show that `0 ≤ ⨅ i, f i`. -/
lemma iInf_nonneg (hf : ∀ i, 0 ≤ f i) : 0 ≤ iInf f := Real.le_iInf hf le_rfl

/-- As `sSup s = 0` when `s` is a set of reals that's unbounded above, it suffices to show that `s`
contains a nonnegative element to show that `0 ≤ sSup s`. -/
lemma sSup_nonneg' (hs : ∃ x ∈ s, 0 ≤ x) : 0 ≤ sSup s := by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  exact dite _ (fun h ↦ le_csSup_of_le h hxs hx) fun h ↦ (sSup_of_not_bddAbove h).ge

/-- As `⨆ i, f i = 0` when the real-valued function `f` is unbounded above,
it suffices to show that `f` takes a nonnegative value to show that `0 ≤ ⨆ i, f i`. -/
lemma iSup_nonneg' (hf : ∃ i, 0 ≤ f i) : 0 ≤ ⨆ i, f i := sSup_nonneg' <| Set.exists_range_iff.2 hf

/-- As `sInf s = 0` when `s` is a set of reals that's unbounded below, it suffices to show that `s`
contains a nonpositive element to show that `sInf s ≤ 0`. -/
lemma sInf_nonpos' (hs : ∃ x ∈ s, x ≤ 0) : sInf s ≤ 0 := by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  exact dite _ (fun h ↦ csInf_le_of_le h hxs hx) fun h ↦ (sInf_of_not_bddBelow h).le

/-- As `⨅ i, f i = 0` when the real-valued function `f` is unbounded below,
it suffices to show that `f` takes a nonpositive value to show that `0 ≤ ⨅ i, f i`. -/
lemma iInf_nonpos' (hf : ∃ i, f i ≤ 0) : ⨅ i, f i ≤ 0 := sInf_nonpos' <| Set.exists_range_iff.2 hf

/-- As `sSup s = 0` when `s` is a set of reals that's either empty or unbounded above,
it suffices to show that all elements of `s` are nonnegative to show that `0 ≤ sSup s`. -/
lemma sSup_nonneg (hs : ∀ x ∈ s, 0 ≤ x) : 0 ≤ sSup s := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact sSup_empty.ge
  · exact sSup_nonneg' ⟨x, hx, hs _ hx⟩

/-- As `⨆ i, f i = 0` when the domain of the real-valued function `f` is empty or unbounded above,
it suffices to show that all values of `f` are nonnegative to show that `0 ≤ ⨆ i, f i`. -/
lemma iSup_nonneg (hf : ∀ i, 0 ≤ f i) : 0 ≤ ⨆ i, f i := sSup_nonneg <| Set.forall_mem_range.2 hf

lemma iSup_nonneg_of_nonnegHomClass {ι F α : Type*} [FunLike F α ℝ] [NonnegHomClass F α ℝ] (f : F)
    (g : ι → α) :
    0 ≤ ⨆ i, f (g i) :=
  iSup_nonneg (fun i ↦ apply_nonneg f (g i))

/-- As `sInf s = 0` when `s` is a set of reals that's either empty or unbounded below,
it suffices to show that all elements of `s` are nonpositive to show that `sInf s ≤ 0`. -/
lemma sInf_nonpos (hs : ∀ x ∈ s, x ≤ 0) : sInf s ≤ 0 := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact sInf_empty.le
  · exact sInf_nonpos' ⟨x, hx, hs _ hx⟩

/-- As `⨅ i, f i = 0` when the domain of the real-valued function `f` is empty or unbounded below,
it suffices to show that all values of `f` are nonpositive to show that `0 ≤ ⨅ i, f i`. -/
lemma iInf_nonpos (hf : ∀ i, f i ≤ 0) : ⨅ i, f i ≤ 0 := sInf_nonpos <| Set.forall_mem_range.2 hf

theorem sInf_le_sSup (s : Set ℝ) (h₁ : BddBelow s) (h₂ : BddAbove s) : sInf s ≤ sSup s := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · rw [sInf_empty, sSup_empty]
  · exact csInf_le_csSup hne h₁ h₂

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

theorem iInter_Iic_rat : ⋂ r : ℚ, Iic (r : ℝ) = ∅ := by
  exact iInter_Iic_eq_empty_iff.mpr not_bddBelow_coe

/-- Exponentiation is eventually larger than linear growth. -/
lemma exists_natCast_add_one_lt_pow_of_one_lt (ha : 1 < a) : ∃ m : ℕ, (m + 1 : ℝ) < a ^ m := by
  obtain ⟨k, posk, hk⟩ : ∃ k : ℕ, 0 < k ∧ 1 / k + 1 < a := by
    contrapose! ha
    refine le_of_forall_lt_rat_imp_le ?_
    intro q hq
    refine (ha q.den (by positivity)).trans ?_
    rw [← le_sub_iff_add_le, div_le_iff₀ (by positivity), sub_mul, one_mul]
    norm_cast at hq ⊢
    rw [← q.num_div_den, one_lt_div (by positivity)] at hq
    rw [q.mul_den_eq_num]
    norm_cast at hq ⊢
    lia
  use 2 * k ^ 2
  calc
    ((2 * k ^ 2 : ℕ) + 1 : ℝ) ≤ 2 ^ (2 * k) := mod_cast Nat.two_mul_sq_add_one_le_two_pow_two_mul _
    _ = (1 / k * k + 1 : ℝ) ^ (2 * k) := by simp [posk.ne']; norm_num
    _ ≤ ((1 / k + 1) ^ k : ℝ) ^ (2 * k) := by gcongr; exact mul_add_one_le_add_one_pow (by simp) _
    _ = (1 / k + 1 : ℝ) ^ (2 * k ^ 2) := by rw [← pow_mul, mul_left_comm, sq]
    _ < a ^ (2 * k ^ 2) := by gcongr

lemma exists_nat_pos_inv_lt {b : ℝ} (hb : 0 < b) :
    ∃ (n : ℕ), 0 < n ∧ (n : ℝ)⁻¹ < b := by
  refine (exists_nat_gt b⁻¹).imp fun k hk ↦ ?_
  have := (inv_pos_of_pos hb).trans hk
  refine ⟨Nat.cast_pos.mp this, ?_⟩
  rwa [inv_lt_comm₀ this hb]

end Real
