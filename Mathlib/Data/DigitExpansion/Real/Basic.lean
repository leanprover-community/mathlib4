/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.DigitExpansion.Add
import Mathlib.GroupTheory.Subgroup.Basic

/-!
# Defining reals without the use of rationals

Constructing the actual subgroup of the reals.

* [Defining reals without the use of rationals][debruijn1976]

-/

open Order

-- TODO
lemma Fin.pos_of_ne_zero {n : ℕ} {a : Fin (n + 1)} (h : a ≠ 0) :
    0 < a :=
  Nat.pos_of_ne_zero (Fin.val_ne_of_ne h)

-- TODO
theorem pred_min {Z : Type*} [LinearOrder Z] [PredOrder Z] (x y : Z) :
    pred (min x y) = min (pred x) (pred y) := by
  cases' le_total x y with h h
  · rw [min_eq_left h, min_eq_left]
    simp [h]
  · rw [min_eq_right h, min_eq_right]
    simp [h]

theorem pred_max {Z : Type*} [LinearOrder Z] [PredOrder Z] (x y : Z) :
    pred (max x y) = max (pred x) (pred y) := by
  cases' le_total x y with h h
  · rw [max_eq_right h, max_eq_right]
    simp [h]
  · rw [max_eq_left h, max_eq_left]
    simp [h]

theorem succ_min {Z : Type*} [LinearOrder Z] [SuccOrder Z] (x y : Z) :
    succ (min x y) = min (succ x) (succ y) := by
  cases' le_total x y with h h
  · rw [min_eq_left h, min_eq_left]
    simp [h]
  · rw [min_eq_right h, min_eq_right]
    simp [h]

theorem succ_max {Z : Type*} [LinearOrder Z] [SuccOrder Z] (x y : Z) :
    succ (max x y) = max (succ x) (succ y) := by
  cases' le_total x y with h h
  · rw [max_eq_right h, max_eq_right]
    simp [h]
  · rw [max_eq_left h, max_eq_left]
    simp [h]

variable (Z : Type*) [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] (b : ℕ) [hb : NeZero b]
    [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]

namespace DigitExpansion

/-- A sequence is called real if it is either negative or zero or positive.
-/
def real : AddSubgroup (DigitExpansion Z b)
    where
  carrier := {f | f.Positive ∨ f.Negative ∨ f = 0}
  add_mem' := by
    simp_rw [← sub_neg_eq_add]
    simp only [Set.mem_setOf_eq]
    rintro f g (hf | hf | rfl) (hg | hg | rfl)
    · exact Or.inl (hf.sub_negative hg.neg_negative)
    · rcases eq_or_ne f (-g) with (rfl | hne)
      · simp
      rw [← or_assoc]
      exact Or.inl ((hf.sub_positive hg.neg_positive hne).imp And.left fun H => H.left)
    · simp [hf]
    · rcases eq_or_ne f (-g) with (rfl | hne)
      · simp
      rw [← or_assoc]
      exact Or.inl ((hf.sub_negative hg.neg_negative hne).imp And.left fun H => H.left)
    · exact Or.inr (Or.inl (hf.sub_positive hg.neg_positive))
    · simp [hf]
    · simp [hg]
    · simp [hg]
    · simp
  zero_mem' := by simp
  neg_mem' := by
    simp only [Set.mem_setOf_eq]
    rintro f (hf | hf | rfl)
    · exact Or.inr (Or.inl hf.neg_negative)
    · exact Or.inl hf.neg_positive
    · simp

instance : LT (real Z b) :=
  ⟨fun f g => (g - f : DigitExpansion Z b).Positive⟩

variable {Z} {b}
variable {f g : DigitExpansion Z b}

protected theorem real.lt_def {f g : real Z b} :
    f < g ↔ (g - f : DigitExpansion Z b).Positive :=
  Iff.rfl

lemma real.eq_zero_of_isEmpty [IsEmpty Z] (f : real Z b) : f = 0 := by
  rcases f with ⟨_, hf|hf|rfl⟩
  · exact absurd hf (not_positive_of_isEmpty _)
  · exact absurd hf (not_negative_of_isEmpty _)
  · rfl

variable (b) (Z)

instance real.instPartialOrder : PartialOrder (real Z b)
    where
  le f g := f = g ∨ f < g
  lt := (· < ·)
  le_refl _ := Or.inl rfl
  le_trans f g h := by
    rintro (rfl | hfg) (rfl | hgh)
    · exact Or.inl rfl
    · exact Or.inr hgh
    · exact Or.inr hfg
    · refine' Or.inr _
      rw [real.lt_def] at hfg hgh ⊢
      rw [← sub_sub_sub_cancel_right _ _ (g : DigitExpansion Z b),
          ← neg_sub (g : DigitExpansion Z b) f]
      exact hgh.sub_negative hfg.neg_negative
  lt_iff_le_not_le f g := by
    constructor
    · intro h
      refine' ⟨Or.inr h, _⟩
      rintro (rfl | H) <;> rw [real.lt_def] at *
      · refine' (_ : (g : DigitExpansion Z b) ≠ g) rfl
        rw [Ne.def, ← sub_eq_zero]
        exact h.left
      · rw [← neg_sub] at H
        exact h.neg_negative.not_positive H
    · rintro ⟨rfl | h, H⟩
      · contrapose! H
        exact Or.inl rfl
      · exact h
  le_antisymm f g := by
    rintro (rfl | hfg) (hgf | hgf)
    · rfl
    · rfl
    · exact hgf.symm
    · rw [real.lt_def] at hfg hgf
      rw [← neg_sub] at hgf
      exact absurd hgf hfg.neg_negative.not_positive

protected theorem real.le_def {f g : real Z b} :
    f ≤ g ↔ f = g ∨ (g - f : DigitExpansion Z b).Positive :=
  Iff.rfl

noncomputable instance real.instLinearOrder :
    LinearOrder (real Z b) :=
  { real.instPartialOrder _ _ with
    le_total := fun f g => by
      rcases hfg : f - g with ⟨h, H | H | rfl⟩ <;>
        simp only [Subtype.ext_iff, AddSubgroup.coe_sub, Subtype.coe_mk] at hfg
      · subst hfg
        exact Or.inr (Or.inr H)
      · subst hfg
        replace H := H.neg_positive
        rw [neg_sub] at H
        exact Or.inl (Or.inr H)
      · rw [sub_eq_zero, ← Subtype.ext_iff] at hfg
        subst hfg
        exact Or.inl le_rfl
    decidableLE := Classical.decRel _ }

instance : CovariantClass (real Z b) (real Z b) (· + ·) (· < ·) :=
  ⟨fun _ _ _ => by simp_rw [real.lt_def]; simp⟩

instance : CovariantClass (real Z b) (real Z b)
    (Function.swap (· + ·)) (· < ·) :=
  ⟨fun _ _ _ => by simp_rw [real.lt_def]; simp⟩

instance : CovariantClass (real Z b) (real Z b) (· + ·) (· ≤ ·) :=
  ⟨fun _ _ _ => by simp_rw [real.le_def]; simp⟩

instance : CovariantClass (real Z b) (real Z b)
    (Function.swap (· + ·)) (· ≤ ·) :=
  ⟨fun _ _ _ => by simp_rw [real.le_def]; simp⟩

variable {Z} {b}

theorem real.positive_iff {f : real Z b} :
    (f : DigitExpansion Z b).Positive ↔ 0 < f := by
  simp [real.lt_def]

theorem real.negative_iff {f : real Z b} :
    (f : DigitExpansion Z b).Negative ↔ f < 0 := by
  simp only [real.lt_def, AddSubgroup.coe_zero, zero_sub]
  refine' ⟨Negative.neg_positive, fun h => _⟩
  rw [← neg_neg (f : DigitExpansion Z b)]
  exact h.neg_negative

namespace real

section single

/-- An auxiliary function defining a sequence that has the specified digit at the specified
position, and 0 elsewhere. Compare to `Pi.single`. Not included in the de Bruijn paper. -/
def single (z : Z) (n : Fin (b + 1)) : real Z b :=
  ⟨DigitExpansion.single z n, by
    rcases eq_or_ne n 0 with rfl|hn
    · simp only [single_zero]
      exact Or.inr (Or.inr rfl)
    · exact Or.inl (single_positive_of_ne_zero _ hn)⟩

@[simp]
lemma val_single (z : Z) (n : Fin (b + 1)) :
    (single z n : DigitExpansion Z b) = DigitExpansion.single z n := rfl

@[simp]
lemma single_zero (z : Z) :
    (single z (0 : Fin (b + 1))) = 0 := Subtype.ext (DigitExpansion.single_zero z)

lemma single_injective (z : Z) :
    Function.Injective (single (b := b) z) := by
  intro n m h
  simp only [Subtype.ext_iff, val_single, FunLike.ext_iff, ne_eq] at h
  simpa using h z

lemma single_injective_left_of_ne_zero {n : Fin (b + 1)} (hn : n ≠ 0) :
    Function.Injective (single (Z := Z) · n) := by
  intro z x h
  simp only [Subtype.ext_iff, val_single, FunLike.ext_iff, ne_eq] at h
  specialize h z
  by_contra H
  simp [hn, Ne.symm H] at h z

lemma single_strict_mono (z : Z) {n m : Fin (b + 1)} (h : n < m) :
    single z n < single z m := by
  refine ⟨?_, z, fun y hy => ?_⟩
  · rw [FunLike.ne_iff]
    refine ⟨z, ?_⟩
    simp [DigitExpansion.sub_def, sub_eq_zero, h.ne']
  · rw [DigitExpansion.sub_def, difcar_eq_zero_iff.mpr]
    · simp [hy.ne']
    intro x _ H
    rcases eq_or_ne z x with rfl|h
    · simp [h.not_lt] at H
    · simp [h] at H

lemma single_strictMono (z : Z) :
    StrictMono (single (b := b) z) :=
  fun _ _ => single_strict_mono _

@[simp]
lemma single_lt_right_iff {z : Z} {n m : Fin (b + 1)} :
    single z n < single z m ↔ n < m :=
  (single_strictMono z).lt_iff_lt

lemma single_strict_anti_left_of_ne_zero {z x : Z} {n : Fin (b + 1)} (hn : n ≠ 0) (h : z < x) :
    single x n < single z n := by
  refine ⟨?_, z, fun y hy => ?_⟩
  · rw [FunLike.ne_iff]
    refine ⟨x, ?_⟩
    simp only [val_single, DigitExpansion.sub_def, single_apply_self, zero_apply, ne_eq]
    rw [difcar_eq_zero_iff.mpr, sub_zero, sub_eq_zero]
    · simp [h.ne, hn.symm]
    intro _ hx
    simp [hx.ne]
  · rw [DigitExpansion.sub_def, difcar_eq_zero_iff.mpr]
    · simp [hy.ne', (hy.trans h).ne']
    intro w hw H
    have : x = w
    · contrapose! H
      simp [H]
    subst w
    refine ⟨z, h, hy, ?_⟩
    simp [h.ne', Fin.pos_of_ne_zero hn]

lemma single_strictAnti_left_of_ne_zero {n : Fin (b + 1)} (hn : n ≠ 0) :
    StrictAnti (single (Z := Z) · n) :=
  fun _ _ => single_strict_anti_left_of_ne_zero hn

lemma single_anti_left {z x : Z} (n : Fin (b + 1)) (h : z ≤ x) :
    single x n ≤ single z n := by
  rcases eq_or_ne n 0 with rfl|hn
  · simp
  rcases h.eq_or_lt with rfl|h
  · exact le_rfl
  · exact (single_strictAnti_left_of_ne_zero hn h).le

lemma single_antitone_left (n : (Fin (b + 1))) :
    Antitone (single (Z := Z) · n) :=
  fun _ _ => single_anti_left _

@[simp]
lemma single_lt_left_iff_of_ne_zero {z x : Z} {n : Fin (b + 1)} (hn : n ≠ 0) :
    single z n < single x n ↔ x < z :=
  (single_strictAnti_left_of_ne_zero hn).lt_iff_lt

end single

section cutoff

/-- An auxiliary function that truncates the right-tail of a sequence by setting that tail to
all digit 0. Such truncation preserves order. -/
def cutoff (z : Z) (f : real Z b) : real Z b :=
  ⟨DigitExpansion.cutoff z (f : DigitExpansion Z b), by
    rcases f with ⟨f, hf | hf | rfl⟩ <;> rw [Subtype.coe_mk]
    · obtain ⟨x, xpos, hx⟩ := hf.exists_least_pos
      cases' lt_or_le z x with h h
      · refine' Or.inr (Or.inr _)
        ext y : 1
        cases' lt_or_le z y with hy hy
        · rw [cutoff_apply_lt _ _ _ hy, zero_apply]
        · rw [cutoff_apply_le _ _ _ hy]
          exact hx _ (h.trans_le' hy)
      · refine' Or.inl ⟨fun H => xpos.ne _, x, fun y hy => _⟩
        · rw [← cutoff_apply_le _ _ _ h, H, zero_apply]
        · rw [cutoff_apply_le _ _ _ (hy.le.trans h), hx _ hy]
    · exact Or.inr (Or.inl (hf.negative_cutoff _))
    · refine' Or.inr (Or.inr _)
      ext x : 1
      cases' lt_or_le z x with h h <;> simp [cutoff_apply_le, cutoff_apply_lt, h]⟩

@[simp]
lemma cutoff_zero (z : Z) : cutoff z (0 : real Z b) = 0 :=
  Subtype.ext (DigitExpansion.cutoff_zero z)

@[simp]
lemma val_cutoff (z : Z) (f : real Z b) :
    (cutoff z f : DigitExpansion Z b) = DigitExpansion.cutoff z f := rfl

@[simp]
lemma cutoff_idem (f : real Z b) (z : Z) : (cutoff z (cutoff z f)) = cutoff z f :=
  Subtype.ext <| DigitExpansion.cutoff_idem _ _

lemma cutoff_mono (z : Z) {f g : real Z b} (hfg : f ≤ g) :
    cutoff z f ≤ cutoff z g := by
  rcases hfg.eq_or_lt with rfl|hfg'
  · simp
  rw [real.lt_def] at hfg'
  refine' or_iff_not_imp_left.mpr _
  intro H
  have hne : g ≠ f := by intro H; refine' hfg'.left _; rw [H, sub_self]
  rw [real.lt_def]
  obtain ⟨f, hf | hf | hf⟩ := f <;>
  obtain ⟨g, hg | hg | hg⟩ := g <;>
  simp only at hfg'
  · refine' ⟨by simpa [Subtype.ext_iff, sub_eq_zero] using Ne.symm H, _⟩
    simp only [val_cutoff]
    obtain ⟨a, ha, ha'⟩ := hfg'.exists_least_pos
    obtain ⟨m, hm'⟩ := hf.right
    obtain ⟨n, hn'⟩ := hg.right
    simp_rw [DigitExpansion.sub_def] at ha ha' ⊢
    refine' ⟨min (min m n) (min z a), _⟩
    simp only [ge_iff_le, le_pred_iff, pred_lt_iff, min_lt_iff, le_min_iff, lt_min_iff, and_imp]
    intros y hym hyn hyz hya
    rw [cutoff_apply_le _ _ _ hyz.le, cutoff_apply_le _ _ _ hyz.le,
        hm' _ hym, hn' _ hyn]
    specialize ha' y hya
    rw [hm' _ hym, hn' _ hyn] at ha'
    simp only [sub_self, zero_sub, neg_eq_zero, difcar_eq_zero_iff, gt_iff_lt] at ha' ⊢
    intro w hyw hw
    have hwz : w ≤ z
    · contrapose! hw
      simp [cutoff_apply_lt _ _ _ hw]
    rw [cutoff_apply_le _ _ _ hwz, cutoff_apply_le _ _ _ hwz] at hw
    obtain ⟨u, hu, hu', hu''⟩ := ha' w hyw hw
    refine' ⟨u, hu, hu', _⟩
    rw [cutoff_apply_le _ _ _ (hu.le.trans hwz), cutoff_apply_le _ _ _ (hu.le.trans hwz)]
    exact hu''
  · exact absurd (hg.sub_positive hf) hfg'.not_negative
  · simp only [hg, zero_sub, gt_iff_lt] at hfg' H ⊢
    exact absurd hf.neg_negative hfg'.not_negative
  · simp only [val_cutoff] at hfg' H ⊢
    refine' ⟨by simpa [Subtype.ext_iff, sub_eq_zero] using Ne.symm H, _⟩
    obtain ⟨a, ha'⟩ := hfg'.right
    obtain ⟨m, hm'⟩ := hf.right
    obtain ⟨n, hn'⟩ := hg.right
    refine' ⟨min (min (pred m) (pred n)) (min z a), _⟩
    simp only [ge_iff_le, le_pred_iff, pred_lt_iff, min_lt_iff, le_min_iff, lt_min_iff, and_imp]
    intros y hym hyn hyz hya
    simp_rw [DigitExpansion.sub_def] at ha' ⊢
    rw [cutoff_apply_le _ _ _ hyz.le, cutoff_apply_le _ _ _ hyz.le,
        hm' _ (hym.trans_le (pred_le _)), hn' _ (hyn.trans_le (pred_le _))]
    specialize ha' y hya
    rw [hm' _ (hym.trans_le (pred_le _)), hn' _ (hyn.trans_le (pred_le _))] at ha'
    simp only [zero_sub, Fin.neg_coe_eq_one, sub_eq_zero, eq_comm (a := (1 : Fin (b + 1))),
      difcar_eq_one_iff, gt_iff_lt] at ha' ⊢
    obtain ⟨u, hu, -, -⟩ := ha'
    refine' ⟨min (min (pred n) (pred m)) (min z u), _, _, _⟩
    · simp [hym, hyn, hya, hyz, hu]
    · rw [cutoff_apply_le _ _ _, cutoff_apply_le _ _ _, hn', hm']
      · simp [Fin.lt_iff_val_lt_val, Nat.pos_of_ne_zero hb.out]
      · simp
      · simp
      · simp
      · simp
    · intro w hw _
      simp only [ge_iff_le, le_pred_iff, pred_lt_iff, le_min_iff, min_le_iff, min_lt_iff,
          lt_min_iff] at hw
      rw [cutoff_apply_le _ _ _ hw.right.left.le, cutoff_apply_le _ _ _ hw.right.left.le,
          hn' _ (hw.left.left.trans_le (pred_le _))]
      simp
  · simp only [val_cutoff]
    refine' ⟨by simpa [Subtype.ext_iff, sub_eq_zero] using Ne.symm H, _⟩
    obtain ⟨a, ha'⟩ := hfg'.right
    obtain ⟨m, hm'⟩ := hf.right
    obtain ⟨n, hn'⟩ := hg.right
    refine' ⟨min (min (pred m) (pred n)) (min z a), _⟩
    simp only [ge_iff_le, le_pred_iff, pred_lt_iff, min_lt_iff, le_min_iff, lt_min_iff, and_imp]
    intros y hym hyn hyz hya
    simp_rw [DigitExpansion.sub_def] at ha' ⊢
    rw [cutoff_apply_le _ _ _ hyz.le, cutoff_apply_le _ _ _ hyz.le,
        hm' _ (hym.trans_le (pred_le _)), hn' _ (hyn.trans_le (pred_le _))]
    specialize ha' y hya
    rw [hm' _ (hym.trans_le (pred_le _)), hn' _ (hyn.trans_le (pred_le _))] at ha'
    simp only [sub_self, zero_sub, neg_eq_zero, difcar_eq_zero_iff, gt_iff_lt] at ha' ⊢
    intro w hyw hw
    have hwz : w ≤ z
    · contrapose! hw
      simp [cutoff_apply_lt _ _ _ hw]
    rw [cutoff_apply_le _ _ _ hwz, cutoff_apply_le _ _ _ hwz] at hw
    obtain ⟨u, hu, hu', hu''⟩ := ha' w hyw hw
    refine' ⟨u, hu, hu', _⟩
    rw [cutoff_apply_le _ _ _ (hu.le.trans hwz), cutoff_apply_le _ _ _ (hu.le.trans hwz)]
    exact hu''
  · simp only [zero_sub, val_cutoff, cutoff_zero, hg]
    simpa using (hf.negative_cutoff z).neg_positive
  · subst hf
    simp only [sub_zero, Subtype.ext_iff, val_cutoff, cutoff_zero] at hfg' H ⊢
    obtain ⟨hne, x, hx⟩ := hg
    refine' ⟨by simpa [Subtype.ext_iff, sub_eq_zero] using Ne.symm H, x, _⟩
    intro y
    simp only [DigitExpansion.cutoff_zero, sub_zero]
    intro hy
    cases' lt_or_le z y with hzy hzy
    · rw [cutoff_apply_lt _ _ _ hzy]
    · rw [cutoff_apply_le _ _ _ hzy]
      exact hx _ hy
  · refine' absurd _ hfg'.not_negative
    simp [hf, hg]
  · simp [hf, hg] at hne

lemma cutoff_monotone (z : Z) : Monotone (cutoff (b := b) z) :=
  fun _ _ => cutoff_mono z

lemma cutoff_mono_left {z z' : Z} (f : real Z b) (h : z ≤ z') :
    cutoff z f ≤ cutoff z' f := by
  rcases h.eq_or_lt with rfl|h
  · simp
  by_cases hf : cutoff z f = 0
  · rw [hf]
    rcases f.prop with hf'|hf'|hf'
    · rw [positive_iff] at hf'
      simpa using cutoff_mono z' hf'.le
    · obtain ⟨-, x, hx'⟩ := hf'
      simp only [Subtype.ext_iff, val_cutoff, ZeroMemClass.coe_zero] at hf
      suffices : DigitExpansion.cutoff (b := b) z f (pred (min z x)) = 0
      · rw [cutoff_apply_le, hx'] at this
        · simp [Fin.ext_iff, hb.out] at this
        · simp [pred_min]
        · simp [pred_min, pred_le]
      simp [hf]
    · simp only [ZeroMemClass.coe_eq_zero] at hf'
      simp [hf']
  have hle : ∀ y, (DigitExpansion.cutoff z f.val) y ≤ (DigitExpansion.cutoff z' f.val) y
  · intro y
    cases' le_or_lt y z with hyz hyz
    · rw [cutoff_apply_le _ _ _ hyz, cutoff_apply_le _ _ _ (hyz.trans h.le)]
    · simp [cutoff_apply_lt _ _ _ hyz]
  by_cases hw : ∃ w ≤ z', z < w ∧ 0 < (f : DigitExpansion Z b) w
  · obtain ⟨w, hwz', hzw, hw⟩ := hw
    refine' le_of_lt ⟨_, pred z, _⟩
    · contrapose! hw
      simp only [val_cutoff] at hw
      have : difcar (DigitExpansion.cutoff z' f) (DigitExpansion.cutoff (b := b) z f) w = 0
      · rw [difcar_eq_zero_iff]
        intro u
        simp [(hle u).not_lt]
      rw [← zero_apply w, ← hw, DigitExpansion.sub_def, cutoff_apply_lt _ _ _ hzw,
          cutoff_apply_le _ _ _ hwz', sub_zero, this]
      simp
    · intros y hy
      simp only [val_cutoff]
      rw [DigitExpansion.sub_def, cutoff_apply_le _ _ _ (hy.le.trans (pred_le _)),
          cutoff_apply_le _ _ _ ((hy.le.trans (pred_le _)).trans h.le), sub_self,
          zero_sub, neg_eq_zero, difcar_eq_zero_iff]
      intro u
      simp [(hle u).not_lt]
  · push_neg at hw
    simp only [Fin.le_zero_iff] at hw
    refine' le_of_eq _
    ext y
    simp only [val_cutoff]
    cases' le_or_lt y z with hyz hyz
    · rw [cutoff_apply_le _ _ _ hyz, cutoff_apply_le _ _ _ (hyz.trans h.le)]
    rw [cutoff_apply_lt _ _ _ hyz]
    cases' le_or_lt y z' with hyz' hyz'
    · rw [cutoff_apply_le _ _ _ hyz', hw _ hyz' hyz]
    · rw [cutoff_apply_lt _ _ _ hyz']

theorem cutoff_cutoff_of_le
    (f : real Z b) {z x : Z} (h : x ≤ z) : cutoff x (cutoff z f) = cutoff x f := by
  ext : 1
  exact DigitExpansion.cutoff_cutoff_of_le (b := b) f h

lemma le_of_forall_cutoff_le_cutoff {f g : real Z b} (h : ∀ z, cutoff z f ≤ cutoff z g) :
    f ≤ g := by
  rw [← not_lt]
  intro H
  obtain ⟨hne, z, hz⟩ := id H
  rw [sub_ne_zero, FunLike.ne_iff] at hne
  obtain ⟨x, hx⟩ := hne
  rw [← cutoff_apply_self f.val, ← val_cutoff, le_antisymm (h _) (cutoff_mono _ H.le),
      val_cutoff, cutoff_apply_self] at hx
  exact hx rfl

theorem exists_exists_isLeast_image_cutoff [Nonempty Z] -- e.g. the case where S = {0}
    (S : Set (real Z b)) (hn : S.Nonempty) (h : BddBelow S) :
    ∃ z x, IsLeast (cutoff z '' S) x := by
  obtain ⟨g, h⟩ := h
  obtain ⟨f, hf⟩ := id hn
  rcases g.prop with (hg|hg|hg)
  · have hgf := h hf
    have hf' : DigitExpansion.Positive (f : DigitExpansion Z b)
    · rw [positive_iff] at hg ⊢
      exact hg.trans_le hgf
    obtain ⟨-, v, hv'⟩ := hf'
    obtain ⟨-, u, hu'⟩ := hg
    have : cutoff (pred (min u v)) f = cutoff (pred (min u v)) g
    · ext y
      simp only [ge_iff_le, val_cutoff]
      cases' le_or_lt y (pred (min u v)) with hy hy
      · rw [cutoff_apply_le _ _ _ hy, cutoff_apply_le _ _ _ hy,
            hv' _ (hy.trans_lt _), hu' _ (hy.trans_lt _)]
        · simp
        · simp
      · rw [cutoff_apply_lt _ _ _ hy, cutoff_apply_lt _ _ _ hy]
    refine' ⟨pred (min u v), cutoff (pred (min u v)) f, ⟨f, hf, rfl⟩, _⟩
    rw [this]
    exact (cutoff_monotone _).mem_lowerBounds_image h
  · by_cases hS : ∃ f ∈ S, DigitExpansion.Negative (f : DigitExpansion Z b)
    · obtain ⟨f, hf, hf'⟩ := hS
      obtain ⟨-, v, hv'⟩ := hf'
      obtain ⟨-, u, hu'⟩ := hg
      have : cutoff (pred (min u v)) f = cutoff (pred (min u v)) g
      · ext y
        simp only [ge_iff_le, val_cutoff]
        cases' le_or_lt y (pred (min u v)) with hy hy
        · rw [cutoff_apply_le _ _ _ hy, cutoff_apply_le _ _ _ hy,
              hv' _ (hy.trans_lt _), hu' _ (hy.trans_lt _)]
          · simp
          · simp
        · rw [cutoff_apply_lt _ _ _ hy, cutoff_apply_lt _ _ _ hy]
      refine' ⟨pred (min u v), cutoff (pred (min u v)) f, ⟨f, hf, rfl⟩, _⟩
      rw [this]
      exact (cutoff_monotone _).mem_lowerBounds_image h
    · replace hS : ∀ f ∈ S, (f : DigitExpansion Z b).Positive ∨ f = 0
      · rintro ⟨f, hf'|hf'|hf'⟩ hf
        · simp [hf']
        · simpa using hS ⟨⟨_, _⟩, hf, hf'⟩
        · simp [hf']
      have h0 : 0 ∈ lowerBounds S
      · intro f hf
        rw [real.le_def]
        rcases (hS f hf) with (hf|rfl) <;> simp [hf]
      specialize hS f hf
      rcases hS with (hf|rfl)
      · obtain ⟨-, v, hv'⟩ := hf
        refine' ⟨pred v, cutoff (pred v) f, ⟨f, hf, rfl⟩, _⟩
        have h0' : cutoff (pred v) f = 0
        · ext y
          simp only [val_cutoff, ZeroMemClass.coe_zero, zero_apply]
          cases' le_or_lt y (pred v) with hy hy
          · rw [cutoff_apply_le _ _ _ hy, hv' _ (hy.trans_lt _)]
            simp
          · rw [cutoff_apply_lt _ _ _ hy,]
        rw [h0']
        rw [← cutoff_zero (pred v)]
        exact (cutoff_monotone _).mem_lowerBounds_image h0
      · obtain ⟨-, x, -⟩ := hg
        refine' ⟨x, cutoff x 0, ⟨0, hf, rfl⟩, _⟩
        exact (cutoff_monotone _).mem_lowerBounds_image h0
  · simp only [ZeroMemClass.coe_eq_zero] at hg
    subst g
    have : ∀ f ∈ S, (f : DigitExpansion Z b).Positive ∨ f = 0
    · intro f hf
      rcases f.prop with hf'|hf'|hf'
      · simp [hf']
      · rw [negative_iff] at hf'
        exact absurd hf' (h hf).not_lt
      · simp only [ZeroMemClass.coe_eq_zero] at hf'
        simp [hf']
    rcases this f hf with hf'|rfl
    · obtain ⟨-, v, hv'⟩ := hf'
      refine' ⟨pred v, cutoff (pred v) f, ⟨f, hf, rfl⟩, _⟩
      have h0' : cutoff (pred v) f = 0
      · ext y
        simp only [val_cutoff, ZeroMemClass.coe_zero, zero_apply]
        cases' le_or_lt y (pred v) with hy hy
        · rw [cutoff_apply_le _ _ _ hy, hv' _ (hy.trans_lt _)]
          simp
        · rw [cutoff_apply_lt _ _ _ hy,]
      rw [h0']
      rw [← cutoff_zero (pred v)]
      exact (cutoff_monotone _).mem_lowerBounds_image h
    · inhabit Z
      refine' ⟨default, cutoff default 0, ⟨0, hf, rfl⟩, _⟩
      exact (cutoff_monotone _).mem_lowerBounds_image h

lemma cutoff_succ_eq_cutoff_add_single (f : real Z b) (u : Z) :
    cutoff (succ u) f = cutoff u f + single (succ u) ((f : DigitExpansion Z b) (succ u)) := by
  rw [← sub_eq_iff_eq_add]
  ext z : 2
  simp only [AddSubgroupClass.coe_sub, val_cutoff, val_single, DigitExpansion.sub_def]
  rcases le_or_lt z u with h|h
  · rw [cutoff_apply_le _ _ _ h, single_apply_of_ne _ _ _ (h.trans_lt (lt_succ _)).ne',
        cutoff_apply_le _ _ _ (h.trans (le_succ _)), difcar_eq_zero_iff.mpr, sub_zero, sub_zero]
    intro x _ H
    have : x = succ u
    · contrapose! H
      simp [H.symm]
    simp [this] at H
  · rw [cutoff_apply_lt _ _ _ h]
    rw [← succ_le_iff] at h
    rcases h.eq_or_lt with rfl|h
    · simp only [cutoff_apply_self, single_apply_self, sub_self, zero_sub, neg_eq_zero,
      difcar_eq_zero_iff, gt_iff_lt, ne_eq]
      intro x hx H
      have : x = succ u
      · contrapose! H
        simp [H.symm]
      simp [this] at hx
    · rw [cutoff_apply_lt _ _ _ h, single_apply_of_ne _ _ _ h.ne, difcar_eq_zero_iff.mpr]
      · simp
      intro x hx H
      have : x = succ u
      · contrapose! H
        simp [H.symm]
      simp [this, (h.trans' (lt_succ _)).not_le] at hx

end cutoff

end real

end DigitExpansion
