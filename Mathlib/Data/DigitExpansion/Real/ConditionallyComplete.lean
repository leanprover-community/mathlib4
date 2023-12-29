/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.DigitExpansion.Real.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Defining reals without the use of rationals

Constructing the conditionally complete linear order on the reals.

* [Defining reals without the use of rationals][debruijn1976]

-/


open Order

variable {Z : Type*} [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : NeZero b]
    [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]

namespace DigitExpansion.real

lemma cutoff_succ_aux_isLeast (S : Set (real Z b)) (u : Z)
    (g : real Z b) (hg : IsLeast (cutoff u '' S) g) :
    ∃ f ∈ S, IsLeast (cutoff (succ u) '' S) (cutoff (succ u) f) := by
  let S' : Set (Fin (b + 1)) := ((· (succ u)) ∘ Subtype.val) '' (S ∩ {g' | cutoff u g' = g})
  obtain ⟨g', hg'⟩ := hg.left
  have hN : S'.Nonempty := ⟨g'.val (succ u), g', hg', rfl⟩
  have hF : S'.Finite := S'.toFinite
  obtain ⟨i, ⟨f, ⟨hmem, hf⟩, rfl⟩, hmin⟩ := Set.exists_min_image S' id hF hN
  simp only [Function.comp_apply, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq,
    exists_and_right, id_eq, forall_exists_index, and_imp] at hmin
  refine' ⟨f, hmem, ⟨f, hmem, rfl⟩, _⟩
  intro p ⟨p', hp, hp'⟩
  rw [← hp']
  by_contra! H
  have hup : cutoff u p' = cutoff u p := by
    rw [← hp', cutoff_cutoff_of_le _ (le_succ _)]
  have H' : cutoff u p = cutoff u f := by
    rw [← hup]
    refine le_antisymm ?_ ?_
    · convert cutoff_mono u H.le using 1
      · exact (cutoff_cutoff_of_le _ (le_succ u)).symm
      · exact (cutoff_cutoff_of_le _ (le_succ u)).symm
    · rw [hf]
      exact hg.right ⟨_, hp, rfl⟩
  have key : (p' : DigitExpansion Z b) (succ u) < (f : DigitExpansion Z b) (succ u) := by
    rw [cutoff_succ_eq_cutoff_add_single, cutoff_succ_eq_cutoff_add_single, hup, H'] at H
    simpa using H
  refine key.not_le (hmin _ _ hp ?_ rfl)
  rw [hup, H', hf]

theorem exists_isLeast_image_cutoff
    (S : Set (real Z b)) (hn : S.Nonempty) (h : BddBelow S) (z : Z) :
    ∃ x, IsLeast (cutoff z '' S) x := by
  have : Nonempty Z := ⟨z⟩
  obtain ⟨w, f, hf⟩ := exists_exists_isLeast_image_cutoff S hn h
  cases' le_total z w with hw hw
  · refine' ⟨cutoff z f, _⟩
    have : cutoff z '' (cutoff w '' S) = cutoff z '' S
    · ext g
      simp only [Set.mem_image]
      refine' ⟨_, _⟩
      · rintro ⟨n, ⟨m, hm, rfl⟩, rfl⟩
        exact ⟨m, hm, (cutoff_cutoff_of_le _ hw).symm⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨_, ⟨n, hn, rfl⟩, (cutoff_cutoff_of_le _ hw)⟩
    rw [← this]
    exact ⟨⟨f, hf.left, rfl⟩, (cutoff_monotone  _).mem_lowerBounds_image hf.right⟩
  · revert hf
    refine' Succ.rec _ _ hw
    · intro h
      exact ⟨_, h⟩
    intro u _ IH hf
    obtain ⟨g, hg⟩ := IH hf
    obtain ⟨f, _, hf'⟩ := cutoff_succ_aux_isLeast S u g hg
    exact ⟨_, hf'⟩

section sInf

/-- The infimum sequence of a nonempty bounded below set. Such a sequence is real,
directly constructed in `DigitExpansion.real.sInf`. -/
protected noncomputable def sInf_aux (S : Set (real Z b)) (hn : S.Nonempty) (h : BddBelow S) :
    DigitExpansion Z b where
  toFun z := (exists_isLeast_image_cutoff S hn h z).choose.val z
  bounded' := by
    rintro ⟨x, hx⟩
    obtain ⟨u, hu, hu'⟩ := (exists_isLeast_image_cutoff S hn h (succ x)).choose_spec.left
    suffices : ∀ y > x, cutoff y (exists_isLeast_image_cutoff S hn h y).choose = cutoff y u
    · obtain ⟨y, hy, hy'⟩ := u.val.exists_bounded x
      refine absurd ?_ hy'.not_le
      rw [← cutoff_apply_self, ← val_cutoff, ← this y hy, val_cutoff, cutoff_apply_self]
      simpa using (hx y hy).ge
    intro y hy
    refine Succ.rec ?_ ?_ (succ_le_of_lt hy)
    · obtain ⟨g, hg, hg'⟩ := (exists_isLeast_image_cutoff S hn h y).choose_spec.left
      have hug : cutoff (succ x) u = cutoff (succ x) g := by
        refine le_antisymm (((exists_isLeast_image_cutoff S hn h _).choose_spec.right
            ⟨g, hg, rfl⟩).trans' hu'.le) ?_
        rw [← cutoff_cutoff_of_le g (succ_le_of_lt hy), ← cutoff_cutoff_of_le u (succ_le_of_lt hy)]
        refine cutoff_mono _ <| ((exists_isLeast_image_cutoff S hn h _).choose_spec.right
            ⟨u, hu, rfl⟩).trans' hg'.le
      rw [← hu', hug, cutoff_idem]
    intro y hy IH
    obtain ⟨F, hF, hF'⟩ := (exists_isLeast_image_cutoff S hn h y).choose_spec.left
    obtain ⟨f, hf, hf'⟩ := (exists_isLeast_image_cutoff S hn h (succ y)).choose_spec.left
    have hfF : cutoff y F = cutoff y f := by
      refine le_antisymm (((exists_isLeast_image_cutoff S hn h _).choose_spec.right
          ⟨f, hf, rfl⟩).trans' hF'.le) ?_
      rw [← cutoff_cutoff_of_le F (le_succ _), ← cutoff_cutoff_of_le f (le_succ _), hf']
      exact cutoff_mono _ <| (exists_isLeast_image_cutoff S hn h _).choose_spec.right
          ⟨F, hF, rfl⟩
    have : cutoff (succ y) f ≤ cutoff (succ y) u := by
      rw [hf']
      exact (exists_isLeast_image_cutoff S hn h _).choose_spec.right
          ⟨u, hu, rfl⟩
    cases' this.eq_or_lt with huf huf
    · rw [← hf', huf, cutoff_idem]
    specialize hx (succ y) <| (lt_succ _).trans_le (hy.trans (le_succ _))
    simp only at hx
    rw [cutoff_succ_eq_cutoff_add_single, cutoff_succ_eq_cutoff_add_single, ← hfF,
        ← cutoff_idem _ y, hF', IH, add_lt_add_iff_left, single_lt_right_iff,
        ← cutoff_apply_self, ← val_cutoff, hf', hx] at huf
    convert absurd (Fin.le_last _) (huf.trans_le' _).not_le
    simp [Fin.ext_iff]

/-- The infimum sequence of a nonempty bounded below set. -/
protected noncomputable def sInf (S : Set (real Z b)) (hn : S.Nonempty) (h : BddBelow S) :
    real Z b where
  val := real.sInf_aux S hn h
  property := by
    cases' eq_or_ne (real.sInf_aux S hn h) 0 with h0 hne0
    · rw [h0]
      exact AddSubgroup.zero_mem (real Z b)
    have := hne0
    simp only [ne_eq, FunLike.ne_iff, zero_apply] at this
    obtain ⟨k, hk⟩ := this
    by_cases H : ∃ x, (exists_isLeast_image_cutoff S hn h x).choose.val.Negative
    · obtain ⟨x, -, z, hz⟩ := H
      obtain ⟨g, hg, hg'⟩ := (exists_isLeast_image_cutoff S hn h x).choose_spec.left
      have hz' : z ≤ succ x := by
        contrapose! hz
        refine ⟨_, hz, ?_⟩
        simp [← hg', val_cutoff, cutoff_apply_lt _ _ _ (lt_succ _), Fin.ext_iff, hb.out.symm]
      suffices : ∀ y < z, real.sInf_aux S hn h y = b
      · refine Or.inr (Or.inl ⟨hne0, _, this⟩)
      intro y hy
      simp only [real.sInf_aux, mk_apply]
      obtain ⟨u, hu, hu'⟩ := (exists_isLeast_image_cutoff S hn h y).choose_spec.left
      have hug : cutoff y u ≤ cutoff y g := hu'.le.trans <|
        (exists_isLeast_image_cutoff S hn h y).choose_spec.right ⟨g, hg, rfl⟩
      have hgu : cutoff x g ≤ cutoff x u := hg'.le.trans <|
        (exists_isLeast_image_cutoff S hn h x).choose_spec.right ⟨u, hu, rfl⟩
      replace hug : cutoff y u = cutoff y g := by
        refine le_antisymm hug ?_
        convert cutoff_mono y hgu using 1 <;>
        rw [cutoff_cutoff_of_le _ (le_of_lt_succ (hy.trans_le hz'))]
      rw [← hu', hug, val_cutoff, cutoff_apply_self,
          ← cutoff_apply_le _ _ _ (le_of_lt_succ (hy.trans_le hz')), ← val_cutoff, hg', hz _ hy]
    · push_neg at H
      have := H k
      obtain ⟨g, hg, hg'⟩ := (exists_isLeast_image_cutoff S hn h k).choose_spec.left
      rcases (cutoff k g).prop with hgr|hgr|hgr
      · obtain ⟨-, z, hz⟩ := hgr
        refine Or.inl ⟨hne0, z, ?_⟩
        intro y hy
        simp only [real.sInf_aux, mk_apply]
        obtain ⟨u, hu, hu'⟩ := (exists_isLeast_image_cutoff S hn h y).choose_spec.left
        have hug : cutoff y u ≤ cutoff y g := hu'.le.trans <|
          (exists_isLeast_image_cutoff S hn h y).choose_spec.right ⟨g, hg, rfl⟩
        have hgu : cutoff k g ≤ cutoff k u := hg'.le.trans <|
          (exists_isLeast_image_cutoff S hn h k).choose_spec.right ⟨u, hu, rfl⟩
        cases' le_or_lt k y with hyk hyk
        · simp only [real.sInf_aux, mk_apply, ← hg', hz _ (hyk.trans_lt hy),
                     not_true_eq_false] at hk
        replace hug : cutoff y u = cutoff y g := by
          refine le_antisymm hug ?_
          convert cutoff_mono y hgu using 1 <;>
          rw [cutoff_cutoff_of_le _ hyk.le]
        rw [← hu', hug, val_cutoff, cutoff_apply_self,
            ← cutoff_apply_le _ _ _ hyk.le, ← val_cutoff, hz _ hy]
      · rw [hg'] at hgr
        exact absurd hgr (H _)
      · simp only [real.sInf_aux, mk_apply, ← hg', hgr, zero_apply, not_true_eq_false] at hk

protected lemma sInf_le (S : Set (real Z b)) (hn : S.Nonempty) (h : BddBelow S) (f : real Z b)
    (hf : f ∈ S) : real.sInf S hn h ≤ f := by
  have key : ∀ z, cutoff z (real.sInf S hn h) ≤ cutoff z f
  · intro z
    obtain ⟨g, hg, hg'⟩ := (exists_isLeast_image_cutoff S hn h z).choose_spec.left
    have hgf : cutoff z g ≤ cutoff z f := hg'.le.trans <|
      (exists_isLeast_image_cutoff S hn h _).choose_spec.right ⟨f, hf, rfl⟩
    have hcg : cutoff z (real.sInf S hn h) ≤ cutoff z g := by
      refine le_of_eq ?_
      ext i : 2
      cases' lt_or_le z i with hi hi
      · simp [cutoff_apply_lt, hi]
      · rw [real.sInf, val_cutoff, cutoff_apply_le _ _ _ hi, val_cutoff]
        simp only [real.sInf_aux, mk_apply]
        obtain ⟨u, hu, hu'⟩ := (exists_isLeast_image_cutoff S hn h i).choose_spec.left
        have hug : cutoff i u ≤ cutoff i g := hu'.le.trans <|
          (exists_isLeast_image_cutoff S hn h i).choose_spec.right ⟨g, hg, rfl⟩
        have hgu : cutoff z g ≤ cutoff z u := hg'.le.trans <|
          (exists_isLeast_image_cutoff S hn h z).choose_spec.right ⟨u, hu, rfl⟩
        replace hug : cutoff i u = cutoff i g := by
          refine le_antisymm hug ?_
          convert cutoff_mono i hgu using 1 <;>
          rw [cutoff_cutoff_of_le _ hi]
        rw [← hu', hug, val_cutoff, cutoff_apply_le _ _ _ hi, cutoff_apply_self]
    exact hcg.trans hgf
  by_contra!
  obtain ⟨z, zpos, hz⟩ := id this.exists_least_pos
  have hcf := le_antisymm (cutoff_mono z this.le) (key z)
  rw [DigitExpansion.sub_def, ← cutoff_apply_self, ← val_cutoff, ← hcf, val_cutoff,
      cutoff_apply_self, sub_self, zero_sub] at zpos
  replace zpos : difcar (real.sInf S hn h).val f z = 1
  · refine (difcar_eq_zero_or_one _ _ z).resolve_left ?_
    intro H
    simp [H] at zpos
  rw [difcar_eq_one_iff] at zpos
  obtain ⟨x, -, IH⟩ := zpos
  have hcf' := le_antisymm (cutoff_mono x this.le) (key x)
  rw [Subtype.ext_iff, FunLike.ext_iff] at hcf'
  specialize hcf' x
  simp [IH.left.ne'] at hcf'

protected lemma sInf_lt_iff {S : Set (real Z b)} {hn : S.Nonempty} {h : BddBelow S}
    {f : real Z b} : real.sInf S hn h < f ↔ ∃ g ∈ S, g < f := by
  constructor
  · intro H
    have : ∃ z, cutoff z (real.sInf S hn h) < cutoff z f := by
      contrapose! H
      exact le_of_forall_cutoff_le_cutoff H
    obtain ⟨z, hz⟩ := this
    obtain ⟨g, hg, hg'⟩ := (exists_isLeast_image_cutoff S hn h z).choose_spec.left
    have : cutoff z (real.sInf S hn h) = cutoff z g := by
      ext i : 2
      cases' lt_or_le z i with hi hi
      · simp [cutoff_apply_lt, hi]
      · rw [real.sInf, val_cutoff, cutoff_apply_le _ _ _ hi, val_cutoff]
        simp only [real.sInf_aux, mk_apply]
        obtain ⟨u, hu, hu'⟩ := (exists_isLeast_image_cutoff S hn h i).choose_spec.left
        have hug : cutoff i u ≤ cutoff i g := hu'.le.trans <|
          (exists_isLeast_image_cutoff S hn h i).choose_spec.right ⟨g, hg, rfl⟩
        have hgu : cutoff z g ≤ cutoff z u := hg'.le.trans <|
          (exists_isLeast_image_cutoff S hn h z).choose_spec.right ⟨u, hu, rfl⟩
        replace hug : cutoff i u = cutoff i g := by
          refine le_antisymm hug ?_
          convert cutoff_mono i hgu using 1 <;>
          rw [cutoff_cutoff_of_le _ hi]
        rw [← hu', hug, val_cutoff, cutoff_apply_le _ _ _ hi, cutoff_apply_self]
    refine ⟨g, hg, ?_⟩
    contrapose! hz
    rw [this]
    exact cutoff_mono _ hz
  · rintro ⟨g, hg, hg'⟩
    contrapose! hg'
    exact hg'.trans (real.sInf_le _ _ _ _ hg)

open Classical
noncomputable instance : ConditionallyCompleteLinearOrder (real Z b) :=
  { DigitExpansion.real.instLinearOrder _
    _ with
    sup := max
    inf := min
    le_sup_left := le_max_left
    le_sup_right := le_max_right
    sup_le := fun _ _ _ => max_le
    inf_le_left := min_le_left
    inf_le_right := min_le_right
    le_inf := fun _ _ _ => le_min
    sSup := fun s => if h : s.Nonempty ∧ BddAbove s then
      - real.sInf ((- ·) '' s) (by simpa using h.left.image (- ·)) (by
          have : Antitone (fun x : real Z b ↦ -x) := by intro; simp
          simpa using this.map_bddAbove h.right
        )
        else 0
    sInf := fun s => if h : s.Nonempty ∧ BddBelow s then real.sInf s h.left h.right else 0
    le_csSup := by
      intro s x hs hx
      have hs' : s.Nonempty := ⟨_, hx⟩
      have hx' : -x ∈ ((- ·) '' s) := by simp [hx]
      simpa [hs', hs, ← le_neg (b := x)] using real.sInf_le _ _ _ _ hx'
    le_csInf := by
      intro s x hs hx
      have hs' : BddBelow s := ⟨x, hx⟩
      simp only [hs, hs', and_self, dite_true, ge_iff_le]
      rw [← not_lt, real.sInf_lt_iff]
      push_neg
      intro _ hg
      exact hx hg
    csSup_le := by
      intro s x hs hx
      have hs' : BddAbove s := ⟨x, hx⟩
      simp only [hs, hs', and_self, dite_true, ge_iff_le]
      rw [neg_le, ← not_lt, real.sInf_lt_iff]
      push_neg
      intro g hg
      rw [neg_le]
      refine hx ?_
      obtain ⟨_, hg', rfl⟩ := hg
      simp [hg']
    csInf_le := by
      intro s _ hs hx
      have hs' : s.Nonempty := ⟨_, hx⟩
      simpa [hs, hs'] using real.sInf_le _ _ _ _ hx
    csSup_of_not_bddAbove := by
      intro _ hs
      dsimp only
      rw [dif_neg, dif_neg] <;>
      simp [hs]
    csInf_of_not_bddBelow := by
      intro _ hs
      dsimp only
      rw [dif_neg, dif_neg] <;>
      simp [hs]
  }

end sInf

end DigitExpansion.real
