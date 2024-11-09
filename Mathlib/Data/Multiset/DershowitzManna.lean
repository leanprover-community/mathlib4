/-
Copyright (c) 2024 Haitian Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitian Wang, Malvin Gattinger
-/
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Multiset.OrderedMonoid

/-!
# Dershowitz-Manna ordering

In this file we define the _Dershowitz-Manna ordering_ on multisets. Specifically, for two multisets
`M` and `N` in a partial order `(S, <)`, `M` is smaller than `N` in the Dershowitz-Manna ordering if
`M` can be obtained from `N` by replacing one or more elements in `N` by some finite number of
elements from `S`, each of which is smaller (in the underling ordering over `S`) than one of the
replaced elements from `N`. We prove that, given a well-founded partial order on the underlying set,
the Dershowitz-Manna ordering defined over multisets is also well-founded.

## Main results

- `Multiset.IsDershowitzMannaLT` : the standard definition fo the `Dershowitz-Manna ordering`.
- `Multiset.wellFounded_isDershowitzMannaLT` : the main theorem about the
`Dershowitz-Manna ordering` being well-founded.
- `Multiset.TransLT_eq_isDershowitzMannaLT` : two definitions of the `Dershowitz-Manna ordering`
are equivalent.

## References

* [Wikipedia, Dershowitz–Manna ordering*]
(https://en.wikipedia.org/wiki/Dershowitz%E2%80%93Manna_ordering)

* [CoLoR](https://github.com/fblanqui/color), a Coq library on rewriting theory and termination.
  Our code here is inspired by their formalization and the theorem is called `mOrd_wf` in the file
  [MultisetList.v](https://github.com/fblanqui/color/blob/1.8.5/Util/Multiset/MultisetOrder.v).

-/

open Relation

namespace Multiset

variable {α : Type*} [Preorder α] {M N P : Multiset α} {a : α}

/-- The standard Dershowitz–Manna ordering. -/
def IsDershowitzMannaLT (M N : Multiset α) : Prop :=
  ∃ X Y Z,
      Z ≠ ∅
    ∧ M = X + Y
    ∧ N = X + Z
    ∧ ∀ y ∈ Y, ∃ z ∈ Z, y < z

/-- `IsDershowitzMannaLT` is transitive. -/
lemma IsDershowitzMannaLT.trans :
    IsDershowitzMannaLT M N → IsDershowitzMannaLT N P → IsDershowitzMannaLT M P := by
  classical
  rintro ⟨X₁, Y₁, Z₁, hZ₁, rfl, rfl, hYZ₁⟩ ⟨X₂, Y₂, Z₂, hZ₂, hXZXY, rfl, hYZ₂⟩
  rw [add_comm X₁,add_comm X₂] at hXZXY
  refine ⟨X₁ ∩ X₂, Y₁ + (Y₂ - Z₁), Z₂ + (Z₁ - Y₂), ?_, ?_, ?_, ?_⟩
  · simpa [-not_and, not_and_or] using .inl hZ₂
  · rwa [← add_assoc, add_right_comm, inter_add_sub_of_add_eq_add]
  · rw [← add_assoc, add_right_comm, add_left_inj, inter_comm, inter_add_sub_of_add_eq_add]
    rwa [eq_comm]
  simp only [mem_add, or_imp, forall_and]
  refine ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨z, hz, hyz⟩ := hYZ₁ y hy
    by_cases z_in : z ∈ Y₂
    · obtain ⟨w, hw, hzw⟩ := hYZ₂ z z_in
      exact ⟨w, .inl hw, hyz.trans hzw⟩
    · exact ⟨z, .inr <| by rwa [mem_sub, count_eq_zero_of_not_mem z_in, count_pos], hyz⟩
  · obtain ⟨z, hz, hyz⟩ := hYZ₂ y <| mem_of_le (Multiset.sub_le_self ..) hy
    exact ⟨z, .inl hz, hyz⟩

/-- A special case of `IsDershowitzMannaLT`. The transitive closure of it is used to define
an equivalent (proved later) version of the ordering. -/
private def OneStep (M N : Multiset α) : Prop :=
  ∃ X Y a,
      M = X + Y
    ∧ N = X + {a}
    ∧ ∀ y ∈ Y, y < a

private lemma isDershowitzMannaLT_of_oneStep : OneStep M N → IsDershowitzMannaLT M N := by
  rintro ⟨X, Y, a, M_def, N_def, ys_lt_a⟩
  use X, Y, {a}, by simp, M_def, N_def
  · simpa

private lemma isDershowitzMannaLT_singleton_insert (h : OneStep N (a ::ₘ M)) :
    ∃ M', N = a ::ₘ M' ∧ OneStep M' M ∨ N = M + M' ∧ ∀ x ∈ M', x < a := by
  classical
  rcases h with ⟨X, Y, a0, rfl, h0, h2⟩
  by_cases hyp : a = a0
  · exists Y; right; apply And.intro
    · rw [add_left_inj]
      rw [add_comm, singleton_add] at h0
      simp_all
    · simp_all
  exists (Y + (M - {a0}))
  left
  constructor
  · have : X = (M - {a0} + {a}) := by
      rw [add_comm, singleton_add] at *
      ext b
      simp only [ext, count_cons] at h0
      by_cases h : b = a
      · have := h0 b
        simp_all only [ite_true, ite_false, add_zero, sub_singleton, count_cons_self, ne_eq,
          not_false_eq_true, count_erase_of_ne]
      have := h0 b
      simp [sub_singleton]
      simp_all only [↓reduceIte, add_zero, ne_eq, not_false_eq_true, count_cons_of_ne]
      split at this
      next h_1 =>
        simp_all
      next h_1 => simp_all only [add_zero, ne_eq, not_false_eq_true, count_erase_of_ne]
    subst this
    rw [add_comm]
    nth_rewrite 2 [add_comm]
    rw [singleton_add, add_cons]
  · unfold OneStep
    refine ⟨M - {a0}, Y, a0, ?_, ?_, h2⟩
    · change Y + (M - {a0}) = (M - {a0}) + Y
      rw [add_comm]
    · change M = M - {a0} + {a0}
      have this0 : M = X + {a0} - {a} := by
        rw [← h0, sub_singleton, erase_cons_head]
      have a0M : a0 ∈ M := by
        rw [this0, sub_singleton, mem_erase_of_ne]
        rw [mem_add, mem_singleton]
        · apply Or.inr
          rfl
        · exact fun h ↦ hyp (Eq.symm h)
      rw [add_comm]
      simp_all [singleton_add]

private lemma acc_cons (a : α) (M0 : Multiset α)
    (_ : ∀ b M , LT.lt b a → Acc OneStep M → Acc OneStep (b ::ₘ M))
    (_ : Acc OneStep M0)
    (_ : ∀ M, OneStep M M0 → Acc OneStep (a ::ₘ M)) :
    Acc OneStep (a ::ₘ M0) := by
  constructor
  intros N N_lt
  change Acc OneStep N
  rcases (isDershowitzMannaLT_singleton_insert N_lt) with ⟨x, H, h0⟩
  case h.intro.inr h =>
    rcases h with ⟨H, h0⟩
    rw [H]
    clear H
    induction x using Multiset.induction with
    | empty =>
      simpa
    | cons h =>
      simp_all only [mem_cons, or_true, implies_true, true_implies, forall_eq_or_imp,
        add_cons]
  case h.intro.inl.intro =>
    simp_all

private lemma acc_cons_of_acc (a : α)
    (H : ∀ b, ∀ M, b < a → Acc OneStep M → Acc OneStep (b ::ₘ M)) :
    ∀ M, Acc OneStep M → Acc OneStep (a ::ₘ M) := by
  intros M h0
  induction h0 with
  | intro x wfH wfh2 =>
    apply acc_cons
    · simpa
    · constructor; simpa only
    · simpa only

private lemma acc_cons_of_acc_of_lt (ha : Acc LT.lt a) :
    ∀ M, Acc OneStep M → Acc OneStep (a ::ₘ M) := by
  induction ha with
  | intro x _ ih => exact acc_cons_of_acc _ (by simp_all)

/-- If all elements of a multiset `M` are accessible with `<`, then the multiset `M` is
accessible given the `OneStep` relation. -/
private lemma acc_of_acc_lt (wf_el : ∀ x ∈ M, Acc LT.lt x) : Acc OneStep M := by
  induction M using Multiset.induction_on with
  | empty =>
    constructor
    intro y y_lt
    absurd y_lt
    rintro ⟨X, Y, a, _, nonsense, _⟩
    have contra : a ∈ (0 : Multiset α):= by
      simp_all only [mem_add, mem_singleton, or_true]
    contradiction
  | cons _ _ ih =>
    apply acc_cons_of_acc_of_lt
    · apply wf_el
      simp_all
    · apply ih
      intros
      apply wf_el
      simp_all

/-- Over a well-founded order, `OneStep` is well-founded. -/
private lemma isDershowitzMannaLT_singleton_wf (wf_lt : WellFoundedLT α) :
    WellFounded (OneStep : Multiset α → Multiset α → Prop) := by
  constructor
  intros a
  apply acc_of_acc_lt
  intros x _
  apply wf_lt.induction x
  intros y h
  apply Acc.intro y
  assumption

private lemma transGen_oneStep_of_isDershowitzMannaLT :
    IsDershowitzMannaLT M N → TransGen OneStep M N := by
  classical
  rintro ⟨X, Y, Z, Z_not_empty, MXY, NXZ, h⟩
  revert X Y M N
  induction Z using strongInductionOn
  case ih Z IH =>
    rintro M N X Y rfl rfl Y_lt_Z
    cases em (card Z = 0)
    · simp_all
    cases em (card Z = 1)
    case inl hyp' hyp=>
      rw [card_eq_one] at hyp
      obtain ⟨z, rfl⟩ := hyp
      apply TransGen.single
      refine ⟨X, Y, z, rfl, rfl, ?_⟩
      simp only [mem_singleton, exists_eq_left] at Y_lt_Z
      exact Y_lt_Z
    case inr hyp' hyp =>
      have : ∃ a, a ∈ Z := by
        rw [← Z.card_pos_iff_exists_mem]
        cases Z_empty : card Z
        tauto
        simp
      rcases this with ⟨z,z_in_Z⟩
      let newZ := Z.erase z
      have newZ_nonEmpty : newZ ≠ 0 := by
        simp [newZ, ← sub_singleton, tsub_eq_zero_iff_le]
        aesop
      have newZ_sub_Z : newZ < Z := by simp (config := {zetaDelta := true}); exact z_in_Z
      let f : α → Multiset α := fun z => Y.filter (fun y => y < z) -- DecidableRel
      let N' := X + newZ + f z
      apply @transitive_transGen _ _ _ N'
      -- step from `N'` to `M`
      · apply IH newZ newZ_sub_Z newZ_nonEmpty
        · change _ = (X + f z) + (Y - f z)
          ext a
          have count_lt := count_le_of_le a (filter_le (fun y => y < z) Y)
          simp_all only [empty_eq_zero, ne_eq, card_eq_zero, not_false_eq_true,
            count_add, count_sub]
          let y := count a Y
          let x := count a X
          let fz := count a (filter (fun x => x < z) Y)
          change x + y = x + fz + (y - fz)
          change fz ≤ y at count_lt
          have : y = fz + (y - fz) := by simp_all
          omega
        · unfold N'
          rw [add_assoc, add_assoc, add_comm newZ (f z)]
        · intro y y_in
          let Y_lt_Z := Y_lt_Z y
          have y_in_Y : y ∈ Y := by
            have Yfy_le_Y : Y - f z ≤ Y:= by simp (config := {zetaDelta := true})
            apply mem_of_le Yfy_le_Y
            exact y_in
          let Y_lt_Z := Y_lt_Z y_in_Y
          rcases Y_lt_Z with ⟨t, t_in_Z, y_lt_t⟩
          use t
          constructor
          · by_cases t_in_newZ : t ∈ newZ
            · exact t_in_newZ
            · exfalso
              have : t = z := by
                have : Z = newZ + {z} := by
                  unfold newZ
                  rw [add_comm, singleton_add]
                  simp [cons_erase z_in_Z]
                rw [this, mem_add] at t_in_Z
                have : t ∈ ( {z} : Multiset α) := Or.resolve_left t_in_Z t_in_newZ
                rwa [← mem_singleton]
              have y_in_fz : y ∈ f z := by
                unfold f; simp; rw [← this]; exact ⟨y_in_Y, y_lt_t⟩
              have y_notin_Yfz : y ∉ Y - f z := by
                by_contra
                let neg_f : α → Multiset α := fun y' => Y.filter (fun x => ¬ x < y')
                have : Y - f z = neg_f z := by
                  have fz_negfz_Y : f z + neg_f z = Y := filter_add_not _ _
                  rw [← fz_negfz_Y, add_tsub_cancel_left]
                have y_in_neg_fz : y ∈ neg_f z := this ▸ y_in
                subst_eqs
                unfold neg_f at *
                simp_all only [mem_filter]
              exact y_notin_Yfz y_in
          · exact y_lt_t
      -- single step `N` to `N'`
      · refine .single ⟨X + newZ, f z, z, ?_, ?_, ?_ ⟩
        · rfl
        · have newZ_z_Z: newZ + {z} = Z := by
            unfold newZ; rw [add_comm, singleton_add]
            apply cons_erase z_in_Z
          have : X + newZ + {z} = X + (newZ + {z}) := by apply add_assoc
          rw [this, newZ_z_Z]
        · unfold f; intro z z_in; simp at z_in; exact z_in.2

private lemma isDershowitzMannaLT_of_transGen_oneStep (hMN : TransGen OneStep M N) :
    IsDershowitzMannaLT M N :=
  hMN.trans_induction_on (by rintro _ _ ⟨X, Y, a, rfl, rfl, hYa⟩; exact ⟨X, Y, {a}, by simpa⟩)
    fun  _ _ ↦ .trans

/-- `TransGen OneStep` and `IsDershowitzMannaLT` are equivalent. -/
private lemma transGen_oneStep_eq_isDershowitzMannaLT :
    (TransGen OneStep : Multiset α → Multiset α → Prop) = IsDershowitzMannaLT := by
  ext M N
  exact ⟨isDershowitzMannaLT_of_transGen_oneStep, transGen_oneStep_of_isDershowitzMannaLT⟩

/-- Over a well-founded order, the Dershowitz-Manna order on multisets is well-founded. -/
theorem wellFounded_isDershowitzMannaLT [WellFoundedLT α] :
    WellFounded (IsDershowitzMannaLT : Multiset α → Multiset α → Prop) := by
  rw [← transGen_oneStep_eq_isDershowitzMannaLT]
  exact (isDershowitzMannaLT_singleton_wf ‹_›).transGen

instance instWellFoundedisDershowitzMannaLT [WellFoundedLT α] : WellFoundedRelation (Multiset α) :=
    ⟨IsDershowitzMannaLT, wellFounded_isDershowitzMannaLT⟩

end Multiset
