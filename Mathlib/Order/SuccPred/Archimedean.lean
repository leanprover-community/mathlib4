/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Daniel Weber
-/
import Mathlib.Order.SuccPred.Basic

/-!
# Archimedean successor and predecessor

* `IsSuccArchimedean`: `SuccOrder` where `succ` iterated to an element gives all the greater
  ones.
* `IsPredArchimedean`: `PredOrder` where `pred` iterated to an element gives all the smaller
  ones.
-/

variable {α β : Type*}

open Order Function

/-- A `SuccOrder` is succ-archimedean if one can go from any two comparable elements by iterating
`succ` -/
class IsSuccArchimedean (α : Type*) [Preorder α] [SuccOrder α] : Prop where
  /-- If `a ≤ b` then one can get to `a` from `b` by iterating `succ` -/
  exists_succ_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, succ^[n] a = b

/-- A `PredOrder` is pred-archimedean if one can go from any two comparable elements by iterating
`pred` -/
class IsPredArchimedean (α : Type*) [Preorder α] [PredOrder α] : Prop where
  /-- If `a ≤ b` then one can get to `b` from `a` by iterating `pred` -/
  exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, pred^[n] b = a

export IsSuccArchimedean (exists_succ_iterate_of_le)

export IsPredArchimedean (exists_pred_iterate_of_le)

section Preorder

variable [Preorder α]

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

instance : IsPredArchimedean αᵒᵈ :=
  ⟨fun {a b} h => by convert exists_succ_iterate_of_le h.ofDual⟩

theorem LE.le.exists_succ_iterate (h : a ≤ b) : ∃ n, succ^[n] a = b :=
  exists_succ_iterate_of_le h

theorem exists_succ_iterate_iff_le : (∃ n, succ^[n] a = b) ↔ a ≤ b := by
  refine ⟨?_, exists_succ_iterate_of_le⟩
  rintro ⟨n, rfl⟩
  exact id_le_iterate_of_id_le le_succ n a

/-- Induction principle on a type with a `SuccOrder` for all elements above a given element `m`. -/
@[elab_as_elim]
theorem Succ.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (succ n)) ⦃n : α⦄
    (hmn : m ≤ n) : P n := by
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate; clear hmn
  induction' n with n ih
  · exact h0
  · rw [Function.iterate_succ_apply']
    exact h1 _ (id_le_iterate_of_id_le le_succ n m) ih

theorem Succ.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) {a b : α} (h : a ≤ b) :
    p a ↔ p b := by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  exact Iterate.rec (fun b => p a ↔ p b) (fun c hc => hc.trans (hsucc _)) Iff.rfl n

lemma le_total_of_ge {r v₁ v₂ : α} (h₁ : r ≤ v₁) (h₂ : r ≤ v₂) : v₁ ≤ v₂ ∨ v₂ ≤ v₁ := by
  obtain ⟨n, rfl⟩ := h₁.exists_succ_iterate
  obtain ⟨m, rfl⟩ := h₂.exists_succ_iterate
  clear h₁ h₂
  wlog h : n ≤ m
  · rw [Or.comm]
    apply this
    exact Nat.le_of_not_ge h
  left
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, Function.iterate_add, Function.comp_apply]
  apply Order.le_succ_iterate

end SuccOrder

section PredOrder

variable [PredOrder α] [IsPredArchimedean α] {a b : α}

instance : IsSuccArchimedean αᵒᵈ :=
  ⟨fun {a b} h => by convert exists_pred_iterate_of_le h.ofDual⟩

theorem LE.le.exists_pred_iterate (h : a ≤ b) : ∃ n, pred^[n] b = a :=
  exists_pred_iterate_of_le h

theorem exists_pred_iterate_iff_le : (∃ n, pred^[n] b = a) ↔ a ≤ b :=
  exists_succ_iterate_iff_le (α := αᵒᵈ)

/-- Induction principle on a type with a `PredOrder` for all elements below a given element `m`. -/
@[elab_as_elim]
theorem Pred.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, n ≤ m → P n → P (pred n)) ⦃n : α⦄
    (hmn : n ≤ m) : P n :=
  Succ.rec (α := αᵒᵈ) (P := P) h0 h1 hmn

theorem Pred.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) {a b : α} (h : a ≤ b) :
    p a ↔ p b :=
  (Succ.rec_iff (α := αᵒᵈ) hsucc h).symm

lemma le_total_of_le {r v₁ v₂ : α} (h₁ : v₁ ≤ r) (h₂ : v₂ ≤ r) : v₁ ≤ v₂ ∨ v₂ ≤ v₁ :=
  Or.symm (le_total_of_ge (α := αᵒᵈ) h₁ h₂)

end PredOrder

end Preorder

section PartialOrder

variable [PartialOrder α]

lemma lt_or_le_of_ge [SuccOrder α] [IsSuccArchimedean α] {r v₁ v₂ : α} (h₁ : r ≤ v₁) (h₂ : r ≤ v₂) :
    v₁ < v₂ ∨ v₂ ≤ v₁ := by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_ge h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

/--
This isn't an instance due to a loop with `LinearOrder`.
-/
-- See note [reducible non instances]
abbrev IsSuccArchimedean.linearOrder [SuccOrder α] [IsSuccArchimedean α]
     [DecidableEq α] [@DecidableRel α (· ≤ ·)] [@DecidableRel α (· < ·)] [IsDirected α (· ≥ ·)] :
     LinearOrder α where
  le_total a b :=
    have ⟨c, ha, hb⟩ := directed_of (· ≥ ·) a b
    le_total_of_ge ha hb
  decidableLE := Classical.decRel _

lemma lt_or_le_of_le [PredOrder α] [IsPredArchimedean α] {r v₁ v₂ : α} (h₁ : v₁ ≤ r) (h₂ : v₂ ≤ r) :
    v₁ < v₂ ∨ v₂ ≤ v₁ := by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_le h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

/--
This isn't an instance due to a loop with `LinearOrder`.
-/
-- See note [reducible non instances]
abbrev IsPredArchimedean.linearOrder [PredOrder α] [IsPredArchimedean α]
     [DecidableEq α] [@DecidableRel α (· ≤ ·)] [@DecidableRel α (· < ·)] [IsDirected α (· ≤ ·)] :
     LinearOrder α :=
  letI : LinearOrder αᵒᵈ := IsSuccArchimedean.linearOrder
  inferInstanceAs (LinearOrder αᵒᵈᵒᵈ)

end PartialOrder

section LinearOrder

variable [LinearOrder α]

section SuccOrder
variable [SuccOrder α]

lemma succ_max (a b : α) : succ (max a b) = max (succ a) (succ b) := succ_mono.map_max
lemma succ_min (a b : α) : succ (min a b) = min (succ a) (succ b) := succ_mono.map_min

variable [IsSuccArchimedean α] {a b : α}

theorem exists_succ_iterate_or : (∃ n, succ^[n] a = b) ∨ ∃ n, succ^[n] b = a :=
  (le_total a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le

theorem Succ.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) (a b : α) : p a ↔ p b :=
  (le_total a b).elim (Succ.rec_iff hsucc) fun h => (Succ.rec_iff hsucc h).symm

end SuccOrder

section PredOrder
variable [PredOrder α]

lemma pred_max (a b : α) : pred (max a b) = max (pred a) (pred b) := pred_mono.map_max
lemma pred_min (a b : α) : pred (min a b) = min (pred a) (pred b) := pred_mono.map_min

variable [IsPredArchimedean α] {a b : α}

theorem exists_pred_iterate_or : (∃ n, pred^[n] b = a) ∨ ∃ n, pred^[n] a = b :=
  (le_total a b).imp exists_pred_iterate_of_le exists_pred_iterate_of_le

theorem Pred.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) (a b : α) : p a ↔ p b :=
  (le_total a b).elim (Pred.rec_iff hsucc) fun h => (Pred.rec_iff hsucc h).symm

end PredOrder

end LinearOrder

section bdd_range
variable [Preorder α] [Nonempty α] [Preorder β] {f : α → β}

lemma StrictMono.not_bddAbove_range [NoMaxOrder α] [SuccOrder β] [IsSuccArchimedean β]
    (hf : StrictMono f) : ¬ BddAbove (Set.range f) := by
  rintro ⟨m, hm⟩
  have hm' : ∀ a, f a ≤ m := fun a ↦ hm <| Set.mem_range_self _
  obtain ⟨a₀⟩ := ‹Nonempty α›
  suffices ∀ b, f a₀ ≤ b → ∃ a, b < f a by
    obtain ⟨a, ha⟩ : ∃ a, m < f a := this m (hm' a₀)
    exact ha.not_le (hm' a)
  have h : ∀ a, ∃ a', f a < f a' := fun a ↦ (exists_gt a).imp (fun a' h ↦ hf h)
  apply Succ.rec
  · exact h a₀
  rintro b _ ⟨a, hba⟩
  exact (h a).imp (fun a' ↦ (succ_le_of_lt hba).trans_lt)

lemma StrictMono.not_bddBelow_range [NoMinOrder α] [PredOrder β] [IsPredArchimedean β]
    (hf : StrictMono f) : ¬ BddBelow (Set.range f) := hf.dual.not_bddAbove_range

lemma StrictAnti.not_bddAbove_range [NoMinOrder α] [SuccOrder β] [IsSuccArchimedean β]
    (hf : StrictAnti f) : ¬ BddAbove (Set.range f) := hf.dual_right.not_bddBelow_range

lemma StrictAnti.not_bddBelow_range [NoMaxOrder α] [PredOrder β] [IsPredArchimedean β]
    (hf : StrictAnti f) : ¬ BddBelow (Set.range f) := hf.dual_right.not_bddAbove_range

end bdd_range

section IsWellFounded

variable [PartialOrder α]

instance (priority := 100) WellFoundedLT.toIsPredArchimedean [h : WellFoundedLT α]
    [PredOrder α] : IsPredArchimedean α :=
  ⟨fun {a b} => by
    refine WellFounded.fix (C := fun b => a ≤ b → ∃ n, Nat.iterate pred n b = a)
      h.wf ?_ b
    intros b ih hab
    replace hab := eq_or_lt_of_le hab
    rcases hab with (rfl | hab)
    · exact ⟨0, rfl⟩
    rcases eq_or_lt_of_le (pred_le b) with hb | hb
    · cases (min_of_le_pred hb.ge).not_lt hab
    dsimp at ih
    obtain ⟨k, hk⟩ := ih (pred b) hb (le_pred_of_lt hab)
    refine ⟨k + 1, ?_⟩
    rw [iterate_add_apply, iterate_one, hk]⟩

instance (priority := 100) WellFoundedGT.toIsSuccArchimedean [h : WellFoundedGT α]
    [SuccOrder α] : IsSuccArchimedean α :=
  let h : IsPredArchimedean αᵒᵈ := by infer_instance
  ⟨h.1⟩

end IsWellFounded

section OrderBot

variable [Preorder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]

theorem Succ.rec_bot (p : α → Prop) (hbot : p ⊥) (hsucc : ∀ a, p a → p (succ a)) (a : α) : p a :=
  Succ.rec hbot (fun x _ h => hsucc x h) (bot_le : ⊥ ≤ a)

end OrderBot

section OrderTop

variable [Preorder α] [OrderTop α] [PredOrder α] [IsPredArchimedean α]

theorem Pred.rec_top (p : α → Prop) (htop : p ⊤) (hpred : ∀ a, p a → p (pred a)) (a : α) : p a :=
  Pred.rec htop (fun x _ h => hpred x h) (le_top : a ≤ ⊤)

end OrderTop

lemma SuccOrder.forall_ne_bot_iff
    [Nontrivial α] [PartialOrder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]
    (P : α → Prop) :
    (∀ i, i ≠ ⊥ → P i) ↔ (∀ i, P (SuccOrder.succ i)) := by
  refine ⟨fun h i ↦ h _ (Order.succ_ne_bot i), fun h i hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ := exists_succ_iterate_of_le (bot_le : ⊥ ≤ i)
  have hj : 0 < j := by apply Nat.pos_of_ne_zero; contrapose! hi; simp [hi]
  rw [← Nat.succ_pred_eq_of_pos hj]
  simp only [Function.iterate_succ', Function.comp_apply]
  apply h
