/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
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
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact h1 _ (id_le_iterate_of_id_le le_succ n m) ih

theorem Succ.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) {a b : α} (h : a ≤ b) :
    p a ↔ p b := by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  exact Iterate.rec (fun b => p a ↔ p b) (fun c hc => hc.trans (hsucc _)) Iff.rfl n

lemma le_total_of_codirected {r v₁ v₂ : α} (h₁ : r ≤ v₁) (h₂ : r ≤ v₂) : v₁ ≤ v₂ ∨ v₂ ≤ v₁ := by
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

lemma le_total_of_directed {r v₁ v₂ : α} (h₁ : v₁ ≤ r) (h₂ : v₂ ≤ r) : v₁ ≤ v₂ ∨ v₂ ≤ v₁ :=
  Or.symm (le_total_of_codirected (α := αᵒᵈ) h₁ h₂)

end PredOrder

end Preorder

section PartialOrder

variable [PartialOrder α]

lemma lt_or_le_of_codirected [SuccOrder α] [IsSuccArchimedean α] {r v₁ v₂ : α} (h₁ : r ≤ v₁)
    (h₂ : r ≤ v₂) : v₁ < v₂ ∨ v₂ ≤ v₁ := by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_codirected h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

/--
This isn't an instance due to a loop with `LinearOrder`.
-/
-- See note [reducible non instances]
abbrev IsSuccArchimedean.linearOrder [SuccOrder α] [IsSuccArchimedean α]
     [DecidableEq α] [DecidableLE α] [DecidableLT α]
     [IsDirected α (· ≥ ·)] : LinearOrder α where
  le_total a b :=
    have ⟨c, ha, hb⟩ := directed_of (· ≥ ·) a b
    le_total_of_codirected ha hb
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance

lemma lt_or_le_of_directed [PredOrder α] [IsPredArchimedean α] {r v₁ v₂ : α} (h₁ : v₁ ≤ r)
    (h₂ : v₂ ≤ r) : v₁ < v₂ ∨ v₂ ≤ v₁ := by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_directed h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

/--
This isn't an instance due to a loop with `LinearOrder`.
-/
-- See note [reducible non instances]
abbrev IsPredArchimedean.linearOrder [PredOrder α] [IsPredArchimedean α]
     [DecidableEq α] [DecidableLE α] [DecidableLT α]
     [IsDirected α (· ≤ ·)] : LinearOrder α :=
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

lemma StrictMono.not_bddAbove_range_of_isSuccArchimedean [NoMaxOrder α] [SuccOrder β]
    [IsSuccArchimedean β] (hf : StrictMono f) : ¬ BddAbove (Set.range f) := by
  rintro ⟨m, hm⟩
  have hm' : ∀ a, f a ≤ m := fun a ↦ hm <| Set.mem_range_self _
  obtain ⟨a₀⟩ := ‹Nonempty α›
  suffices ∀ b, f a₀ ≤ b → ∃ a, b < f a by
    obtain ⟨a, ha⟩ : ∃ a, m < f a := this m (hm' a₀)
    exact ha.not_ge (hm' a)
  have h : ∀ a, ∃ a', f a < f a' := fun a ↦ (exists_gt a).imp (fun a' h ↦ hf h)
  apply Succ.rec
  · exact h a₀
  rintro b _ ⟨a, hba⟩
  exact (h a).imp (fun a' ↦ (succ_le_of_lt hba).trans_lt)

lemma StrictMono.not_bddBelow_range_of_isPredArchimedean [NoMinOrder α] [PredOrder β]
    [IsPredArchimedean β] (hf : StrictMono f) : ¬ BddBelow (Set.range f) :=
  hf.dual.not_bddAbove_range_of_isSuccArchimedean

lemma StrictAnti.not_bddBelow_range_of_isSuccArchimedean [NoMinOrder α] [SuccOrder β]
    [IsSuccArchimedean β] (hf : StrictAnti f) : ¬ BddAbove (Set.range f) :=
  hf.dual_right.not_bddBelow_range_of_isPredArchimedean

lemma StrictAnti.not_bddBelow_range_of_isPredArchimedean [NoMaxOrder α] [PredOrder β]
    [IsPredArchimedean β] (hf : StrictAnti f) : ¬ BddBelow (Set.range f) :=
  hf.dual_right.not_bddAbove_range_of_isSuccArchimedean

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

section IsLeast

-- TODO: generalize to PartialOrder and `DirectedOn` after https://github.com/leanprover-community/mathlib4/pull/16272
lemma BddAbove.exists_isGreatest_of_nonempty {X : Type*} [LinearOrder X] [SuccOrder X]
    [IsSuccArchimedean X] {S : Set X} (hS : BddAbove S) (hS' : S.Nonempty) :
    ∃ x, IsGreatest S x := by
  obtain ⟨m, hm⟩ := hS
  obtain ⟨n, hn⟩ := hS'
  by_cases hm' : m ∈ S
  · exact ⟨_, hm', hm⟩
  have hn' := hm hn
  revert hn hm hm'
  refine Succ.rec ?_ ?_ hn'
  · simp +contextual
  intro m _ IH hm hn hm'
  rw [mem_upperBounds] at IH hm
  simp_rw [Order.le_succ_iff_eq_or_le] at hm
  replace hm : ∀ x ∈ S, x ≤ m := by
    intro x hx
    refine (hm x hx).resolve_left ?_
    rintro rfl
    exact hm' hx
  by_cases hmS : m ∈ S
  · exact ⟨m, hmS, hm⟩
  · exact IH hm hn hmS

lemma BddBelow.exists_isLeast_of_nonempty {X : Type*} [LinearOrder X] [PredOrder X]
    [IsPredArchimedean X] {S : Set X} (hS : BddBelow S) (hS' : S.Nonempty) :
    ∃ x, IsLeast S x :=
  hS.dual.exists_isGreatest_of_nonempty hS'

end IsLeast

section OrderIso

variable {X Y : Type*} [PartialOrder X] [PartialOrder Y]

/-- `IsSuccArchimedean` transfers across equivalences between `SuccOrder`s. -/
protected lemma IsSuccArchimedean.of_orderIso [SuccOrder X] [IsSuccArchimedean X] [SuccOrder Y]
    (f : X ≃o Y) : IsSuccArchimedean Y where
  exists_succ_iterate_of_le {a b} h := by
    refine (exists_succ_iterate_of_le ((map_inv_le_map_inv_iff f).mpr h)).imp ?_
    intro n
    rw [← f.apply_eq_iff_eq, EquivLike.apply_inv_apply]
    rintro rfl
    clear h
    induction n generalizing a with
    | zero => simp
    | succ n IH => simp only [Function.iterate_succ', Function.comp_apply, IH, f.map_succ]

/-- `IsPredArchimedean` transfers across equivalences between `PredOrder`s. -/
protected lemma IsPredArchimedean.of_orderIso [PredOrder X] [IsPredArchimedean X] [PredOrder Y]
    (f : X ≃o Y) : IsPredArchimedean Y where
  exists_pred_iterate_of_le {a b} h := by
    refine (exists_pred_iterate_of_le ((map_inv_le_map_inv_iff f).mpr h)).imp ?_
    intro n
    rw [← f.apply_eq_iff_eq, EquivLike.apply_inv_apply]
    rintro rfl
    clear h
    induction n generalizing b with
    | zero => simp
    | succ n IH => simp only [Function.iterate_succ', Function.comp_apply, IH, f.map_pred]

end OrderIso

section OrdConnected

variable [PartialOrder α]

instance Set.OrdConnected.isPredArchimedean [PredOrder α] [IsPredArchimedean α]
    (s : Set α) [s.OrdConnected] : IsPredArchimedean s where
  exists_pred_iterate_of_le := @fun ⟨b, hb⟩ ⟨c, hc⟩ hbc ↦ by classical
    simp only [Subtype.mk_le_mk] at hbc
    obtain ⟨n, hn⟩ := hbc.exists_pred_iterate
    use n
    induction n generalizing c with
    | zero => simp_all
    | succ n hi =>
      simp_all only [Function.iterate_succ, Function.comp_apply]
      change Order.pred^[n] (dite ..) = _
      split_ifs with h
      · dsimp only at h ⊢
        apply hi _ _ _ hn
        · rw [← hn]
          apply Order.pred_iterate_le
      · have : Order.pred (⟨c, hc⟩ : s) = ⟨c, hc⟩ := by
          change dite .. = _
          simp [h]
        rw [Function.iterate_fixed]
        · simp only [Order.pred_eq_iff_isMin] at this
          apply (this.eq_of_le _).symm
          exact hbc
        · exact this

instance Set.OrdConnected.isSuccArchimedean [SuccOrder α] [IsSuccArchimedean α]
    (s : Set α) [s.OrdConnected] : IsSuccArchimedean s :=
  letI : IsPredArchimedean sᵒᵈ := inferInstanceAs (IsPredArchimedean (OrderDual.ofDual ⁻¹' s))
  inferInstanceAs (IsSuccArchimedean sᵒᵈᵒᵈ)

end OrdConnected

section Monotone
variable {α β : Type*} [PartialOrder α] [Preorder β]

section SuccOrder
variable [SuccOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

lemma monotoneOn_of_le_succ (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMax a → a ∈ s → succ a ∈ s → f a ≤ f (succ a)) : MonotoneOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at hb ⊢
    have : succ^[n] a ∈ s := hs.1 ha hb ⟨le_succ_iterate .., le_succ _⟩
    by_cases hb' : IsMax (succ^[n] a)
    · rw [succ_eq_iff_isMax.2 hb']
      exact hn this
    · exact (hn this).trans (hf _ hb' this hb)

lemma antitoneOn_of_succ_le (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMax a → a ∈ s → succ a ∈ s → f (succ a) ≤ f a) : AntitoneOn f s :=
  monotoneOn_of_le_succ (β := βᵒᵈ) hs hf

lemma strictMonoOn_of_lt_succ (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMax a → a ∈ s → succ a ∈ s → f a < f (succ a)) : StrictMonoOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  apply not_isMax_of_lt at hab
  induction n with
  | zero => simpa using hf _ hab ha hb
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at hb ⊢
    have : succ^[n + 1] a ∈ s := hs.1 ha hb ⟨le_succ_iterate .., le_succ _⟩
    by_cases hb' : IsMax (succ^[n + 1] a)
    · rw [succ_eq_iff_isMax.2 hb']
      exact hn this
    · exact (hn this).trans (hf _ hb' this hb)

lemma strictAntiOn_of_succ_lt (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMax a → a ∈ s → succ a ∈ s → f (succ a) < f a) : StrictAntiOn f s :=
  strictMonoOn_of_lt_succ (β := βᵒᵈ) hs hf

lemma monotone_of_le_succ (hf : ∀ a, ¬ IsMax a → f a ≤ f (succ a)) : Monotone f := by
  simpa using monotoneOn_of_le_succ Set.ordConnected_univ (by simpa using hf)

lemma antitone_of_succ_le (hf : ∀ a, ¬ IsMax a → f (succ a) ≤ f a) : Antitone f := by
  simpa using antitoneOn_of_succ_le Set.ordConnected_univ (by simpa using hf)

lemma strictMono_of_lt_succ (hf : ∀ a, ¬ IsMax a → f a < f (succ a)) : StrictMono f := by
  simpa using strictMonoOn_of_lt_succ Set.ordConnected_univ (by simpa using hf)

lemma strictAnti_of_succ_lt (hf : ∀ a, ¬ IsMax a → f (succ a) < f a) : StrictAnti f := by
  simpa using strictAntiOn_of_succ_lt Set.ordConnected_univ (by simpa using hf)

end SuccOrder

section PredOrder
variable [PredOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

lemma monotoneOn_of_pred_le (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMin a → a ∈ s → pred a ∈ s → f (pred a) ≤ f a) : MonotoneOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_pred_iterate_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at ha ⊢
    have : pred^[n] b ∈ s := hs.1 ha hb ⟨pred_le _, pred_iterate_le ..⟩
    by_cases ha' : IsMin (pred^[n] b)
    · rw [pred_eq_iff_isMin.2 ha']
      exact hn this
    · exact (hn this).trans' (hf _ ha' this ha)

lemma antitoneOn_of_le_pred (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMin a → a ∈ s → pred a ∈ s → f a ≤ f (pred a)) : AntitoneOn f s :=
  monotoneOn_of_pred_le (β := βᵒᵈ) hs hf

lemma strictMonoOn_of_pred_lt (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMin a → a ∈ s → pred a ∈ s → f (pred a) < f a) : StrictMonoOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_pred_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  apply not_isMin_of_lt at hab
  induction n with
  | zero => simpa using hf _ hab hb ha
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at ha ⊢
    have : pred^[n + 1] b ∈ s := hs.1 ha hb ⟨pred_le _, pred_iterate_le ..⟩
    by_cases ha' : IsMin (pred^[n + 1] b)
    · rw [pred_eq_iff_isMin.2 ha']
      exact hn this
    · exact (hn this).trans' (hf _ ha' this ha)

lemma strictAntiOn_of_lt_pred (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMin a → a ∈ s → pred a ∈ s → f a < f (pred a)) : StrictAntiOn f s :=
  strictMonoOn_of_pred_lt (β := βᵒᵈ) hs hf

lemma monotone_of_pred_le (hf : ∀ a, ¬ IsMin a → f (pred a) ≤ f a) : Monotone f := by
  simpa using monotoneOn_of_pred_le Set.ordConnected_univ (by simpa using hf)

lemma antitone_of_le_pred (hf : ∀ a, ¬ IsMin a → f a ≤ f (pred a)) : Antitone f := by
  simpa using antitoneOn_of_le_pred Set.ordConnected_univ (by simpa using hf)

lemma strictMono_of_pred_lt (hf : ∀ a, ¬ IsMin a → f (pred a) < f a) : StrictMono f := by
  simpa using strictMonoOn_of_pred_lt Set.ordConnected_univ (by simpa using hf)

lemma strictAnti_of_lt_pred (hf : ∀ a, ¬ IsMin a → f a < f (pred a)) : StrictAnti f := by
  simpa using strictAntiOn_of_lt_pred Set.ordConnected_univ (by simpa using hf)

end PredOrder
end Monotone
