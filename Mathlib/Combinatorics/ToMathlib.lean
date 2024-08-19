import Mathlib.Order.Atoms
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.SuccPred.Basic
import Mathlib.Data.Nat.Find

instance Set.Ici.predOrder {α : Type*} [DecidableEq α] [PartialOrder α] [PredOrder α] {a : α} :
  PredOrder (Set.Ici a) where
  pred := fun x ↦ if ha : x.1 = a then ⟨a, by simp⟩ else
    ⟨Order.pred x.1, Order.le_pred_of_lt <| lt_of_le_of_ne (by simpa using x.2) <| Ne.symm ha⟩
  pred_le := fun ⟨x, hx⟩ ↦ by dsimp; split <;> simp_all [Order.pred_le]
  min_of_le_pred := @fun ⟨x, hx⟩ h ↦ by
    dsimp at h
    rw [isMin_iff_eq_bot]
    apply Subtype.val_injective
    simp only [coe_bot]
    split at h
    · assumption
    · simp only [Subtype.mk_le_mk] at h
      apply Order.min_of_le_pred at h
      exact (h.eq_of_le hx).symm
  le_pred_of_lt := @fun ⟨b, hb⟩ ⟨c, hc⟩ h ↦ by
    rw [Subtype.mk_lt_mk] at h
    dsimp only
    split
    · simp_all [le_of_lt]
    · exact Order.le_pred_of_lt h

instance Set.Ici.isPredArchimedean {α : Type*} [DecidableEq α] [PartialOrder α] [PredOrder α]
    [IsPredArchimedean α] {a : α} : IsPredArchimedean (Set.Ici a) where
  exists_pred_iterate_of_le := @fun ⟨b, hb⟩ ⟨c, hc⟩ hbc ↦ by
    rw [Subtype.mk_le_mk] at hbc
    obtain ⟨n, hn⟩ := IsPredArchimedean.exists_pred_iterate_of_le hbc
    use n
    clear hbc
    induction n generalizing b
    · simpa
    case succ n hn1 =>
      simp_all only [mem_Ici, Function.iterate_succ', Function.comp_apply]
      rw [mem_Ici] at hb hc
      rw [hn1 (Order.pred^[n] c)]
      · change dite .. = _
        apply Subtype.val_injective
        simp only [apply_dite Subtype.val, dite_eq_ite, ← hn, ite_eq_right_iff]
        intro h
        rw [h] at hn ⊢
        rw [← hn] at hb
        apply le_antisymm hb (Order.pred_le a)
      · apply le_trans _ (Order.pred_le ..)
        rwa [hn]
      · rfl

lemma IsPredArchimedean.le_total_of_le {α : Type*} [Preorder α] [PredOrder α]
    [IsPredArchimedean α] (r v₁ v₂ : α) (h₁ : v₁ ≤ r) (h₂ : v₂ ≤ r) :
    v₁ ≤ v₂ ∨ v₂ ≤ v₁ := by
  obtain ⟨n, rfl⟩ := h₁.exists_pred_iterate
  obtain ⟨m, rfl⟩ := h₂.exists_pred_iterate
  clear h₁ h₂
  wlog h : n ≤ m
  · rw [Or.comm]
    apply this
    omega
  right
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, Function.iterate_add, Function.comp_apply]
  apply Order.pred_iterate_le

lemma IsPredArchimedean.lt_or_le_of_le {α : Type*} [PartialOrder α] [PredOrder α]
    [IsPredArchimedean α] (r v₁ v₂ : α) (h₁ : v₁ ≤ r) (h₂ : v₂ ≤ r) :
    v₁ < v₂ ∨ v₂ ≤ v₁ := by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_le r v₁ v₂ h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

def IsPredArchimedean.find_atom {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] (r : α) : α :=
  Order.pred^[Nat.find (bot_le (a := r)).exists_pred_iterate - 1] r

lemma IsPredArchimedean.find_atom_le {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] (r : α) : IsPredArchimedean.find_atom r ≤ r :=
  Order.pred_iterate_le _ _

@[simp]
lemma IsPredArchimedean.pred_find_atom {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] (r : α) :
    Order.pred (IsPredArchimedean.find_atom r) = ⊥ := by
  unfold find_atom
  generalize h : Nat.find (bot_le (a := r)).exists_pred_iterate = n
  cases n
  · have : Order.pred^[0] r = ⊥ := by
      rw [← h]
      apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate
    simp only [Function.iterate_zero, id_eq] at this
    simp [this]
  · simp only [Nat.add_sub_cancel_right, ← Function.iterate_succ_apply', Nat.succ_eq_add_one]
    rw [←h]
    apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate

lemma IsPredArchimedean.find_atom_ne_bot {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] (r : α) (hr : r ≠ ⊥) :
    IsPredArchimedean.find_atom r ≠ ⊥ := by
  unfold find_atom
  intro nh
  have := Nat.find_min' (bot_le (a := r)).exists_pred_iterate nh
  replace : Nat.find (bot_le (a := r)).exists_pred_iterate = 0 := by omega
  simp [this, hr] at nh

def IsPredArchimedean.find_atom_is_atom {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] (r : α) (hr : r ≠ ⊥) :
    IsAtom (IsPredArchimedean.find_atom r) := by
  constructor
  · apply find_atom_ne_bot r hr
  · intro b hb
    apply Order.le_pred_of_lt at hb
    simpa using hb


instance IsPredArchimedean.instIsAtomic {α : Type*} [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] : IsAtomic α where
  eq_bot_or_exists_atom_le b := by classical
    rw [Classical.or_iff_not_imp_left]
    intro hb
    use find_atom b, find_atom_is_atom b hb, find_atom_le b

def InfHom.subtype_val  {α : Type*} [SemilatticeInf α] {P : α → Prop}
    (Pinf : ∀ ⦃x y : α⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.semilatticeInf Pinf
    InfHom {x : α // P x} α :=
  letI := Subtype.semilatticeInf Pinf
  InfHom.mk Subtype.val (by simp)

def InfHom.Ici_val  {α : Type*} [SemilatticeInf α] {r : α} :
    InfHom (Set.Ici r) α := InfHom.subtype_val (fun _ _ ↦ le_inf)
