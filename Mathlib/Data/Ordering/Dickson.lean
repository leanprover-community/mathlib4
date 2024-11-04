/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.TFAE
import Mathlib.Order.OrderIsoNat

/-! # Dickson orders -/


section Dickson

/-- A subset `B` of a set `S` in a preordered type is a basis
if any element of `S` is larger than some element of `B`  -/
def Set.isBasis {α : Type*} [Preorder α] (S B : Set α) : Prop :=
  B ⊆ S ∧ ∀ x ∈ S, ∃ y ∈ B, y ≤ x

/-- A preordered type has the Dickson property if any set contains a finite basis -/
def Preorder.isDickson (α : Type*) [Preorder α] : Prop :=
  ∀ (S : Set α), ∃ (B : Set α), S.isBasis B ∧ Finite B

open Preorder

variable {α : Type*} [Preorder α]

theorem Equiv.isDickson_of_monotone {β : Type*} [Preorder β]
    (f : α ≃ β) (hf : Monotone f) (H : isDickson α) :
  isDickson β := fun S ↦ by
  obtain ⟨B, hB, hB'⟩ := H (S.preimage f)
  use f '' B
  refine ⟨?_, Finite.Set.finite_image B ⇑f⟩
  refine ⟨Set.image_subset_iff.mpr hB.1, ?_⟩
  intro x hx
  obtain ⟨b, hb, hbx⟩ :=
    hB.2 (f.symm x) (by simp only [Set.mem_preimage, Equiv.apply_symm_apply, hx])
  use f b
  refine ⟨Set.mem_image_of_mem (⇑f) hb, ?_⟩
  convert hf hbx
  simp only [Equiv.apply_symm_apply]

theorem exists_lt_and_le_of_isDickson (H : isDickson α) (a : ℕ → α) :
    ∃ i j, i < j ∧ a i ≤ a j := by
  obtain ⟨B, hB, hB'⟩ := H (Set.range a)
  let B' : Set ℕ := a.invFun '' B
  have hB'' : Finite B' := Finite.Set.finite_image B (Function.invFun a)
  have : ∃ n, ∀ c ∈ B', c ≤ n := Set.exists_upper_bound_image B' (fun b ↦ b) hB''
  obtain ⟨n, hn⟩ := this
  obtain ⟨b, hb, hb'⟩ := hB.2 (a (n + 1)) (Set.mem_range_self _)
  use a.invFun b, n + 1
  constructor
  · apply Nat.lt_add_one_of_le
    exact hn _ (Set.mem_image_of_mem (Function.invFun a) hb)
  · convert hb'
    apply Function.invFun_eq
    rw [← Set.mem_range]
    exact hB.1 hb

-- TODO : Generalize to `PreOrder α`
-- This means that the conclusion should take place
-- in the quotient partial order associated with the preorder.
theorem minimal_ne_and_finite_of {α : Type*} [PartialOrder α]
    (H : ∀ a : ℕ → α, ∃ i j, i < j ∧ a i ≤ a j) (S : Set α) (hSne : S.Nonempty) :
    let M := {x ∈ S | Minimal (fun x ↦ x ∈ S) x}
    M.Nonempty ∧ M.Finite := by
  constructor
  · by_contra hM
    rw [Set.not_nonempty_iff_eq_empty] at hM
    by_cases hS : S.Finite
    · -- in a finite set, there are minimal elements
      obtain ⟨x, hx, hxm⟩ :=  Set.Finite.exists_minimal_wrt id S hS hSne
      simp only [Set.sep_eq_empty_iff_mem_false] at hM
      exact hM x hx (minimal_iff.mpr ⟨hx, hxm⟩)
    · have : ∀ x : S, ∃ y : S, (y : α) < x := by
        rintro ⟨x, hx⟩
        simp only [Set.sep_eq_empty_iff_mem_false] at hM
        by_contra hx'
        push_neg at hx'
        apply hM x hx
        unfold Minimal
        refine ⟨hx, ?_⟩
        intro y hy
        rw [le_iff_eq_or_lt]
        rintro (hyx | hyx)
        · exact le_of_eq hyx.symm
        · exfalso
          exact hx' ⟨y,hy⟩ hyx
      obtain ⟨a0, ha0⟩ := hSne
      let a : ℕ → S := Nat.rec ⟨a0, ha0⟩ fun _ x ↦ (this x).choose
      have ha : ∀ n, (a (n + 1)).val < (a n).val := fun n ↦ (this (a n)).choose_spec
      obtain ⟨i, j, H, H'⟩ := H (fun n ↦ (a n).val)
      rw [← lt_self_iff_false (a i)]
      exact lt_of_le_of_lt  H' (strictAnti_nat_of_succ_lt ha H)
  · rw [← Set.not_infinite]
    intro hM
    obtain ⟨a, ha⟩ := Set.Infinite.natEmbedding _ hM
    obtain ⟨i, j, h, H⟩ := H (fun n ↦ a n)
    simp only [Set.mem_setOf_eq, Subtype.coe_le_coe] at H
    exact ne_of_lt h <| ha <| le_antisymm H ((a j).prop.2.2 (a i).prop.1 H)

-- Unless the equivalence classes for the preorder are finite,
-- the assumption is often meaningless
-- TODO : Generalize to `PartialOrder α`
theorem isDickson_of_minimal_ne_and_finite
    (H : ∀ (S : Set α) (_ : S.Nonempty), { x ∈ S | Minimal (fun x ↦ x ∈ S) x}.Nonempty
        ∧ {x ∈ S | Minimal (fun x ↦ x ∈ S) x}.Finite) :
    isDickson α := by
  intro S
  let B := {x ∈ S | Minimal (fun x ↦ x ∈ S) x}
  have hBS : B ⊆ S := Set.sep_subset S (Minimal fun x ↦ x ∈ S)
  use B
  by_cases hS : S.Nonempty
  · refine ⟨⟨hBS, ?_⟩, (H S hS).2⟩
    intro a ha
    let S' := {x ∈ S | x ≤ a}
    have := H S' ⟨a, by simp [S', ha]⟩
    obtain ⟨b, hb, hb'⟩ := this.1
    refine ⟨b, ?_, hb.2⟩
    simp only [B]
    refine ⟨hb.1, ?_⟩
    refine ⟨Set.mem_of_mem_inter_left hb, ?_⟩
    intro y hy hyb
    exact hb'.2 ⟨hy, le_trans hyb hb.2⟩ hyb
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    have hB : B = ∅ := Set.subset_eq_empty hBS hS
    constructor
    exact ⟨hBS, by simp [hS]⟩
    simp [hB, Finite.of_fintype]

-- TODO : Generalize to `Preorder α`
/-- Becker-Weispfenning, Proposition 4.42 -/
theorem isDickson_tfae (α : Type*) [PartialOrder α] : List.TFAE [
    isDickson α,
    ∀ (a : ℕ → α), ∃ i j, i < j ∧ a i ≤ a j,
    ∀ (S : Set α) (_ : S.Nonempty), { x ∈ S | Minimal (fun x ↦ x ∈ S) x}.Nonempty
        ∧ {x ∈ S | Minimal (fun x ↦ x ∈ S) x}.Finite] := by
  tfae_have 1 → 2
  · exact exists_lt_and_le_of_isDickson
  tfae_have 2 → 3
  · exact  minimal_ne_and_finite_of
  tfae_have 3 → 1
  · exact isDickson_of_minimal_ne_and_finite
  tfae_finish

theorem isDickson_iff_exists_monotone (α : Type*) [PartialOrder α] :
    isDickson α ↔ ∀ (a : ℕ → α), ∃ (n : ℕ → ℕ), StrictMono n ∧ Monotone (a ∘ n) := by
  constructor
  · intro H a
    have H' : ∀ (S : Set ℕ) (_ : S.Infinite), ∃ s ∈ S, ∃ T,
        T.Infinite ∧ T ⊆ S ∧ (∀ t ∈ T, s < t ∧ a s ≤ a t):= by
      intro S hS
      obtain ⟨B, hB, hBf⟩ := H (a '' S)
      let f (b) := {n ∈ S | b ≤ a n}
      have : ⋃ b ∈ B, f b = S := by
        ext n
        constructor
        · simp only [Set.mem_iUnion, exists_prop, forall_exists_index, and_imp]
          intro b _ hn
          exact hn.1
        · intro hnS
          obtain ⟨b, hb, hb_le⟩:= hB.2 (a n) (Set.mem_image_of_mem a hnS)
          exact Set.mem_biUnion hb ⟨hnS, hb_le⟩
      have : ∃ b ∈ B, (f b).Infinite := by
        by_contra h
        push_neg at h
        simp only [Set.not_infinite] at h
        apply hS
        rw [← this]
        exact Set.Finite.biUnion' hBf h
      obtain ⟨b, hbB, hb⟩ := this
      obtain ⟨q, hqS, hqb⟩ := (Set.mem_image _ _ _).mpr (hB.1 hbB)
      use q, hqS, {n | n ∈ S ∧ b ≤ a n ∧ q < n}
      refine ⟨?_, Set.sep_subset S _, fun x ht ↦ ⟨ht.2.2, hqb ▸ ht.2.1⟩⟩
      -- this set is infinite
      simp_rw [← and_assoc]
      change ({n | n ∈ S ∧ b ≤ a n} ∩ {n | q < n}).Infinite
      rw [← Set.diff_compl]
      apply Set.Infinite.diff hb
      rw [Set.compl_setOf]
      simp_rw [not_lt]
      exact Set.finite_le_nat q
    obtain ⟨s0, _, S0, hS0⟩ := H' Set.univ Set.infinite_univ
    let v : ℕ → {(s, S) : ℕ × Set ℕ | S.Infinite ∧ ∀ x ∈ S, s < x ∧ a s ≤ a x} :=
      Nat.rec (⟨(s0, S0), ⟨hS0.1, hS0.2.2⟩⟩) (fun _ sS ↦ by
        let t := (H' sS.val.2 sS.prop.1).choose
        let T := (H' sS.val.2 sS.prop.1).choose_spec.2.choose
        let hT : T.Infinite ∧ T ⊆ sS.val.2 ∧ ∀ x ∈ T, t < x ∧ a t ≤ a x :=
          (H' sS.val.2 sS.prop.1).choose_spec.2.choose_spec
        exact ⟨(t, T), ⟨hT.1, hT.2.2⟩⟩)
    let n (k) := (v k).val.1
    let S (k) := (v k).val.2
    have hS (k) : (S k).Infinite := (v k).prop.1
    have hn (k) : ∀ x ∈ S k, n k < x ∧ a (n k) ≤ a x := (v k).prop.2
    have hn_mem_S (k) : n k.succ ∈ S k := (H' (S k) (hS k)).choose_spec.1
    use n
    constructor
    · apply strictMono_nat_of_lt_succ
      exact fun k ↦ (hn k (n (k + 1)) (hn_mem_S k)).1
    · apply monotone_nat_of_le_succ
      exact fun k ↦ (hn k (n (k + 1)) (hn_mem_S k)).2
  · intro H
    simp only [List.TFAE.out (isDickson_tfae _) 0 1]
    intro a
    obtain ⟨n, hn, han⟩ := H a
    exact ⟨n 0, n 1, hn Nat.one_pos, han (Nat.zero_le 1)⟩

/-
theorem wellFounded_iff_not_exists {α : Type*} (r : α → α → Prop) :
    WellFounded r ↔ ¬ ∃ (a : ℕ → α), ∀ n, r (a (n + 1)) (a n) := by
  constructor
  · intro H
    suffices ∀ a, ¬ ∃ (u : ℕ → α), u 0 = a ∧ ∀ n, r (u (n + 1)) (u n) by
      intro Ha
      obtain ⟨u, hu⟩ := Ha
      exact this (u 0) ⟨u, rfl, hu⟩
    intro  a
    induction a using WellFounded.induction H with
    | _ a Ha =>
    rintro ⟨u, hua, hu⟩
    apply Ha (u 1)
    simp only [← hua, hu 0]
    use fun n ↦ u (n + 1)
    simp only [zero_add, true_and]
    intro n
    exact hu (n + 1)
  · intro H
    apply WellFounded.intro
    intro a
    by_contra ha
    apply H
    let u : ℕ → {x | ¬ Acc r x} :=
      Nat.rec ⟨a, ha⟩ (fun _ x ↦ ⟨(RelEmbedding.exists_not_acc_lt_of_not_acc x.prop).choose,
        (RelEmbedding.exists_not_acc_lt_of_not_acc x.prop).choose_spec.1⟩)
    use fun n ↦ (u n).val
    intro n
    exact (RelEmbedding.exists_not_acc_lt_of_not_acc (u n).prop).choose_spec.2
-/

theorem WellFoundedLT.isDickson {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    isDickson α := fun S ↦ by
  by_cases hS : S.Nonempty
  · obtain ⟨a, haS, ha⟩ := WellFounded.has_min wellFounded_lt S hS
    use {a}
    constructor
    · unfold Set.isBasis
      constructor
      simp [haS]
      intro x hx
      use a
      simp_rw [not_lt] at ha
      simp [ha x hx]
    · exact Finite.of_fintype _
  · use ∅
    constructor
    unfold Set.isBasis
    constructor
    · exact Set.empty_subset S
    · simp only [Set.not_nonempty_iff_eq_empty] at hS
      simp [hS]
    exact Finite.of_fintype _

theorem isDickson.wf {α : Type*} [PartialOrder α] (H : isDickson α) : WellFoundedLT α := by
  unfold WellFoundedLT
  apply IsWellFounded.mk
  rw [RelEmbedding.wellFounded_iff_no_descending_seq]
  apply IsEmpty.mk
  rintro ⟨a, ha⟩
  have := List.TFAE.out (isDickson_tfae α) 0 1
  rw [this] at H
  obtain ⟨i, j, hij, H⟩ := H a
  exact ne_of_lt (lt_of_le_of_lt H (ha.mpr hij)) rfl

theorem Finsupp.isDickson_equiv {α β : Type*} (e : α ≃ β) (hα : isDickson (α →₀ ℕ)) :
    isDickson (β →₀ ℕ) := by
  apply Equiv.isDickson_of_monotone (equivCongrLeft e) _ hα
  exact fun a b h d ↦ by simp [h (e.symm d)]

theorem isDickson_prod {α β : Type*} [PartialOrder α] [PartialOrder β]
    (hα : isDickson α) (hβ : isDickson β) :
    isDickson (α × β) := by
  simp only [List.TFAE.out (isDickson_tfae _) 0 1]
  intro a
  simp only [isDickson_iff_exists_monotone] at hα hβ
  obtain ⟨m, hm, ha1⟩ := hα (fun k ↦ (a k).1)
  obtain ⟨n, hn, ha2⟩ := hβ (fun k ↦ (a (m k)).2)
  use m (n 0), m (n 1)
  constructor
  exact hm (hn zero_lt_one)
  simp only [Prod.le_def]
  constructor
  · apply ha1
    exact hn.monotone zero_le_one
  · apply ha2 zero_le_one

theorem Nat.isDickson : isDickson ℕ := WellFoundedLT.isDickson

theorem Fin.isDickson_nat (n : ℕ) : isDickson (Fin n → ℕ) := by
  induction n with
  | zero => exact fun S ↦ ⟨S,⟨⟨subset_rfl, fun x hx ↦ ⟨x, hx, le_rfl⟩⟩, Subtype.finite⟩⟩
  | succ n h =>
      apply Equiv.isDickson_of_monotone (Fin.snocEquiv (fun _ ↦ ℕ))
      · intro a b h i
        rw [Prod.le_def] at h
        simp only [snocEquiv_apply]
        rcases i.eq_castSucc_or_eq_last with (hi | hi)
        · obtain ⟨j, rfl⟩ := hi
          simp only [snoc_castSucc, ge_iff_le, h.2 j]
        · simp only [hi, snoc_last, h.1]
      · exact isDickson_prod Nat.isDickson h

theorem Finsupp.isDickson_nat (n : ℕ) : isDickson (Fin n →₀ ℕ) := by
  let e : (Fin n → ℕ) ≃ (Fin n →₀ ℕ) := equivFunOnFinite.symm
  apply Equiv.isDickson_of_monotone e (fun x y h i ↦ by exact h i) (Fin.isDickson_nat n)

theorem Finsupp.isDickson (σ : Type*) [Finite σ] : isDickson (σ →₀ ℕ) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  exact Finsupp.isDickson_equiv e.symm (Finsupp.isDickson_nat n)

end Dickson

