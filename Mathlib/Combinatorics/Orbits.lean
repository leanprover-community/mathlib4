/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Order.Partition.Finpartition

/-!
# Orbits of function

The file has some results about orbits of functions, or equivalently cycles in the corresponding
functional graph.


--/

namespace Orbit

open Function

variable {α : Type*} (f : α → α) (a b c : α) (i : ℕ)

/--
We say that `b` is reachable from `a` using `f`, and write `a ⇝[f] b`, if `f^i(a) = b` for some `i`.
-/
def Reachable : Prop := ∃ i : ℕ, f^[i] a = b

@[inherit_doc]
scoped notation:75 a:50 " ⇝[" f "] " b:50 => Reachable f a b

lemma reachable_def : a ⇝[f] b ↔ ∃ i : ℕ, f^[i] a = b := .rfl

@[simp, refl]
lemma reachable_rfl : a ⇝[f] a := ⟨0, rfl⟩

@[simp]
lemma reachable_iterate : a ⇝[f] f^[i] a := ⟨i, rfl⟩

@[simp]
lemma reachable_apply : a ⇝[f] f a := ⟨1, rfl⟩

lemma reachable_trans (hab : a ⇝[f] b) (hbc : b ⇝[f] c) : a ⇝[f] c := by
  obtain ⟨i, rfl⟩ := hab
  obtain ⟨j, rfl⟩ := hbc
  simp [← iterate_add_apply]

instance {α : Type*} (f : α → α) : IsPreorder α (· ⇝[f] ·) where
  refl a := by rfl
  trans a b c ha hb := by
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    simp [← Function.iterate_add_apply]

lemma reachable_of_reachable_of_nontrivial (h : a ≠ b) (hab : a ⇝[f] b) (hba : b ⇝[f] a)
    (hac : a ⇝[f] c) : c ⇝[f] a := by
  obtain ⟨i, rfl⟩ := hab
  have ine : i ≠ 0 := fun nh ↦ by simp [nh] at h
  obtain ⟨j, hba⟩ := hba
  rw [← Function.iterate_add_apply] at hba
  obtain ⟨k, rfl⟩ := hac
  use j + i - k % (j + i)
  rw [← Function.iterate_add_apply]
  obtain ⟨l, hl⟩ : j + i ∣ j + i - k % (j + i) + k := by
    rw [← Nat.sub_add_comm, Nat.add_sub_assoc]
    · simp only [Nat.dvd_add_self_left, Nat.dvd_sub_mod]
    · apply Nat.mod_le
    · apply le_of_lt
      apply Nat.mod_lt
      omega
  rw [hl, Function.iterate_mul]
  apply Function.iterate_fixed hba

lemma reachable_iff_reachable_small {α : Type*} [Fintype α] (f : α → α) (a b : α) :
    a ⇝[f] b ↔ ∃ i < Fintype.card α, f^[i] a = b where
  mp hr := by
    obtain ⟨m, n, hmn, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun v : Fin (Fintype.card α + 1) ↦ f^[v] a) (by simp)
    wlog hmn : n < m
    · exact this f a b hr n m (by omega) h.symm (by omega)
    obtain ⟨i, hi⟩ := hr
    obtain ⟨j, hj, h⟩ := Function.iterate_exists_loop h hmn i
    use j
    simp only [← h, hi, and_true]
    omega
  mpr h := h.elim (fun a ha ↦ ⟨a, ha.2⟩)

instance {α : Type*} [Fintype α] [DecidableEq α] (f : α → α) : DecidableRel (· ⇝[f] ·) :=
  fun a b ↦ decidable_of_iff' _ (reachable_iff_reachable_small f a b)

section Orbits

variable [Fintype α] [DecidableEq α]

def orbits : Finpartition (Finset.univ : Finset α) :=
  .ofSetoid (AntisymmRel.setoid _ (· ⇝[f] ·))

lemma orbits_congr' {α : Type*} [Fintype α] [DecidableEq α] (f g : α → α) (s : Finset α)
    (hs : s.card ≠ 1) (hfg : ∀ x ∈ s, f x = g x) (hf : s ∈ (orbits f).parts) :
    s ∈ (orbits g).parts := by
  rcases hs.lt_or_lt  with hs | hs
  · simp_all [← Finset.bot_eq_empty]
  rw [Finset.one_lt_card_iff_nontrivial] at hs
  obtain ⟨x, hx⟩ := hs.nonempty
  rw [Finset.mem_coe] at hx
  obtain rfl := Finpartition.part_eq_of_mem _ hf hx
  clear hf hx
  suffices (scc f).part x = (scc g).part x by simp [this]
  ext z
  have := scc_part_eq_orbit_of_nontrivial f x hs
  rw [← Finset.mem_coe, this]
  simp_rw [← Finset.mem_coe, this] at hfg
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hfg
  simp only [Set.mem_setOf_eq]

  sorry

lemma scc_congr {α : Type*} [Fintype α] [DecidableEq α] (f g : α → α) (s : Finset α)
    (hs : s.card ≠ 1) (hfg : ∀ x ∈ s, f x = g x) : s ∈ (scc f).parts ↔ s ∈ (scc g).parts := by
  constructor <;> apply scc_congr' <;> simp_all

end Orbits

section Perm

variable {a b}

lemma Reachable.sameCycle {f : Equiv.Perm α} (hab : a ⇝[f] b) :
    f.SameCycle a b := by
  obtain ⟨a, rfl⟩ := hab
  simp [Equiv.Perm.SameCycle.refl]

section Finite

variable [Finite α]

lemma _root_.Equiv.Perm.SameCycle.reachable {f : Equiv.Perm α} (hab : f.SameCycle a b) :
    a ⇝[f] b := by
  rw [Equiv.Perm.SameCycle.iff_exists_pow_eq] at hab
  obtain ⟨i, _, rfl⟩ := hab
  simp [← Equiv.Perm.iterate_eq_pow]

lemma sameCycle_iff_reachable {f : Equiv.Perm α} :
    f.SameCycle a b ↔ a ⇝[f] b := ⟨(·.reachable), (·.sameCycle)⟩

lemma Reachable.symm {f : Equiv.Perm α} (hab : a ⇝[f] b) : b ⇝[f] a :=
  hab.sameCycle.symm.reachable

lemma perm_reachable_comm {f : Equiv.Perm α} :
    a ⇝[f] b ↔ b ⇝[f] a := ⟨(·.symm), (·.symm)⟩

end Finite

section Orbits

variable [Fintype α] [DecidableEq α]

lemma _root_.Equiv.Perm.mem_orbits_iff
    {α : Type*} [Fintype α] [DecidableEq α] (f : Equiv.Perm α) (s : Finset α) :
    s ∈ (orbits f).parts ↔ s.Nonempty ∧ f.IsCycleOn s where
  mp h := by
    constructor
    · rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp only [← Finset.bot_eq_empty, Finpartition.not_bot_mem] at h
    · constructor
      · convert f.symm.bijOn_symm_image
        ext y
        simp only [Finset.mem_coe, Set.mem_image_equiv, Equiv.symm_symm]
        constructor <;> {
          intro hy
          rw [Finpartition.mem_iff_rel_of_mem_parts h hy]
          simp only [AntisymmRel.setoid_r, AntisymmRel, reachable_apply, true_and, and_true]
          use orderOf f - 1
          rw [← Function.iterate_succ_apply,
            show (orderOf f - 1).succ = orderOf f from Nat.succ_pred (orderOf_pos f).ne']
          simp [pow_orderOf_eq_one]
        }
      · intro a ha b hb
        rw [Finset.mem_coe] at ha hb
        exact ((Finpartition.mem_iff_rel_of_mem_parts h ha).1 hb).1.sameCycle
  mpr h := by
    obtain ⟨⟨x, hx⟩, h⟩ := h
    suffices s = (orbits f).part x by simp [this]
    ext y
    simp only [h.exists_pow_eq_iff hx, ← Equiv.Perm.iterate_eq_pow, ← reachable_def, ←
      sameCycle_iff_reachable, orbits, Finpartition.mem_part_ofSetoid_iff_rel, AntisymmRel.setoid_r,
      AntisymmRel, Equiv.Perm.sameCycle_comm, and_self]

end Orbits

end Perm

end Orbit
