import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Order.SuccPred.Basic

namespace SimpleGraph

open Walk

variable {V : Type*} {G : SimpleGraph V}

set_option linter.unusedVariables false in
def IsTree.rootedAt (hG : G.IsTree) (v : V) : Type _ := V

lemma List.IsPrefix.antisymm {α : Type*} {l₁ l₂ : List α} (h₁ : l₁ <+: l₂) (h₂ : l₂ <+: l₁) :
    l₁ = l₂ := h₁.eq_of_length (le_antisymm h₁.length_le h₂.length_le)

lemma IsAcyclic.IsPrefix_of_mem_support (hG : G.IsAcyclic) {a b c : V} (w₁ : G.Walk a b)
    (w₂ : G.Walk a c) (h₁ : w₁.IsPath) (h₂ : w₂.IsPath) (h : b ∈ w₂.support) :
    w₁.support <+: w₂.support := by classical
  rw [← take_spec _ h, support_append]
  convert List.prefix_append _ _
  convert_to (⟨_, h₂.takeUntil h⟩ : G.Path _ _) = (⟨w₁, h₁⟩ : G.Path _ _)
  · simp only [Subtype.mk.injEq]
  apply hG.path_unique

instance (hG : G.IsTree) (v : V) : PartialOrder (hG.rootedAt v) where
  le a b := a ∈ (hG.existsUnique_path v b).choose.support
  le_refl a := by simp
  le_trans a b c hab hbc := by classical
    dsimp at *
    have := hG.IsAcyclic.IsPrefix_of_mem_support (hG.existsUnique_path v b).choose
      (hG.existsUnique_path v c).choose (hG.existsUnique_path v b).choose_spec.1
      (hG.existsUnique_path v c).choose_spec.1 hbc
    apply this.subset hab
  le_antisymm a b hab hba := by
    dsimp at *
    rw [← support_getLast (hG.existsUnique_path v a).choose,
      ← support_getLast (hG.existsUnique_path v b).choose]
    congr 1
    apply List.IsPrefix.antisymm
    · apply hG.IsAcyclic.IsPrefix_of_mem_support
      exact (hG.existsUnique_path v a).choose_spec.1
      exact (hG.existsUnique_path v b).choose_spec.1
      exact hab
    · apply hG.IsAcyclic.IsPrefix_of_mem_support
      exact (hG.existsUnique_path v b).choose_spec.1
      exact (hG.existsUnique_path v a).choose_spec.1
      exact hba

lemma IsTree.rootedAt.le_iff (hG : G.IsTree) (v : V) (a b : hG.rootedAt v) :
  a ≤ b ↔ a ∈ (hG.existsUnique_path v b).choose.support := Iff.rfl

lemma dist_lt_of_lt (hG : G.IsTree) (v : V) (a b : hG.rootedAt v) (h : a < b) :
    G.dist v a < G.dist v b := by

  sorry

instance (hG : G.IsTree) (v : V) : OrderBot (hG.rootedAt v) where
  bot := v
  bot_le a := by simp only [IsTree.rootedAt.le_iff, start_mem_support]

def Walk.penultimate {v u : V} : G.Walk v u → V
| nil => v
| cons hadj nil => v
| cons _ p => p.penultimate

def Walk.dropLast {v u : V} : (p : G.Walk v u) → G.Walk v p.penultimate
| nil => nil
| cons hadj nil => nil
| cons hadj p@(cons _ _) => cons hadj (p.dropLast.copy rfl (by simp [Walk.penultimate, *]))

lemma Walk.penultimate_adj {v w : V} (p : G.Walk v w) (hp : ¬p.Nil) :
    G.Adj p.penultimate w := by
  induction p with
  | nil => simp at hp
  | cons hadj p hind =>
    match p with
    | nil => simpa [Walk.penultimate]
    | cons hadj2 p => simp [Walk.penultimate, hind]

lemma Nil_of_penultimate_eq {v w : V} {p : G.Walk v w} (h : p.penultimate = w) : p.Nil := by
  by_contra! nh
  exact G.irrefl (h ▸ p.penultimate_adj nh)

lemma Walk.penultimate_mem_support {v w : V} (p : G.Walk v w) : p.penultimate ∈ p.support := by
  induction p with
  | nil => simp [Walk.penultimate]
  | cons hadj p hind =>
    match p with
    | nil => simp [Walk.penultimate]
    | cons hadj2 p =>
      simp only [support_cons, List.mem_cons] at hind
      simp [Walk.penultimate, hind]

lemma Walk.dropLast_concat {v w : V} (p : G.Walk v w) (hp : ¬p.Nil) :
    p.dropLast.concat (p.penultimate_adj hp) = p := by
  induction p with
  | nil => simp at hp
  | cons hadj p hind =>
    cases p with
    | nil => rw [Walk.dropLast]; rfl
    | cons hadj2 p =>
      simp only [dropLast, copy_rfl_rfl, concat_cons, cons.injEq, heq_eq_eq, true_and]
      apply hind
      simp

lemma Walk.IsPath.dropLast {v w : V} {p : G.Walk v w} (hp : p.IsPath) :
    p.dropLast.IsPath := by
  cases p with
  | nil =>
    simp [Walk.dropLast]
  | cons hadj p =>
    rw [← Walk.dropLast_concat (cons hadj p) (by simp), concat_eq_append] at hp
    exact hp.of_append_left

noncomputable instance (hG : G.IsTree) (v : V) : PredOrder (hG.rootedAt v) where
  pred a := (hG.existsUnique_path v a).choose.penultimate
  pred_le a := penultimate_mem_support _
  min_of_le_pred {a} ha := by
    dsimp at ha
    simp only [isMin_iff_eq_bot]
    replace ha := ha.antisymm (penultimate_mem_support _)
    replace ha := (Nil_of_penultimate_eq ha.symm).eq
    exact ha.symm
  le_pred_of_lt {a b} hab := by
    dsimp
    rw [lt_iff_le_and_ne] at hab
    rw [IsTree.rootedAt.le_iff] at *
    obtain ⟨h, hab⟩ := hab
    have : ¬ (hG.existsUnique_path v b).choose.Nil := fun nh ↦ by
      replace nh : (hG.existsUnique_path v b).choose.support = [b] := by
        rw [nil_iff_support_eq.mp nh, nh.eq]
      rw [nh] at h
      simp at h
      contradiction
    rw [← (hG.existsUnique_path v b).choose.dropLast_concat this] at h
    simp only [support_concat, List.concat_eq_append, List.mem_append, List.mem_singleton, hab,
      or_false] at h
    convert h
    apply ((hG.existsUnique_path v _).choose_spec.2 ..).symm
    exact (hG.existsUnique_path v b).choose_spec.1.dropLast

-- instance (hG : G.IsTree) (v : V) : IsPredArchimedean (hG.rootedAt v) where
--   exists_pred_iterate_of_le {a b} hab := by

--     sorry
