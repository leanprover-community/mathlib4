/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
public import Mathlib.AlgebraicTopology.SimplicialSet.NonemptyFiniteChains

/-!
# ...

-/

universe u

@[expose] public section

open CategoryTheory SSet Simplicial

namespace PartialOrder.NonemptyFiniteChains

variable {X : Type u} [LinearOrder X] {x₀ : X}

namespace horn

namespace pairingCore

variable (x₀) in
def IsIndexI {dim : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋dim⦌) (i : Fin (dim + 1)) : Prop :=
  match i with
  | ⟨0, _⟩ => (s.obj 0).finset = {x₀}
  | ⟨k + 1, hk⟩ => (s.obj ⟨k + 1, hk⟩).finset =
      (s.obj ⟨k, (lt_add_one k).trans hk⟩).finset ∪ {x₀}

variable (x₀) in
lemma congr_isIndexI
    {dim dim' : ℕ} {s : (nerve (NonemptyFiniteChains X)) _⦋dim⦌}
    {s' : (nerve (NonemptyFiniteChains X)) _⦋dim'⦌}
    (hs : S.mk s = S.mk s') (i : Fin (dim + 1)) :
    IsIndexI x₀ s i ↔ IsIndexI x₀ s' ⟨i, by grind⟩ := by
  obtain rfl : dim = dim' := by grind
  obtain rfl : s = s' := by grind
  rfl

@[simp]
lemma isIndexI_zero {dim : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋dim⦌) :
    IsIndexI x₀ s 0 ↔ (s.obj 0).finset = {x₀} := Iff.rfl

@[simp]
lemma isIndexI_succ {dim : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋dim⦌) (i : Fin dim) :
    IsIndexI x₀ s i.succ ↔
      (s.obj i.succ).finset = (s.obj i.castSucc).finset ∪ {x₀} := Iff.rfl

namespace IsIndexI

variable {dim : ℕ} {s : (nerve (NonemptyFiniteChains X)) _⦋dim⦌} {i : Fin (dim + 1)}

lemma mem (hi : IsIndexI x₀ s i) : x₀ ∈ (s.obj i).finset := by
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simp only [isIndexI_zero] at hi
    simp [hi]
  · simp only [isIndexI_succ, Finset.union_singleton] at hi
    simp [hi]

lemma mem_of_ge (hi : IsIndexI x₀ s i) (j : Fin (dim + 1)) (hj : i ≤ j := by lia) :
    x₀ ∈ (s.obj j).finset :=
  s.monotone hj hi.mem

lemma notMem_of_lt
    (hi : IsIndexI x₀ s i) (hs : s ∈ (nerve (NonemptyFiniteChains X)).nonDegenerate dim)
    (j : Fin (dim + 1)) (hj : j < i := by grind) :
    x₀ ∉ (s.obj j).finset := by
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simp at hj
  · simp only [isIndexI_succ, Finset.union_singleton] at hi
    suffices x₀ ∉ (s.obj i.castSucc).finset from
      fun h ↦ this ((s.monotone (by grind)) h)
    intro h
    exact ((mem_nerve_nonDegenerate_iff_strictMono s).1 hs i.castSucc_lt_succ).not_ge (by aesop)

lemma not_isIndexI_of_ne (hi : IsIndexI x₀ s i)
    (hs : s ∈ (nerve (NonemptyFiniteChains X)).nonDegenerate dim) (j : Fin (dim + 1))
    (hij : i ≠ j) :
    ¬ IsIndexI x₀ s j := by
  intro hj
  wlog h : i < j generalizing i j
  · exact this hj i hij.symm hi (by lia)
  exact hj.notMem_of_lt hs i h hi.mem

lemma dim_ne_zero [Fintype X] [Nontrivial X] (hi : IsIndexI x₀ s i)
    (hs : s ∉ (horn x₀).obj _) : dim ≠ 0 := by
  rw [notMem_horn_iff] at hs
  rintro rfl
  fin_cases i
  aesop

end IsIndexI

section

variable {dim : ℕ} {s : (nerve (NonemptyFiniteChains X)) _⦋dim⦌}

variable (x₀ s) in
def finsetMem : Finset (Fin (dim + 1)) := { i | x₀ ∉ (s.obj i).finset }

lemma mem_finsetMem_iff (i : Fin (dim + 1)) :
    i ∈ finsetMem x₀ s ↔ x₀ ∉ (s.obj i).finset := by
  simp [finsetMem]

lemma notMem_finsetMem_iff (i : Fin (dim + 1)) :
    i ∉ finsetMem x₀ s ↔ x₀ ∈ (s.obj i).finset := by
  simp [mem_finsetMem_iff]

lemma mem_finsetMem_of_le {j : Fin (dim + 1)} (hj : j ∈ finsetMem x₀ s)
    (i : Fin (dim + 1)) (hij : i ≤ j) :
    i ∈ finsetMem x₀ s := by
  rw [mem_finsetMem_iff] at hj ⊢
  intro hi
  exact hj (s.monotone hij hi)

variable [Fintype X] [Nontrivial X]
  (hs : ∀ i, ¬ IsIndexI x₀ s i)
  (notMem : s ∉ (horn x₀).obj _)
  (nonDeg : s ∈ (nerve (NonemptyFiniteChains X)).nonDegenerate dim)

/-

...

-/

end

variable [Fintype X] [Nontrivial X]


variable (x₀) in
structure ι where
  dim : ℕ
  simplex : nerve (NonemptyFiniteChains X) _⦋dim + 1⦌
  notMem₁ : simplex ∉ (horn x₀).obj _
  nonDegenerate₁ : simplex ∈ (nerve (NonemptyFiniteChains X)).nonDegenerate (dim + 1)
  index : Fin (dim + 2)
  isIndexI : IsIndexI x₀ simplex index

namespace ι

variable (σ : ι x₀)

lemma strictMono : StrictMono σ.simplex.obj := by
  rw [← mem_nerve_nonDegenerate_iff_strictMono]
  exact σ.nonDegenerate₁

def simplex₂ : nerve (NonemptyFiniteChains X) _⦋σ.dim⦌ :=
  (nerve (NonemptyFiniteChains X)).δ σ.index σ.simplex

lemma simplex₂_def : σ.simplex₂ = (nerve (NonemptyFiniteChains X)).δ σ.index σ.simplex := rfl

lemma nonDegenerate₂ : σ.simplex₂ ∈ (nerve (NonemptyFiniteChains X)).nonDegenerate σ.dim :=
  nonDegenerate_δ σ.nonDegenerate₁ _

lemma mem : x₀ ∈ (σ.simplex.obj σ.index).finset :=
  σ.isIndexI.mem

lemma mem_of_ge (i : Fin (σ.dim + 2)) (hi : σ.index ≤ i := by grind) :
    x₀ ∈ (σ.simplex.obj i).finset :=
  σ.isIndexI.mem_of_ge i hi

lemma notMem_of_lt (i : Fin (σ.dim + 2)) (hi : i < σ.index := by grind) :
    x₀ ∉ (σ.simplex.obj i).finset :=
  σ.isIndexI.notMem_of_lt σ.nonDegenerate₁ i hi

lemma mem_iff (i : Fin (σ.dim + 2)) :
    x₀ ∈ (σ.simplex.obj i).finset ↔ σ.index ≤ i := by
  by_cases! hi : σ.index ≤ i
  · simp [σ.mem_of_ge i, hi]
  · simp [σ.notMem_of_lt i, hi]

lemma obj_simplex_castSucc_last_eq
    (hσ : σ.index = Fin.last (σ.dim + 1)) :
    σ.simplex.obj (Fin.last σ.dim).castSucc = complSingleton x₀ := by
  have h₁ := σ.isIndexI
  rw [hσ, ← Fin.succ_last, isIndexI_succ, ] at h₁
  have h₂ := σ.strictMono (Fin.castSucc_lt_succ (i := Fin.last _))
  rw [NonemptyFiniteChains.lt_iff, Finset.ssubset_iff] at h₂
  obtain ⟨x, hx₁, hx₂⟩ := h₂
  rw [Finset.insert_eq, Finset.union_subset_iff, Finset.singleton_subset_iff, h₁] at hx₂
  obtain rfl : x₀ = x := by grind
  have h₃ := σ.notMem₁
  rw [notMem_horn_iff, NonemptyFiniteChains.le_iff, ← Fin.succ_last] at h₃
  rw [NonemptyFiniteChains.ext_iff]
  exact subset_antisymm (by aesop) (fun y hy ↦ by have := h₃ hy; aesop)

lemma notMem₂ : σ.simplex₂ ∉ (horn x₀).obj _ := by
  rw [simplex₂_def, notMem_horn_iff, nerve.δ_obj]
  by_cases hσ : σ.index = Fin.last _
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by grind),
      σ.obj_simplex_castSucc_last_eq hσ]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by grind),
      Fin.succ_last, ← notMem_horn_iff]
    exact σ.notMem₁

lemma injective_type₁ {σ σ' : ι x₀} (hσ : S.mk σ.simplex = S.mk σ'.simplex) :
    σ = σ' := by
  suffices σ.index.val = σ'.index.val by cases σ; cases σ'; aesop
  obtain ⟨dim, s, notMem, nonDeg, index, h⟩ := σ
  obtain ⟨dim', s', _, _, index', h'⟩ := σ'
  obtain rfl : dim = dim' := by grind
  obtain rfl : s = s' := by grind
  obtain rfl : index = index' := by
    by_contra!
    exact h.not_isIndexI_of_ne nonDeg index' this h'
  rfl

lemma not_isIndexI_simplex₂ (i : Fin (σ.dim + 1)) :
    ¬ (IsIndexI x₀ σ.simplex₂ i) := by
  intro hσ
  rw [simplex₂_def] at hσ
  have hi : i.castSucc = σ.index := by
    have h₁ := hσ.mem
    rw [nerve.δ_obj, σ.mem_iff] at h₁
    obtain hi | hi | hi := lt_trichotomy i.castSucc σ.index
    · rw [Fin.succAbove_of_castSucc_lt _ _ hi] at h₁
      grind
    · exact hi
    · exfalso
      obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero (by grind)
      apply hσ.notMem_of_lt σ.nonDegenerate₂ i.castSucc Fin.castSucc_lt_succ
      rw [nerve.δ_obj, σ.mem_iff, Fin.succAbove_of_lt_succ _ _ (by grind)]
      grind
  rw [← hi] at hσ
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · rw [Fin.castSucc_zero, isIndexI_zero, nerve.δ_obj,
      Fin.zero_succAbove, Fin.succ_zero_eq_one] at hσ
    have := Finset.nonempty_def.1 (σ.simplex.obj 0).nonempty
    have := σ.strictMono (show 0 < 1 by simp)
    aesop
  · rw [isIndexI_succ, nerve.δ_obj, nerve.δ_obj,
      Fin.succAbove_of_le_castSucc _ _ (by grind),
      Fin.succAbove_of_castSucc_lt _ _ (by grind)] at hσ
    have := σ.isIndexI
    rw [← hi, Fin.castSucc_succ, isIndexI_succ, ← hσ] at this
    exact this.not_lt (σ.strictMono (by grind))

lemma type₁_ne_type₂ (σ σ' : ι x₀) : S.mk σ.simplex ≠ S.mk σ'.simplex₂ := by
  intro hσ
  have := σ.isIndexI
  rw [congr_isIndexI x₀ hσ] at this
  exact σ'.not_isIndexI_simplex₂ _ this

lemma injective_type₂ {σ σ' : ι x₀} (hσ : S.mk σ.simplex₂ = S.mk σ'.simplex₂) :
    σ = σ' := by
  sorry

end ι

end pairingCore

variable (x₀)

variable [Fintype X] [Nontrivial X]

open pairingCore in
@[implicit_reducible]
def pairingCore : (horn x₀).PairingCore where
  ι := ι x₀
  dim := ι.dim
  simplex := ι.simplex
  index := ι.index
  nonDegenerate₁ := ι.nonDegenerate₁
  nonDegenerate₂ := ι.nonDegenerate₂
  notMem₁ := ι.notMem₁
  notMem₂ := ι.notMem₂
  injective_type₁' := ι.injective_type₁
  injective_type₂' := ι.injective_type₂
  type₁_ne_type₂' := ι.type₁_ne_type₂
  surjective' := sorry

def pairingCore.weakRankFunction : (pairingCore x₀).WeakRankFunction ℕ := sorry

instance : (pairingCore x₀).IsRegular := by
  rw [(pairingCore x₀).isRegular_iff_nonempty_weakRankFunction]
  exact ⟨pairingCore.weakRankFunction x₀⟩

end horn

end PartialOrder.NonemptyFiniteChains
