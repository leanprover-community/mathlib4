/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
public import Mathlib.AlgebraicTopology.SimplicialSet.NonemptyFiniteChains
public import Mathlib.Order.Interval.Finset.Fin

/-!
# ...

-/

universe u

@[expose] public section

open CategoryTheory SSet Simplicial

@[simp]
lemma Fin.predAbove_succAbove_succ {n : ℕ} (i j : Fin (n + 1)) :
    i.predAbove (i.succ.succAbove j) = j := by
  by_cases hi : j ≤ i
  · rw [Fin.succAbove_of_succ_le _ _ (by grind),
      Fin.predAbove_of_le_castSucc _ _ (by grind)]
    simp
  · rw [Fin.succAbove_of_lt_succ _ _ (by grind),
      Fin.predAbove_of_succ_le _ _ (by grind)]
    simp

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
def finsetNotMem : Finset (Fin (dim + 1)) := { i | x₀ ∉ (s.obj i).finset }

variable (x₀) in
lemma congr_finsetNotMem_card {dim' : ℕ} {s' : (nerve (NonemptyFiniteChains X)) _⦋dim'⦌}
    (h : S.mk s = S.mk s') :
    (finsetNotMem x₀ s).card = (finsetNotMem x₀ s').card := by
  obtain rfl : dim = dim' := by grind
  obtain rfl : s = s' := by grind
  rfl

lemma mem_finsetNotMem_iff (i : Fin (dim + 1)) :
    i ∈ finsetNotMem x₀ s ↔ x₀ ∉ (s.obj i).finset := by
  simp [finsetNotMem]

lemma notMem_finsetNotMem_iff (i : Fin (dim + 1)) :
    i ∉ finsetNotMem x₀ s ↔ x₀ ∈ (s.obj i).finset := by
  simp [mem_finsetNotMem_iff]

lemma mem_finsetNotMem_of_le {j : Fin (dim + 1)} (hj : j ∈ finsetNotMem x₀ s)
    (i : Fin (dim + 1)) (hij : i ≤ j) :
    i ∈ finsetNotMem x₀ s := by
  rw [mem_finsetNotMem_iff] at hj ⊢
  intro hi
  exact hj (s.monotone hij hi)

variable (x₀ s) in
lemma finsetNotMem_eq_empty_or :
    finsetNotMem x₀ s = ∅ ∨
      ∃ (i : Fin (dim + 1)), finsetNotMem x₀ s = Finset.Iic i := by
  by_cases! hs : finsetNotMem x₀ s = ∅
  · exact Or.inl hs
  · refine Or.inr ⟨(finsetNotMem x₀ s).max' hs, ?_⟩
    ext j
    simp only [Finset.mem_Iic]
    exact ⟨fun hj ↦ (finsetNotMem x₀ s).le_max' j hj,
      fun hj ↦ mem_finsetNotMem_of_le (Finset.max'_mem _ _) _ hj⟩

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

@[implicit_reducible, simps dim]
def cast {dim' : ℕ} (h : σ.dim = dim') : ι x₀ where
  dim := dim'
  simplex := _root_.cast (by subst h; rfl) σ.simplex
  notMem₁ := by subst h; exact σ.notMem₁
  nonDegenerate₁ := by subst h; exact σ.nonDegenerate₁
  index := Fin.cast (by simp [h]) σ.index
  isIndexI := by subst h; exact σ.isIndexI

lemma cast_eq_self {dim' : ℕ} (h : σ.dim = dim') :
    σ.cast h = σ := by
  subst h; rfl

lemma strictMono : StrictMono σ.simplex.obj := by
  rw [← mem_nerve_nonDegenerate_iff_strictMono]
  exact σ.nonDegenerate₁

def simplex₂ : nerve (NonemptyFiniteChains X) _⦋σ.dim⦌ :=
  (nerve (NonemptyFiniteChains X)).δ σ.index σ.simplex

lemma simplex₂_def : σ.simplex₂ = (nerve (NonemptyFiniteChains X)).δ σ.index σ.simplex := rfl

lemma simplex₂_cast {dim' : ℕ} (h : σ.dim = dim') :
    S.mk (σ.cast h).simplex₂ = S.mk σ.simplex₂ := by
  subst h
  rfl

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

lemma finsetNotMem_simplex₂ :
    finsetNotMem x₀ σ.simplex₂ = Finset.filter (fun i ↦ i.castSucc < σ.index) .univ := by
  ext j
  simp [simplex₂_def, mem_finsetNotMem_iff, nerve.δ_obj.{u}, σ.mem_iff]

lemma index_coe_eq_card (σ : ι x₀) :
    σ.index.val = (finsetNotMem x₀ σ.simplex₂).card := by
  rw [finsetNotMem_simplex₂]
  obtain ⟨i, hi⟩ | hσ := σ.index.eq_castSucc_or_eq_last
  · simp only [hi, Fin.val_castSucc, Fin.castSucc_lt_castSucc_iff]
    rw [← Fin.card_Iio]
    congr 1
    grind
  · simp [hσ]

lemma injective_type₂ {σ σ' : ι x₀} (hσ : S.mk σ.simplex₂ = S.mk σ'.simplex₂) :
    σ = σ' := by
  have hdim : σ.dim = σ'.dim := by grind
  let σ₀ := σ.cast hdim
  suffices σ₀ = σ' by rwa [← σ.cast_eq_self hdim]
  replace hσ : σ₀.simplex₂ = σ'.simplex₂ := by
    rwa [← σ.simplex₂_cast hdim, S.ext_iff] at hσ
  have hindex : σ₀.index = σ'.index := by
    ext
    simp only [index_coe_eq_card, hσ]
  have hsimplex : σ₀.simplex = σ'.simplex := by
    ext i : 2
    dsimp at i
    wlog! hi : i ≠ σ₀.index generalizing i
    · have h₀ := σ₀.isIndexI
      have h' := σ'.isIndexI
      simp only [← hi, ← hindex] at h₀ h'
      rw [NonemptyFiniteChains.ext_iff]
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · rw [isIndexI_zero] at h₀ h'
        rw [h₀, h']
      · rw [isIndexI_succ] at h₀ h'
        rw [h₀, h', this i.castSucc (by grind)]
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    replace hσ := congr($(hσ).obj j)
    rwa [simplex₂_def, simplex₂_def, nerve.δ_obj, nerve.δ_obj, ← hindex] at hσ
  exact injective_type₁ (by simp [hsimplex])

section

variable {dim : ℕ}
  {s : nerve (NonemptyFiniteChains X) _⦋dim⦌}
  (hs : ∀ (i : Fin (dim + 1)), ¬IsIndexI x₀ s i)
  (nonDeg : s ∈ (nerve (NonemptyFiniteChains X)).nonDegenerate dim)
  (notMem : s ∉ (horn x₀).obj _)

namespace ofNotIsIndexIOfEqEmpty

omit [Fintype X] [Nontrivial X]

variable (x₀ s) in
def obj (i : Fin (dim + 2)) : NonemptyFiniteChains X :=
  Fin.cases { finset := {x₀} } s.obj i

@[simp] lemma obj_zero_finset : (obj x₀ s 0).finset = {x₀} := rfl

@[simp] lemma obj_one : (obj x₀ s 1) = s.obj 0 := rfl

@[simp] lemma obj_last : obj x₀ s (Fin.last _) = s.obj (Fin.last _) := rfl

include nonDeg hs in
lemma strictMono_obj (h₀ : finsetNotMem x₀ s = ∅) : StrictMono (obj x₀ s) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, obj_one, lt_iff, obj_zero_finset,
      ssubset_iff_subset_ne, Finset.singleton_subset_iff]
    exact ⟨by simp [← notMem_finsetNotMem_iff, h₀],
      Ne.symm (by simpa only [isIndexI_zero] using hs 0)⟩
  · simp only [obj, Fin.castSucc_succ, Fin.cases_succ, lt_iff]
    rw [mem_nerve_nonDegenerate_iff_strictMono] at nonDeg
    exact nonDeg Fin.castSucc_lt_succ

end ofNotIsIndexIOfEqEmpty

open ofNotIsIndexIOfEqEmpty in
@[simps, implicit_reducible]
def ofNotIsIndexIOfEqEmpty (h₀ : finsetNotMem x₀ s = ∅) : ι x₀ where
  dim := dim
  simplex := (strictMono_obj hs nonDeg h₀).monotone.functor
  notMem₁ := by
    simpa only [nerve_obj, notMem_horn_iff, Monotone.functor_obj, obj_last] using notMem
  nonDegenerate₁ := by
    rw [mem_nerve_nonDegenerate_iff_strictMono]
    exact strictMono_obj hs nonDeg h₀
  index := 0
  isIndexI := by simp

@[simp]
lemma ofNotIsIndexIOfEqEmpty_simplex₂ (h₀ : finsetNotMem x₀ s = ∅) :
    (ofNotIsIndexIOfEqEmpty hs nonDeg notMem h₀).simplex₂ = s := rfl

namespace ofNotIsIndexI

omit [Fintype X] [Nontrivial X]

variable {i₀ : Fin (dim + 1)} (hi₀ : finsetNotMem x₀ s = Finset.Iic i₀)

variable (x₀ s i₀) in
def obj (i : Fin (dim + 2)) : NonemptyFiniteChains X :=
  if i ≠ i₀.succ then s.obj (i₀.predAbove i)
  else { finset := (s.obj i₀).finset ∪ {x₀} }

lemma obj_eq_apply_predAbove (i : Fin (dim + 2)) (hi : i ≠ i₀.succ) :
    obj x₀ s i₀ i = s.obj (i₀.predAbove i) := by
  grind [obj]

@[simp]
lemma obj_succAbove (i : Fin (dim + 1)) :
    obj x₀ s i₀ (i₀.succ.succAbove i) = s.obj i := by
  rw [obj_eq_apply_predAbove _ (by simp)]
  simp

@[simp]
lemma obj_castSucc :
    obj x₀ s i₀ i₀.castSucc = s.obj i₀ := by
  rw [obj_eq_apply_predAbove _ (by grind)]
  simp

@[simp]
lemma obj_succ_finset :
    (obj x₀ s i₀ i₀.succ).finset = (s.obj i₀).finset ∪ {x₀} := by
  dsimp [obj]
  rw [ite_eq_right (by simp)]

lemma le_obj_last :
    s.obj (Fin.last _) ≤ obj x₀ s i₀ (Fin.last _) := by
  by_cases hi₀ : i₀ = Fin.last _
  · simp [← Fin.succ_last, ← hi₀]
  · rw [obj_eq_apply_predAbove _ (by grind)]
    simp

include hs nonDeg hi₀ in
lemma strictMono_obj : StrictMono (obj x₀ s i₀) := by
  rw [mem_nerve_nonDegenerate_iff_strictMono s] at nonDeg
  replace hi₀ (i : Fin (dim + 1)) : x₀ ∈ (s.obj i).finset ↔ i₀ < i := by
    simp [← notMem_finsetNotMem_iff, hi₀]
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  simp only [lt_iff]
  obtain hi | rfl | hi := lt_trichotomy i i₀
  · rw [obj_eq_apply_predAbove _ (by grind),
      obj_eq_apply_predAbove _ (by grind)]
    exact nonDeg (by grind [Fin.predAbove, Fin.castPred])
  · simp only [obj_castSucc, obj_succ_finset, Finset.union_singleton]
    exact Finset.ssubset_insert (by simp [hi₀])
  · by_cases hi' : i.castSucc = i₀.succ
    · rw [hi', obj_succ_finset, obj_eq_apply_predAbove _ (by grind),
        Fin.predAbove_of_castSucc_lt _ _ (by grind), Fin.pred_succ,
        ssubset_iff_subset_ne]
      obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hi)
      obtain ⟨i₀, rfl⟩ := i₀.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hi)
      obtain rfl : i = i₀ := by simpa using hi'
      refine ⟨?_, Ne.symm (by simpa only [isIndexI_succ] using hs i.succ)⟩
      simp only [Finset.union_subset_iff, Finset.singleton_subset_iff, hi₀,
        Fin.castSucc_lt_succ_iff, le_refl, and_true]
      exact s.monotone (Fin.castSucc_le_succ i)
    · rw [obj_eq_apply_predAbove _ (by grind),
        obj_eq_apply_predAbove _ (by grind)]
      exact nonDeg (by grind [Fin.predAbove, Fin.castPred])

end ofNotIsIndexI

open ofNotIsIndexI in
@[simps, implicit_reducible]
def ofNotIsIndexI {i₀ : Fin (dim + 1)} (hi₀ : finsetNotMem x₀ s = Finset.Iic i₀) : ι x₀ where
  dim := dim
  simplex := (strictMono_obj hs nonDeg hi₀).monotone.functor
  notMem₁ := by
    rw [notMem_horn_iff] at notMem ⊢
    exact notMem.trans le_obj_last
  nonDegenerate₁ := by
    rw [mem_nerve_nonDegenerate_iff_strictMono]
    exact strictMono_obj hs nonDeg hi₀
  index := i₀.succ
  isIndexI := by simp

@[simp]
lemma ofNotIsIndexI_simplex₂ {i₀ : Fin (dim + 1)} (hi₀ : finsetNotMem x₀ s = Finset.Iic i₀) :
    (ofNotIsIndexI hs nonDeg notMem hi₀).simplex₂ = s := by
  ext i : 2
  simp [ofNotIsIndexI, simplex₂_def, nerve.δ_obj.{u}]

end

end ι

end pairingCore

variable (x₀)

variable [Fintype X] [Nontrivial X]

open pairingCore in
@[simps, implicit_reducible]
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
  surjective' x := by
    obtain ⟨dim, s, nonDeg, notMem, rfl⟩ := x.mk_surjective
    by_cases! hs : ∃ i, IsIndexI x₀ s i
    · obtain ⟨i, hi⟩ := hs
      obtain ⟨dim, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hi.dim_ne_zero notMem)
      exact ⟨{
        dim := dim
        simplex := s
        notMem₁ := notMem
        nonDegenerate₁ := nonDeg
        index := i
        isIndexI := hi }, Or.inl rfl⟩
    · obtain h₀ | ⟨i₀, hi₀⟩ := finsetNotMem_eq_empty_or x₀ s
      · exact ⟨.ofNotIsIndexIOfEqEmpty hs nonDeg notMem h₀, Or.inr rfl⟩
      · refine ⟨.ofNotIsIndexI hs nonDeg notMem hi₀, Or.inr ?_⟩
        rw [S.ext_iff]
        exact (ι.ofNotIsIndexI_simplex₂ hs nonDeg notMem hi₀).symm

def pairingCore.weakRankFunction : (pairingCore x₀).WeakRankFunction ℕ where
  rank s := (finsetNotMem x₀ s.simplex).card
  lt {s' t} hst hdim := by
    dsimp at s' t hdim
    let s : ι x₀ := s'.cast hdim
    replace hst : (pairingCore x₀).AncestralRel s t := by
      simpa only [s, s'.cast_eq_self hdim]
    suffices (finsetNotMem x₀ s.simplex).card < (finsetNotMem x₀ t.simplex).card by
      have : S.mk s'.simplex = S.mk s.simplex := by
        rw [S.ext_iff']
        exact ⟨by simpa [s], rfl⟩
      rwa [congr_finsetNotMem_card x₀ this]
    obtain ⟨hst₁, hst₂⟩ := hst
    obtain ⟨i, hi⟩ : ∃ i, (nerve (NonemptyFiniteChains X)).δ i t.simplex = s.simplex₂ := by
      rw [Subcomplex.N.lt_iff] at hst₂
      obtain ⟨f, _, hf⟩ := N.le_iff_exists_mono.1 hst₂.le
      obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
      exact ⟨i, hf⟩
    --rw [ι.simplex₂_def] at hi
    sorry

instance : (pairingCore x₀).IsRegular := by
  rw [(pairingCore x₀).isRegular_iff_nonempty_weakRankFunction]
  exact ⟨pairingCore.weakRankFunction x₀⟩

end horn

end PartialOrder.NonemptyFiniteChains
