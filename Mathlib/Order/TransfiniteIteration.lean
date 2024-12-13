/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Order.SuccPred.Limit

/-!
# Transfinite iteration of a function `I → I`

Given `φ : I → I` where `I` is a complete lattice, and `i₀ : I`,
we define the transfinite iteration of `φ` indexed by any well-ordered type `J`,
this is `transfiniteIteration φ i₀ : J → I`. It sends `⊥` to `i₀`, the successor
of a non maximal element `j` to `φ (transfiniteIteration φ i₀ j)`, and
a limit element `j` to the supremum of the elements `transfiniteIteration φ i₀ l` for `l < j`.
We show it is a monotone function if `i ≤ φ i` for all `i`. Moreover, if `i < φ i`
when `i ≠ ⊤`, we show in the lemma `top_mem_range_transfiniteIteration` that
there exists `j : J` such that `transfiniteIteration φ i₀ l = ⊤` if we assume that
`transfiniteIteration φ i₀ : J → I` is not injective (which shall hold
when we now `Cardinal.mk I < Cardinal.mk J`).

## TODO (@joelriou)
* deduce that in a Grothendieck abelian category, there is a *set* `I` of monomorphisms
such that any monomorphism is a transfinite composition of pushouts of morphisms in `I`,
and then an object `X` is injective iff `X ⟶ 0` has the right lifting
property with respect to `I`.

-/

universe w u

variable {I : Type u} [CompleteLattice I] (φ : I → I)

/-- This is an auxiliary structure towards the definition `transfiniteIteration`.
Given `φ : I → I` where `I` is a complete lattice, `i₀ : I`, and `j : J` is an element
in a well-ordered set, this structure contains a map `f : Set.Iic j → I`
which sends `k : Set.Iic j` to the `k`th-iteration of `φ` evaluated at `i₀`. -/
structure TransfiniteIteration (i₀ : I) {J : Type w}
    [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] (j : J) where
  /-- a map `Set.Iic j → I` -/
  f : Set.Iic j → I
  f_bot : f ⟨⊥, bot_le⟩ = i₀
  f_succ (k : J) (hk : k < j) : f ⟨Order.succ k, Order.succ_le_of_lt hk⟩ = φ (f ⟨k, hk.le⟩)
  f_limit (k : J) (hk : Order.IsSuccLimit k) (hkj : k ≤ j) :
      f ⟨k, hkj⟩ = iSup (fun (⟨l, hl⟩ : Set.Iio k) ↦ f ⟨l, hl.le.trans hkj⟩)

variable {i₀ : I} {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

namespace TransfiniteIteration

variable {φ}

lemma ext {j : J} {t t' : TransfiniteIteration φ i₀ j}
    (h : ∀ (k : J) (hk : k ≤ j), t.f ⟨k, hk⟩ = t'.f ⟨k, hk⟩) : t = t' := by
  cases t
  cases t'
  simp only [mk.injEq]
  ext ⟨k, hk⟩
  exact h k hk

/-- The element in `TransfiniteIteration φ i₀ j'` induced by
`t : TransfiniteIteration φ i₀ j` when `j' ≤ j`. -/
@[simps]
def ofLE {j : J} (t : TransfiniteIteration φ i₀ j) {j' : J} (hj' : j' ≤ j) :
    TransfiniteIteration φ i₀ j' where
  f := fun ⟨k, hk⟩ ↦ t.f ⟨k, hk.trans hj'⟩
  f_bot := t.f_bot
  f_succ k hk := t.f_succ k (lt_of_lt_of_le hk hj')
  f_limit k hk hkj := t.f_limit k hk (hkj.trans hj')

instance (j : J) : Subsingleton (TransfiniteIteration φ i₀ j) where
  allEq t t' := ext (fun k ↦ by
    induction k using SuccOrder.limitRecOn with
    | hm k hk =>
        obtain rfl := hk.eq_bot
        intro
        simp only [f_bot]
    | hs k hk hk' =>
        intro hk''
        have := (Order.succ_le_iff_of_not_isMax hk).mp hk''
        rw [t.f_succ k this, t'.f_succ k this, hk']
    | hl k hk hk' =>
        intro hkj
        rw [t.f_limit k hk hkj, t'.f_limit k hk hkj]
        congr
        ext ⟨l, hl⟩
        exact hk' l hl (hl.le.trans hkj))

lemma compatibility {j₁ j₂ : J} (t₁ : TransfiniteIteration φ i₀ j₁)
    (t₂ : TransfiniteIteration φ i₀ j₂) (k : J) (hk₁ : k ≤ j₁) (hk₂ : k ≤ j₂) :
      t₁.f ⟨k, hk₁⟩ = t₂.f ⟨k, hk₂⟩ := by
  by_cases hj : j₁ ≤ j₂
  · rw [congr_arg f (Subsingleton.elim t₁ (t₂.ofLE hj)), ofLE_f]
  · rw [congr_arg f (Subsingleton.elim t₂ (t₁.ofLE (le_of_not_ge hj))), ofLE_f]

variable (φ i₀ J) in
/-- The obvious element in `TransfiniteIteration φ i₀ (⊥ : J)`. -/
def ofBot : TransfiniteIteration φ i₀ (⊥ : J) where
  f _ := i₀
  f_bot := rfl
  f_succ k hk := by simp at hk
  f_limit k hk hkj := by
    obtain rfl : k = ⊥ := by simpa using hkj
    exact (Order.not_isSuccLimit_bot hk).elim

open Classical in
/-- The element in `TransfiniteIteration φ i₀ (Order.succ j)` deduced from
`t : TransfiniteIteration φ i₀ j` when `j : J` is not a maximal element. -/
noncomputable def ofSucc {j : J} (t : TransfiniteIteration φ i₀ j) (hj : ¬ IsMax j) :
    TransfiniteIteration φ i₀ (Order.succ j) where
  f := fun ⟨k, hk⟩ ↦
      if hkj : k ≤ j then t.f ⟨k, hkj⟩ else φ (t.f ⟨j, by simp⟩)
  f_bot := by
    dsimp
    rw [dif_pos bot_le, t.f_bot]
  f_succ k hk := by
    dsimp
    obtain hk' | rfl := ((Order.lt_succ_iff_of_not_isMax hj).mp hk).lt_or_eq
    · rw [dif_pos (Order.succ_le_of_lt hk'), t.f_succ _ hk', dif_pos hk'.le]
    · rw [dif_neg (by simpa using hk), dif_pos]
  f_limit k hk hkj := by
    have hk' : k ≤ j := by
      obtain hkj | rfl := hkj.lt_or_eq
      · exact (Order.lt_succ_iff_of_not_isMax hj).1 hkj
      · exact (Order.not_isSuccLimit_succ_of_not_isMax hj hk).elim
    dsimp
    rw [dif_pos hk', t.f_limit k hk]
    congr
    ext ⟨l, hl⟩
    rw [dif_pos]

/-- The element in `TransfiniteIteration φ i₀ j` that is obtained for
elements in `TransfiniteIteration φ i₀ l` for all `l < j`, when `j : J` is a limit element. -/
def ofLimit {j : J} (t : ∀ (l : J) (_ : l < j), TransfiniteIteration φ i₀ l)
    (hj : Order.IsSuccLimit j) :
    TransfiniteIteration φ i₀ j where
  f := fun ⟨k, hk⟩ ↦
      if hkj : k < j then (t k hkj).f ⟨k, by simp⟩
      else iSup (fun (⟨l, hl⟩ : Set.Iio j) ↦ (t l hl).f ⟨l, Set.right_mem_Iic⟩)
  f_bot := by
    dsimp
    rw [dif_pos (Ne.bot_lt (by rintro rfl; exact Order.not_isSuccLimit_bot hj)), f_bot]
  f_succ k hk := by
    dsimp
    have hk' : k < Order.succ k := by
      simp only [Order.lt_succ_iff_not_isMax, not_isMax_iff]
      exact ⟨_, hk⟩
    rw [dif_pos ((Order.IsSuccLimit.succ_lt_iff hj).mpr hk),
      f_succ _ k hk', dif_pos hk]
    congr 1
    apply compatibility
  f_limit k hk hkj := by
    dsimp
    obtain hkj | rfl := hkj.lt_or_eq
    · rw [dif_pos hkj, (t k hkj).f_limit _ hk]
      congr
      ext ⟨l, hl⟩
      dsimp
      rw [dif_pos (hl.trans hkj)]
      apply compatibility
    · rw [dif_neg (by simp)]
      congr
      ext ⟨l, hl⟩
      rw [dif_pos (by simpa using hl)]

instance (j : J) : Nonempty (TransfiniteIteration φ i₀ j) := by
  induction j using SuccOrder.limitRecOn with
  | hm j hj =>
      obtain rfl := hj.eq_bot
      exact ⟨ofBot φ i₀ J⟩
  | hs j hj hj' => exact ⟨ofSucc hj'.some hj⟩
  | hl j hj hj' => exact ⟨ofLimit (fun l hl ↦ (hj' l hl).some) hj⟩

end TransfiniteIteration

variable (i₀)

/-- Given `φ : I → I` where `I` is a complete lattice, `i₀ : I` and `J` a well-ordered
type, this is the map `J → I` which sends `j : J` to the `j`th iteration of `φ`,
evaluated at `i₀`. -/
noncomputable def transfiniteIteration (j : J) : I :=
  (Classical.arbitrary (TransfiniteIteration φ i₀ j)).f ⟨j, by simp⟩

@[simp]
lemma transfiniteIteration_bot :
    transfiniteIteration φ i₀ (⊥ : J) = i₀ :=
  (Classical.arbitrary (TransfiniteIteration φ i₀ (⊥ : J))).f_bot

lemma transfiniteIteration_succ (j : J) (hj : ¬ IsMax j) :
    transfiniteIteration φ i₀ (Order.succ j) =
      φ (transfiniteIteration φ i₀ j) := by
  dsimp [transfiniteIteration]
  rw [TransfiniteIteration.f_succ _ j (Order.lt_succ_of_not_isMax hj)]
  congr 1
  apply TransfiniteIteration.compatibility

lemma transfiniteIteration_limit (j : J) (hj : Order.IsSuccLimit j) :
    transfiniteIteration φ i₀ j =
      iSup (fun (⟨l, _⟩ : Set.Iio j) ↦ transfiniteIteration φ i₀ l) := by
  dsimp [transfiniteIteration]
  rw [TransfiniteIteration.f_limit _ j hj]
  congr
  ext ⟨l, hl⟩
  apply TransfiniteIteration.compatibility

lemma monotone_transfiniteIteration (hφ : ∀ (i : I), i ≤ φ i) :
    Monotone (transfiniteIteration φ i₀ (J := J)) := by
  intro k j hkj
  induction j using SuccOrder.limitRecOn with
  | hm k hk =>
      obtain rfl := hk.eq_bot
      obtain rfl : k = ⊥ := by simpa using hkj
      rfl
  | hs k' hk' hkk' =>
      obtain hkj | rfl := hkj.lt_or_eq
      · refine (hkk' ((Order.lt_succ_iff_of_not_isMax hk').mp hkj)).trans ?_
        rw [transfiniteIteration_succ _ _ _ hk']
        apply hφ
      · rfl
  | hl k' hk' _ =>
      obtain hkj | rfl := hkj.lt_or_eq
      · rw [transfiniteIteration_limit _ _ _ hk']
        exact le_iSup (fun (⟨l, hl⟩ : Set.Iio k') ↦ transfiniteIteration φ i₀ l) ⟨k, hkj⟩
      · rfl

lemma top_mem_range_transfiniteIteration
    (hφ' : ∀ (i : I) (_ : i ≠ ⊤), i < φ i) (φtop : φ ⊤ = ⊤)
    (H : ¬ Function.Injective (transfiniteIteration φ i₀ (J := J))) :
    ∃ (j : J), transfiniteIteration φ i₀ j = ⊤ := by
  have hφ (i : I) : i ≤ φ i := by
    by_cases hi : i = ⊤
    · subst hi
      rw [φtop]
    · exact (hφ' i hi).le
  obtain ⟨j₁, j₂, hj, eq⟩ : ∃ (j₁ j₂ : J) (hj : j₁ < j₂),
      transfiniteIteration φ i₀ j₁ = transfiniteIteration φ i₀ j₂ := by
    dsimp [Function.Injective] at H
    simp only [not_forall] at H
    obtain ⟨j₁, j₂, eq, hj⟩ := H
    by_cases hj' : j₁ < j₂
    · exact ⟨j₁, j₂, hj', eq⟩
    · simp only [not_lt] at hj'
      obtain hj' | rfl := hj'.lt_or_eq
      · exact ⟨j₂, j₁, hj', eq.symm⟩
      · simp at hj
  by_contra!
  suffices transfiniteIteration φ i₀ j₁ < transfiniteIteration φ i₀ j₂ by
    simp only [eq, lt_self_iff_false] at this
  have hj₁ : ¬ IsMax j₁ := by
    simp only [not_isMax_iff]
    exact ⟨_, hj⟩
  refine lt_of_lt_of_le (hφ' _ (this j₁)) ?_
  rw [← transfiniteIteration_succ φ i₀ j₁ hj₁]
  exact monotone_transfiniteIteration _ _ hφ (Order.succ_le_of_lt hj)
