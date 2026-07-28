/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# map-based formulation of the pivot

A standalone parallel of `Pivot.lean` carrying the pivot data as a map `l : m → WithTop n`
sending each row to its leading column, with `⊤` for zero rows.
-/

@[expose] public section

namespace Matrix

open Finset OrderDual

variable {m n : Type*} {R : Type*}

/-! ### Leading entries -/
/- These go into Basic.lean if adopted (same as the finset version) -/

/-- `c` is the leading position of row `i`: entries strictly left of `c` vanish and, when
`c` is a column, the entry at `c` is nonzero. `c = ⊤` states that the row is zero. -/
def IsLeadingEntry [Zero R] [LT n] (A : Matrix m n R) (i : m) (c : WithTop n) : Prop :=
  (∀ j : n, (j : WithTop n) < c → A i j = 0) ∧ ∀ c₀ : n, c = c₀ → A i c₀ ≠ 0

theorem isLeadingEntry_top_iff [Zero R] [LT n] {A : Matrix m n R} {i : m} :
    A.IsLeadingEntry i ⊤ ↔ A i = 0 := by
  constructor
  · intro h
    exact funext fun j => h.1 j (WithTop.coe_lt_top j)
  · intro h0
    exact ⟨fun j _ => congrFun h0 j, fun c₀ hc => absurd hc (by simp)⟩

theorem isLeadingEntry_coe_iff [Zero R] [LT n] {A : Matrix m n R} {i : m} {c : n} :
    A.IsLeadingEntry i c ↔ (∀ j < c, A i j = 0) ∧ A i c ≠ 0 := by
  constructor
  · intro h
    exact ⟨fun j hj => h.1 j (WithTop.coe_lt_coe.mpr hj), h.2 c rfl⟩
  · intro h
    exact ⟨fun j hj => h.1 j (WithTop.coe_lt_coe.mp hj),
      fun c₀ hc => WithTop.coe_inj.mp hc ▸ h.2⟩

/-- A row has at most one leading position. -/
theorem IsLeadingEntry.unique [Zero R] [LinearOrder n] {A : Matrix m n R} {i : m}
    {c₁ c₂ : WithTop n} (h₁ : A.IsLeadingEntry i c₁) (h₂ : A.IsLeadingEntry i c₂) :
    c₁ = c₂ := by
  refine le_antisymm (not_lt.mp fun hlt => ?_) (not_lt.mp fun hlt => ?_)
  · obtain ⟨c₀, hc⟩ := WithTop.ne_top_iff_exists.mp hlt.ne_top
    exact h₂.2 c₀ hc.symm (h₁.1 c₀ (hc ▸ hlt))
  · obtain ⟨c₀, hc⟩ := WithTop.ne_top_iff_exists.mp hlt.ne_top
    exact h₁.2 c₀ hc.symm (h₂.1 c₀ (hc ▸ hlt))

/-! ### Pivot maps -/

/-- `l` is the pivot map of `A`: it sends each row to its leading position, is monotone,
and strictly increases on the nonzero rows. -/
structure IsPivotMap [Preorder m] [Preorder n] [Zero R] (A : Matrix m n R)
    (l : m → WithTop n) : Prop where
  monotone : Monotone l
  strictMonoOn : StrictMonoOn l {i | l i ≠ ⊤}
  isLeadingEntry : ∀ i, A.IsLeadingEntry i (l i)

theorem IsPivotMap.lt_of_lt_of_ne_top [Zero R] [Preorder m] [Preorder n] {A : Matrix m n R}
    {l : m → WithTop n} {i₁ i₂ : m} (h : A.IsPivotMap l) (hlt : i₁ < i₂)
    (h₁ : l i₁ ≠ ⊤) : l i₁ < l i₂ := by
  rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
  · exact h₂ ▸ WithTop.lt_top_iff_ne_top.mpr h₁
  · exact h.strictMonoOn h₁ h₂ hlt

theorem IsPivotMap.rowEchelon [Zero R] [Preorder m] [LinearOrder n] {A : Matrix m n R}
    {l : m → WithTop n} (h : A.IsPivotMap l) : A.RowEchelon := by
  intro i₁ i₂ hlt j₂ hz
  rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
  · have h0 := h.isLeadingEntry i₂
    rw [h₂, isLeadingEntry_top_iff] at h0
    exact congrFun h0 j₂
  · obtain ⟨c₂, hc₂⟩ := WithTop.ne_top_iff_exists.mp h₂
    rcases eq_or_ne (l i₁) ⊤ with h₁ | h₁
    · exact absurd (top_le_iff.mp (h₁ ▸ h.monotone hlt.le)) h₂
    · obtain ⟨c₁, hc₁⟩ := WithTop.ne_top_iff_exists.mp h₁
      have hlead₁ := h.isLeadingEntry i₁
      have hlead₂ := h.isLeadingEntry i₂
      rw [← hc₁, isLeadingEntry_coe_iff] at hlead₁
      rw [← hc₂, isLeadingEntry_coe_iff] at hlead₂
      have hcc : c₁ < c₂ := by
        have hll := h.lt_of_lt_of_ne_top hlt h₁
        rw [← hc₁, ← hc₂] at hll
        exact WithTop.coe_lt_coe.mp hll
      have hle : ¬ c₁ < j₂ := fun hc => hlead₁.2 (hz _ hc)
      exact hlead₂.1 _ (lt_of_le_of_lt (not_lt.mp hle) hcc)

/-- The pivot map of a matrix is unique. -/
theorem IsPivotMap.unique [Zero R] [Preorder m] [LinearOrder n] {A : Matrix m n R}
    {l l' : m → WithTop n} (h : A.IsPivotMap l) (h' : A.IsPivotMap l') : l = l' :=
  funext fun i => (h.isLeadingEntry i).unique (h'.isLeadingEntry i)

theorem IsPivotMap.rank_le_card [Fintype m] [Preorder m] [Fintype n] [Preorder n]
    [DecidableEq n] [CommSemiring R] [StrongRankCondition R] {A : Matrix m n R}
    {l : m → WithTop n} (h : A.IsPivotMap l) :
    A.rank ≤ (univ.filter fun i => l i ≠ ⊤).card := by
  refine rank_le_card_of_row_eq_zero A _ fun i hi => ?_
  have htop : l i = ⊤ := not_not.mp fun hne => hi (mem_filter.mpr ⟨mem_univ _, hne⟩)
  have h0 := h.isLeadingEntry i
  rw [htop, isLeadingEntry_top_iff] at h0
  exact h0

theorem IsPivotMap.card_le_rank [Fintype m] [LinearOrder m] [Fintype n] [Preorder n]
    [DecidableEq n] [CommRing R] [IsDomain R] {A : Matrix m n R} {l : m → WithTop n}
    (h : A.IsPivotMap l) : (univ.filter fun i => l i ≠ ⊤).card ≤ A.rank := by
  let g : {i // l i ≠ ⊤} → n := fun i => (l i.1).untop i.2
  have hlead : ∀ i, (∀ j < g i, A i.1 j = 0) ∧ A i.1 (g i) ≠ 0 := by
    intro i
    have hl := h.isLeadingEntry i.1
    rw [← WithTop.coe_untop (l i.1) i.2, isLeadingEntry_coe_iff] at hl
    exact hl
  have htri : (A.submatrix Subtype.val g).BlockTriangular id := by
    intro i j hij
    refine (hlead i).1 _ ?_
    rw [← WithTop.coe_lt_coe, WithTop.coe_untop, WithTop.coe_untop]
    exact h.strictMonoOn j.2 i.2 hij
  have hdet : (A.submatrix Subtype.val g).det ≠ 0 := by
    rw [det_of_upperTriangular htri]
    exact prod_ne_zero_iff.mpr fun i _ => (hlead i).2
  calc (univ.filter fun i => l i ≠ ⊤).card
      = (A.submatrix Subtype.val g).rank := by
        rw [rank_of_det_ne_zero hdet, Fintype.card_subtype]
    _ ≤ A.rank := rank_submatrix_le A Subtype.val g

theorem IsPivotMap.rank_eq [Fintype m] [LinearOrder m] [Fintype n] [Preorder n]
    [DecidableEq n] [CommRing R] [IsDomain R] {A : Matrix m n R} {l : m → WithTop n}
    (h : A.IsPivotMap l) : A.rank = (univ.filter fun i => l i ≠ ⊤).card :=
  le_antisymm h.rank_le_card h.card_le_rank

theorem rank_mul_eq_right_of_lowerTriangular [Fintype m] [LinearOrder m] [Fintype n]
    [CommRing R] [IsDomain R] (A : Matrix m m R) (B : Matrix m n R) (σ : Equiv.Perm m)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    (A * B.submatrix σ id).rank = B.rank := by
  have hdet : A.det ≠ 0 := by
    rw [det_of_lowerTriangular A hA]
    exact prod_ne_zero_iff.mpr fun i _ => hd i
  rw [rank_mul_eq_right_of_det_ne_zero A (B.submatrix σ id) hdet]
  exact rank_submatrix B σ (Equiv.refl n)

theorem IsPivotMap.rank_eq_of_lowerTriangular [Fintype m] [LinearOrder m] [Fintype n]
    [Preorder n] [DecidableEq n] [CommRing R] [IsDomain R] {A : Matrix m m R}
    {B : Matrix m n R} {σ : Equiv.Perm m} {l : m → WithTop n}
    (hpiv : (A * B.submatrix σ id).IsPivotMap l) (hA : A.BlockTriangular toDual)
    (hd : ∀ i, A i i ≠ 0) : B.rank = (univ.filter fun i => l i ≠ ⊤).card := by
  rw [← rank_mul_eq_right_of_lowerTriangular A B σ hA hd, hpiv.rank_eq]

/-! ## Decidability
  This uses the automatically synthesised version as well -- same as the list-based
  pivot def. The same consideration for a boolean version is open.
 -/

instance decidableIsLeadingEntry [Zero R] [DecidableEq R] [Fintype n] [LT n] [DecidableLT n]
    [DecidableEq n] (A : Matrix m n R) (i : m) (c : WithTop n) :
    Decidable (A.IsLeadingEntry i c) :=
  decidable_of_iff
    ((∀ j : n, (j : WithTop n) < c → A i j = 0) ∧ ∀ c₀ : n, c = c₀ → A i c₀ ≠ 0) Iff.rfl

instance decidableIsPivotMap [Zero R] [DecidableEq R] [Fintype m] [LinearOrder m] [Fintype n]
    [LinearOrder n] (A : Matrix m n R) (l : m → WithTop n) :
    Decidable (A.IsPivotMap l) :=
  haveI : ∀ i : m, Decidable (A.IsLeadingEntry i (l i)) := fun _ => inferInstance
  decidable_of_iff'
    ((∀ i₁ i₂, i₁ ≤ i₂ → l i₁ ≤ l i₂) ∧
      (∀ i₁ i₂, i₁ < i₂ → l i₁ ≠ ⊤ → l i₁ < l i₂) ∧
      ∀ i, A.IsLeadingEntry i (l i))
    ⟨fun h => ⟨fun _ _ hle => h.monotone hle,
      fun _ _ hlt h₁ => h.lt_of_lt_of_ne_top hlt h₁, h.isLeadingEntry⟩,
      fun h => ⟨fun _ _ hle => h.1 _ _ hle, fun _ ha _ _ hab => h.2.1 _ _ hab ha, h.2.2⟩⟩

end Matrix
