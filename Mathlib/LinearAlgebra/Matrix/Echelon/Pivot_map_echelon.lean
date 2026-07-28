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
# map-based formulation of the pivot, taking Echelon form as a field
-/

@[expose] public section

namespace Matrix

open Finset OrderDual

variable {m n : Type*} {R : Type*}

section Zero

variable [Zero R] {A : Matrix m n R} {l : m → WithTop n}

/-! ### Leading entries -/
/- These go into Basic.lean if adopted (same as the finset version) -/

/-- `c` is the leading position of row `i`: entries strictly left of `c` vanish and, when
`c` is a column, the entry at `c` is nonzero. `c = ⊤` states that the row is zero. -/
def IsLeadingEntry [LT n] (A : Matrix m n R) (i : m) (c : WithTop n) : Prop :=
  (∀ j : n, (j : WithTop n) < c → A i j = 0) ∧ ∀ c₀ : n, c = c₀ → A i c₀ ≠ 0

theorem isLeadingEntry_top_iff [LT n] {i : m} :
    A.IsLeadingEntry i ⊤ ↔ A i = 0 := by
  constructor
  · intro h
    exact funext fun j => h.1 j (WithTop.coe_lt_top j)
  · intro h0
    exact ⟨fun j _ => congrFun h0 j, fun c₀ hc => absurd hc (by simp)⟩

theorem isLeadingEntry_coe_iff [LT n] {i : m} {c : n} :
    A.IsLeadingEntry i c ↔ (∀ j < c, A i j = 0) ∧ A i c ≠ 0 := by
  constructor
  · intro h
    exact ⟨fun j hj => h.1 j (WithTop.coe_lt_coe.mpr hj), h.2 c rfl⟩
  · intro h
    exact ⟨fun j hj => h.1 j (WithTop.coe_lt_coe.mp hj),
      fun c₀ hc => WithTop.coe_inj.mp hc ▸ h.2⟩

/-- A row has at most one leading position. -/
theorem IsLeadingEntry.unique [LinearOrder n] {i : m} {c₁ c₂ : WithTop n}
    (h₁ : A.IsLeadingEntry i c₁) (h₂ : A.IsLeadingEntry i c₂) :
    c₁ = c₂ := by
  refine le_antisymm (not_lt.mp fun hlt => ?_) (not_lt.mp fun hlt => ?_)
  · obtain ⟨c₀, hc⟩ := WithTop.ne_top_iff_exists.mp hlt.ne_top
    exact h₂.2 c₀ hc.symm (h₁.1 c₀ (hc ▸ hlt))
  · obtain ⟨c₀, hc⟩ := WithTop.ne_top_iff_exists.mp hlt.ne_top
    exact h₁.2 c₀ hc.symm (h₂.1 c₀ (hc ▸ hlt))

/-! ### Pivot maps -/

/-- `l` is the pivot map of `A`: the matrix is in row echelon form and `l` sends each row
to its leading position. -/
structure IsPivotMap [LT m] [LT n] (A : Matrix m n R) (l : m → WithTop n) : Prop where
  rowEchelon : A.RowEchelon
  isLeadingEntry : ∀ i, A.IsLeadingEntry i (l i)

theorem IsPivotMap.eq_top_iff [LT m] [LT n] {i : m} (h : A.IsPivotMap l) :
    l i = ⊤ ↔ A i = 0 := by
  constructor
  · intro htop
    have h0 := h.isLeadingEntry i
    rw [htop, isLeadingEntry_top_iff] at h0
    exact h0
  · intro h0
    by_contra hne
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hne
    have hl := h.isLeadingEntry i
    rw [← hc, isLeadingEntry_coe_iff] at hl
    exact hl.2 (congrFun h0 c)

theorem IsPivotMap.lt_of_lt_of_ne_top [LT m] [LinearOrder n] {i₁ i₂ : m}
    (h : A.IsPivotMap l) (hlt : i₁ < i₂) (h₁ : l i₁ ≠ ⊤) : l i₁ < l i₂ := by
  obtain ⟨c₁, hc₁⟩ := WithTop.ne_top_iff_exists.mp h₁
  rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
  · rw [h₂, ← hc₁]
    exact WithTop.coe_lt_top c₁
  · obtain ⟨c₂, hc₂⟩ := WithTop.ne_top_iff_exists.mp h₂
    have hlead₁ := h.isLeadingEntry i₁
    have hlead₂ := h.isLeadingEntry i₂
    rw [← hc₁, isLeadingEntry_coe_iff] at hlead₁
    rw [← hc₂, isLeadingEntry_coe_iff] at hlead₂
    rw [← hc₁, ← hc₂, WithTop.coe_lt_coe]
    by_contra hle
    exact hlead₂.2
      (h.rowEchelon hlt fun j hj => hlead₁.1 j (lt_of_lt_of_le hj (not_lt.mp hle)))

theorem IsPivotMap.monotone [PartialOrder m] [LinearOrder n] (h : A.IsPivotMap l) :
    Monotone l := by
  intro i₁ i₂ hle
  rcases hle.lt_or_eq with hlt | rfl
  · rcases eq_or_ne (l i₁) ⊤ with h₁ | h₁
    · have h0₂ : A i₂ = 0 := funext fun j => h.rowEchelon hlt fun j' _ =>
        congrFun (h.eq_top_iff.mp h₁) j'
      rw [h₁, h.eq_top_iff.mpr h0₂]
    · exact (h.lt_of_lt_of_ne_top hlt h₁).le
  · exact le_rfl

theorem IsPivotMap.strictMonoOn [Preorder m] [LinearOrder n] (h : A.IsPivotMap l) :
    StrictMonoOn l {i | l i ≠ ⊤} :=
  fun _ ha _ _ hab => h.lt_of_lt_of_ne_top hab ha

/-- The pivot map of a matrix is unique. -/
theorem IsPivotMap.unique [LT m] [LinearOrder n] {l' : m → WithTop n}
    (h : A.IsPivotMap l) (h' : A.IsPivotMap l') : l = l' :=
  funext fun i => (h.isLeadingEntry i).unique (h'.isLeadingEntry i)

end Zero

theorem rank_mul_eq_right_of_lowerTriangular [Fintype m] [LinearOrder m] [Fintype n]
    [CommRing R] [IsDomain R] (A : Matrix m m R) (B : Matrix m n R) (σ : Equiv.Perm m)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    (A * B.submatrix σ id).rank = B.rank := by
  have hdet : A.det ≠ 0 := by
    rw [det_of_lowerTriangular A hA]
    exact prod_ne_zero_iff.mpr fun i _ => hd i
  rw [rank_mul_eq_right_of_det_ne_zero A (B.submatrix σ id) hdet]
  exact rank_submatrix B σ (Equiv.refl n)

section Rank

variable [Fintype m] [Fintype n] {A : Matrix m n R} {l : m → WithTop n}

theorem IsPivotMap.rank_le_card [LT m] [LT n] [DecidableEq n] [CommSemiring R]
    [StrongRankCondition R] (h : A.IsPivotMap l) :
    A.rank ≤ (univ.filter fun i => l i ≠ ⊤).card := by
  refine rank_le_card_of_row_eq_zero A _ fun i hi => ?_
  exact h.eq_top_iff.mp (not_not.mp fun hne => hi (mem_filter.mpr ⟨mem_univ _, hne⟩))

variable [LinearOrder m] [LinearOrder n] [CommRing R] [IsDomain R]

theorem IsPivotMap.card_le_rank (h : A.IsPivotMap l) :
    (univ.filter fun i => l i ≠ ⊤).card ≤ A.rank := by
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

theorem IsPivotMap.rank_eq (h : A.IsPivotMap l) :
    A.rank = (univ.filter fun i => l i ≠ ⊤).card :=
  le_antisymm h.rank_le_card h.card_le_rank

theorem IsPivotMap.rank_eq_of_lowerTriangular {A : Matrix m m R} {B : Matrix m n R}
    {σ : Equiv.Perm m} (hpiv : (A * B.submatrix σ id).IsPivotMap l)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    B.rank = (univ.filter fun i => l i ≠ ⊤).card := by
  rw [← rank_mul_eq_right_of_lowerTriangular A B σ hA hd, hpiv.rank_eq]

end Rank

/-! ## Decidability -/

section Decidability

variable [Zero R] {A : Matrix m n R} {l : m → WithTop n}

/-- The staircase characterisation of a pivot map, as used by the decidability instance. -/
theorem isPivotMap_iff [PartialOrder m] [LinearOrder n] :
    A.IsPivotMap l ↔
      (∀ i₁ i₂, i₁ ≤ i₂ → l i₁ ≤ l i₂) ∧
        (∀ i₁ i₂, i₁ < i₂ → l i₁ ≠ ⊤ → l i₁ < l i₂) ∧ ∀ i, A.IsLeadingEntry i (l i) := by
  constructor
  · intro h
    exact ⟨fun _ _ hle => h.monotone hle, fun _ _ hlt h₁ => h.lt_of_lt_of_ne_top hlt h₁,
      h.isLeadingEntry⟩
  · rintro ⟨hmono, hstrict, hlead⟩
    refine ⟨?_, hlead⟩
    intro i₁ i₂ hlt j₂ hz
    rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
    · have h0 := hlead i₂
      rw [h₂, isLeadingEntry_top_iff] at h0
      exact congrFun h0 j₂
    · obtain ⟨c₂, hc₂⟩ := WithTop.ne_top_iff_exists.mp h₂
      rcases eq_or_ne (l i₁) ⊤ with h₁ | h₁
      · exact absurd (top_le_iff.mp (h₁ ▸ hmono _ _ hlt.le)) h₂
      · obtain ⟨c₁, hc₁⟩ := WithTop.ne_top_iff_exists.mp h₁
        have hlead₁ := hlead i₁
        have hlead₂ := hlead i₂
        rw [← hc₁, isLeadingEntry_coe_iff] at hlead₁
        rw [← hc₂, isLeadingEntry_coe_iff] at hlead₂
        have hcc : c₁ < c₂ := by
          have hll := hstrict _ _ hlt h₁
          rw [← hc₁, ← hc₂] at hll
          exact WithTop.coe_lt_coe.mp hll
        have hle : ¬ c₁ < j₂ := fun hc => hlead₁.2 (hz _ hc)
        exact hlead₂.1 _ (lt_of_le_of_lt (not_lt.mp hle) hcc)

instance decidableIsLeadingEntry [DecidableEq R] [Fintype n] [LT n] [DecidableLT n]
    [DecidableEq n] (A : Matrix m n R) (i : m) (c : WithTop n) :
    Decidable (A.IsLeadingEntry i c) :=
  decidable_of_iff
    ((∀ j : n, (j : WithTop n) < c → A i j = 0) ∧ ∀ c₀ : n, c = c₀ → A i c₀ ≠ 0) Iff.rfl

instance decidableIsPivotMap [DecidableEq R] [Fintype m] [LinearOrder m] [Fintype n]
    [LinearOrder n] (A : Matrix m n R) (l : m → WithTop n) :
    Decidable (A.IsPivotMap l) :=
  haveI : ∀ i : m, Decidable (A.IsLeadingEntry i (l i)) := fun _ => inferInstance
  decidable_of_iff' _ isPivotMap_iff

end Decidability

end Matrix
