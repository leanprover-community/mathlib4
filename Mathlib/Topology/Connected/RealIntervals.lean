/-
Copyright (c) 2024 Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennis Sweeney
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Intervals.OrdConnected
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Connected.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Connected Subsets of ℝ

In this file, we classify the connected subsets of ℝ.

## Main Results

  - `classify_connected_bounded_reals` : A bounded connected set of reals is one of:
    - `Ioo a b` for some `a < b`,
    - `Ioc a b` for some `a < b`,
    - `Ico a b` for some `a < b`,
    - `Icc a b` for some `a < b`,
    - A singleton `{a}`.

  - `classify_connected_bounded_reals_nonempty_interior` :
    The same as above, but omitting the singleton case.

  - `classify_connected_reals` : A connected set of reals is one of:
    - The bounded connected sets of reals above,
    - `Iio a` for some `a : ℝ`,
    - `Iic a` for some `a : ℝ`,
    - `Ioi a` for some `a : ℝ`,
    - `Ici a` for some `a : ℝ`,
    - `Set.univ : Set ℝ` (all of ℝ).

  - `encard_frontier_BoundedInterval` : Bounded intervals have exactly two endpoints.

## New Types

  - `struct BoundedInterval` : Unifies nontrivial intervals `Ioo`, `Ioc`, `Ico`, and `Icc`.
  - `inductive ConnectedRealClassification` : Unifies the various kinds of connected sets of reals.
-/

/-! ### Classifying Connected Bounded sets of Reals -/

open Set


lemma Ico_Ioo_with_endpoint {a b : ℝ} (hab : a < b) :
    Ico a b = (Ioo a b) ∪ {a} := by
  apply Subset.antisymm
  · intro x ⟨x_le_a, x_lt_b⟩
    by_cases xa : x = a
    · right; exact xa
    · left; exact ⟨Ne.lt_of_le' xa x_le_a, x_lt_b⟩
  · rintro x (x_Ioo | x_a)
    · exact ⟨LT.lt.le x_Ioo.1, x_Ioo.2⟩
    · exact ⟨Eq.ge x_a, Eq.trans_lt x_a hab⟩

lemma Ioc_Ioo_with_endpoint {a b : ℝ} (hab : a < b) :
    Ioc a b = (Ioo a b) ∪ {b} := by
  apply Subset.antisymm
  · intro x ⟨a_lt_x, x_le_b⟩
    by_cases xb : x = b
    · right; exact xb
    have : x < b := Ne.lt_of_le xb x_le_b
    left; exact ⟨a_lt_x, this⟩
  · rintro x (x_Ioo | x_b)
    · exact ⟨x_Ioo.1, LT.lt.le x_Ioo.2⟩
    · exact ⟨(by rw [x_b]; exact hab), Eq.le x_b⟩

section X_section
variable
  {X : Set ℝ}

lemma bdd_subset_Icc {infX supX : ℝ}
    (h_infX : IsGLB X infX) (h_supX : IsLUB X supX) :
    X ⊆ Icc infX supX := by
  intro x xX
  exact ⟨h_infX.1 xX, h_supX.1 xX⟩

lemma x_lt_excluded_supX {x supX : ℝ} (xX: x ∈ X)
    (h_supX: IsLUB X supX) (supX_X : supX ∉ X) : x < supX := by
  have : x ≠ supX := by
    intro x_eq_supX
    rw [← x_eq_supX] at supX_X
    contradiction
  exact Ne.lt_of_le this (h_supX.1 xX)

lemma excluded_infX_lt_x {x infX : ℝ} (xX: x ∈ X)
    (h_infX: IsGLB X infX) (infX_X : infX ∉ X) : infX < x := by
  have : infX ≠ x := by
    intro x_eq_supX
    rw [x_eq_supX] at infX_X
    contradiction
  exact Ne.lt_of_le this (h_infX.1 xX)

section conn_section
variable
  (conn : IsConnected X)

-- connected in ℝ means order-connected.
lemma conn_has_Icc
    (a : ℝ) (aX : a ∈ X) (b : ℝ) (bX : b ∈ X) : Icc a b ⊆ X := by
  have : OrdConnected X :=
    IsPreconnected.ordConnected (IsConnected.isPreconnected conn)
  exact Set.Icc_subset X aX bX

lemma connected_bddAbove_subset_contains_Ioo
    {supX x: ℝ} (h_supX : IsLUB X supX) (xX : x ∈ X) :
    Ioo x supX ⊆ X := by
  intro y ⟨x_lt_y, y_lt_supX⟩
  by_cases h: ∃ z ∈ X, y ≤ z
  · rcases h with ⟨z, zX, y_le_z⟩
    have : Icc x z ⊆ X := conn_has_Icc conn x xX z zX
    exact this ⟨LT.lt.le x_lt_y, y_le_z⟩
  · push_neg at h
    have : y ∈ upperBounds X := fun z ↦ fun zX ↦ LT.lt.le (h z zX)
    have : supX ≤ y := h_supX.2 this
    linarith

lemma connected_bddBelow_subset_contains_Ioo
    {infX : ℝ} {x : ℝ} (h_infX : IsGLB X infX) (xX : x ∈ X) :
    Ioo infX x ⊆ X := by
  intro y ⟨infX_lt_y, y_lt_x⟩
  by_cases h: ∃ z ∈ X, z ≤ y
  · rcases h with ⟨z, zX, z_le_y⟩
    have : Icc z x ⊆ X := conn_has_Icc conn z zX x xX
    exact this ⟨z_le_y, LT.lt.le y_lt_x⟩
  · push_neg at h
    have : y ∈ lowerBounds X := fun z ↦ fun zX ↦ LT.lt.le (h z zX)
    have : y ≤ infX := h_infX.2 this
    linarith

section inf_sup_section
variable
  {infX supX : ℝ}
  (h_infX : IsGLB X infX)
  (h_supX : IsLUB X supX)

lemma connected_bdd_subset_contains_Ioo :
    Ioo infX supX ⊆ X := by
  let ⟨z, zX⟩ := IsConnected.nonempty conn
  have h₁ : Ioo infX z ⊆ X := connected_bddBelow_subset_contains_Ioo conn h_infX zX
  have h₂ : Ioo z supX ⊆ X := connected_bddAbove_subset_contains_Ioo conn h_supX zX
  have h₃ : Ioo infX supX ⊆ Ioo infX z ∪ {z} ∪ Ioo z supX := by
    intro x ⟨infX_lt_x, x_lt_supX⟩
    rcases lt_trichotomy x z with (x_lt_z | x_eq_z | z_lt_z)
    · left; left
      exact ⟨infX_lt_x, x_lt_z⟩
    · left; right
      rw [mem_singleton_iff, x_eq_z]
    · right
      exact ⟨z_lt_z, x_lt_supX⟩
  have h₄ : Ioo infX z ∪ {z} ∪ Ioo z supX ⊆ X := by
    rintro x ((_ | x_eq_z) | _)
    · apply h₁; assumption
    · rw [mem_singleton_iff] at x_eq_z
      rw [x_eq_z]
      exact zX
    · apply h₂; assumption
  intro x x_Ioo
  exact h₄ (h₃ x_Ioo)

lemma characterize_Ioo
    (infX_X : infX ∉ X) (supX_X : supX ∉ X) :
    X = Ioo infX supX := by
  apply Subset.antisymm
  · intro x xX
    exact ⟨excluded_infX_lt_x xX h_infX infX_X,
           x_lt_excluded_supX xX h_supX supX_X⟩
  · exact connected_bdd_subset_contains_Ioo conn h_infX h_supX

lemma characterize_Ioc
    (inf_lt_sup : infX < supX)
    (infX_X : infX ∉ X) (supX_X : supX ∈ X) :
    X = Ioc infX supX := by
  apply Subset.antisymm
  · intro x xX
    exact ⟨excluded_infX_lt_x xX h_infX infX_X,
           h_supX.1 xX⟩
  · rw [Ioc_Ioo_with_endpoint inf_lt_sup, union_subset_iff]
    exact ⟨connected_bdd_subset_contains_Ioo conn h_infX h_supX,
           singleton_subset_iff.mpr supX_X⟩

lemma characterize_Ico
    (inf_lt_sup : infX < supX)
    (infX_X : infX ∈ X) (supX_X : supX ∉ X) :
    X = Ico infX supX := by
  apply Subset.antisymm
  · intro x xX
    exact ⟨h_infX.1 xX,
           x_lt_excluded_supX xX h_supX supX_X⟩
  · rw [Ico_Ioo_with_endpoint inf_lt_sup, union_subset_iff]
    exact ⟨connected_bdd_subset_contains_Ioo conn h_infX h_supX,
           singleton_subset_iff.mpr infX_X⟩

lemma characterize_Icc (infX_X : infX ∈ X) (supX_X : supX ∈ X) : X = Icc infX supX := by
  apply Subset.antisymm
  · exact bdd_subset_Icc h_infX h_supX
  · exact (conn_has_Icc conn) infX infX_X supX supX_X

lemma characterize_singleton (eq : infX = supX) : (X = {infX}) := by
  rw [← eq] at h_supX
  apply Subset.antisymm
  · apply subset_trans (bdd_subset_Icc h_infX h_supX)
    exact Set.Icc_subset {infX} rfl rfl
  · rw [singleton_subset_iff]
    rcases IsLUB.nonempty h_supX with ⟨x, xX⟩
    have : infX = x := LE.le.antisymm (h_infX.1 xX) (h_supX.1 xX)
    exact mem_of_eq_of_mem (id this) xX

end inf_sup_section
end conn_section
end X_section

/-- A tag for the tagged union of kinds of bounded intervals -/
inductive BoundedIntervalKind | IooKind | IocKind | IcoKind | IccKind

open BoundedIntervalKind

/-- A tagged union of the kinds of nontrivial bounded intervals: `Ioo`, `Ioc`, `Ico`, and `Icc`. -/
structure BoundedInterval :=
  /-- the left endpoint (supremum) of the interval -/
  left_endpoint : ℝ
  /-- the right endpoint (infimum) of the interval -/
  right_endpoint : ℝ
  /-- a proof that the interval is nontrivial -/
  left_lt_right : left_endpoint < right_endpoint
  /-- tag indicating which endpoints are included -/
  kind : BoundedIntervalKind

/-- Convert the data of an interval to the set of real numbers it represents -/
def BoundedInterval_as_set : BoundedInterval → Set ℝ
  | ⟨a, b, _, IooKind⟩ => Ioo a b
  | ⟨a, b, _, IocKind⟩ => Ioc a b
  | ⟨a, b, _, IcoKind⟩ => Ico a b
  | ⟨a, b, _, IccKind⟩ => Icc a b

/-- True iff X is one of Ioo a b, Ioc a b, Ico a b, or Icc a b for some a < b-/
def isBoundedInterval (X : Set ℝ) :=
  ∃ I : BoundedInterval, X = BoundedInterval_as_set I

lemma isBoundedInterval_Ioo {a b : ℝ} (lt : a < b) : isBoundedInterval (Ioo a b) := by
  use ⟨a, b, lt, IooKind⟩; rw [BoundedInterval_as_set]
lemma isBoundedInterval_Ioc {a b : ℝ} (lt : a < b) : isBoundedInterval (Ioc a b) := by
  use ⟨a, b, lt, IocKind⟩; rw [BoundedInterval_as_set]
lemma isBoundedInterval_Ico {a b : ℝ} (lt : a < b) : isBoundedInterval (Ico a b) := by
  use ⟨a, b, lt, IcoKind⟩; simp only [BoundedInterval_as_set]
lemma isBoundedInterval_Icc {a b : ℝ} (lt : a < b) : isBoundedInterval (Icc a b) := by
  use ⟨a, b, lt, IccKind⟩; simp only [BoundedInterval_as_set]

/-- The major lemma, assuming inf and sup exist. -/
lemma classify_connected_reals_with_GLB_lt_LUB
    {X : Set ℝ} (conn : IsConnected X) {infX supX : ℝ}
    (h_infX : IsGLB X infX) (h_supX : IsLUB X supX) (lt : infX < supX) :
    isBoundedInterval X := by
  by_cases infX_X : infX ∈ X
  · by_cases supX_X : supX ∈ X
    · use ⟨infX, supX, lt, IccKind⟩
      exact characterize_Icc conn h_infX h_supX infX_X supX_X
    · use ⟨infX, supX, lt, IcoKind⟩
      exact characterize_Ico conn h_infX h_supX lt infX_X supX_X
  · by_cases supX_X : supX ∈ X
    · use ⟨infX, supX, lt, IocKind⟩
      exact characterize_Ioc conn h_infX h_supX lt infX_X supX_X
    · use ⟨infX, supX, lt, IooKind⟩
      exact characterize_Ioo conn h_infX h_supX infX_X supX_X

/-- A connected subset of ℝ is either a singleton or a nontrivial bounded interval. -/
theorem classify_connected_bounded_reals
    {X : Set ℝ} (conn : IsConnected X) (above : BddAbove X) (below : BddBelow X) :
    (∃ a : ℝ, X = {a}) ∨ isBoundedInterval X := by
  have nonempty := IsConnected.nonempty conn
  have ⟨supX, h_supX⟩ := Real.exists_isLUB X nonempty above
  have ⟨infX, h_infX⟩ := Real.exists_isGLB X nonempty below
  by_cases inf_eq_sup : infX = supX
  · left; use infX
    exact characterize_singleton h_infX h_supX inf_eq_sup
  · right
    have : infX ≤ supX := isGLB_le_isLUB h_infX h_supX nonempty
    have : infX < supX := Ne.lt_of_le inf_eq_sup this
    exact classify_connected_reals_with_GLB_lt_LUB conn h_infX h_supX this

/-- A connected subset of ℝ with nonempty interior
    is either a singleton or a nontrivial bounded interval. -/
theorem classify_connected_bounded_reals_nonempty_interior
    {X : Set ℝ} (conn : IsConnected X) (above : BddAbove X) (below : BddBelow X)
    (h : (interior X) ≠ ∅) :
    isBoundedInterval X := by
  rcases classify_connected_bounded_reals conn above below with ⟨a, ha⟩ | bdd
  · rw [ha, interior_singleton] at h
    exact (h rfl).elim
  · exact bdd

/-! ### Facts about `BoundedInterval`s -/

section I_section
variable
  (I : BoundedInterval)

lemma isConnected_BoundedInterval :
    IsConnected (BoundedInterval_as_set I) := by
  rw [BoundedInterval_as_set]
  have ⟨a, b, lt, kind⟩ := I
  match kind with
  | IooKind => exact isConnected_Ioo lt
  | IocKind => exact isConnected_Ioc lt
  | IcoKind => exact isConnected_Ico lt
  | IccKind => exact isConnected_Icc (LT.lt.le lt)

lemma boundedInterval_nonempty : (BoundedInterval_as_set I).Nonempty :=
  IsConnected.nonempty (isConnected_BoundedInterval I)

lemma BoundedInterval_subset_Icc :
    BoundedInterval_as_set I ⊆ Icc I.left_endpoint I.right_endpoint := by
  have ⟨a, b, lt, kind⟩ := I
  match kind with
  | IooKind => dsimp; exact Ioo_subset_Icc_self
  | IocKind => dsimp; exact Ioc_subset_Icc_self
  | IcoKind => dsimp; exact Ico_subset_Icc_self
  | IccKind => dsimp; exact Eq.subset rfl

lemma BoundedInterval_contains_Ioo :
    Ioo I.left_endpoint I.right_endpoint ⊆ BoundedInterval_as_set I := by
  have ⟨a, b, lt, kind⟩ := I
  match kind with
  | IooKind => dsimp; exact Eq.subset rfl
  | IocKind => dsimp; exact Ioo_subset_Ioc_self
  | IcoKind => dsimp; exact Ioo_subset_Ico_self
  | IccKind => dsimp; exact Ioo_subset_Icc_self

lemma closure_BoundedInterval :
    closure (BoundedInterval_as_set I) = Icc I.left_endpoint I.right_endpoint := by
  apply Subset.antisymm
  · calc closure (BoundedInterval_as_set I)
      ⊆ closure (Icc I.left_endpoint I.right_endpoint) :=
        closure_mono (BoundedInterval_subset_Icc I)
    _ = Icc I.left_endpoint I.right_endpoint :=
      IsClosed.closure_eq isClosed_Icc
  · calc Icc I.left_endpoint I.right_endpoint
      = closure (Ioo I.left_endpoint I.right_endpoint) :=
        (closure_Ioo (ne_of_lt I.left_lt_right)).symm
    _ ⊆ closure (BoundedInterval_as_set I) :=
      closure_mono (BoundedInterval_contains_Ioo I)

lemma isBoundedBelow_BoundedInterval : BddBelow (BoundedInterval_as_set I) :=
  BddBelow.mono (BoundedInterval_subset_Icc I) bddBelow_Icc

lemma isBoundedAbove_BoundedInterval : BddAbove (BoundedInterval_as_set I) :=
  BddAbove.mono (BoundedInterval_subset_Icc I) bddAbove_Icc

theorem boundedInterval_left_endpoint_isGLB :
    IsGLB (BoundedInterval_as_set I) I.left_endpoint := by
  let icc := Icc I.left_endpoint I.right_endpoint
  let ioo := Ioo I.left_endpoint I.right_endpoint
  have h₁ : IsGLB icc I.left_endpoint := by
    rw [← csInf_Icc (le_of_lt I.left_lt_right)]
    apply Real.is_glb_sInf icc
    exact nonempty_Icc.mpr (le_of_lt I.left_lt_right)
    exact bddBelow_Icc
  have h₂ : IsGLB ioo I.left_endpoint := by
    rw [← csInf_Ioo I.left_lt_right]
    apply Real.is_glb_sInf ioo
    exact nonempty_Ioo.mpr I.left_lt_right
    exact bddBelow_Ioo
  apply IsGLB.of_subset_of_superset h₂ h₁
  exact BoundedInterval_contains_Ioo I
  exact BoundedInterval_subset_Icc I

theorem boundedInterval_right_endpoint_isLUB :
    IsLUB (BoundedInterval_as_set I) I.right_endpoint := by
  let icc := Icc I.left_endpoint I.right_endpoint
  let ioo := Ioo I.left_endpoint I.right_endpoint
  have h₁ : IsLUB icc I.right_endpoint := by
    rw [← csSup_Icc (le_of_lt I.left_lt_right)]
    apply Real.isLUB_sSup icc
    exact nonempty_Icc.mpr (le_of_lt I.left_lt_right)
    exact bddAbove_Icc
  have h₂ : IsLUB ioo I.right_endpoint := by
    rw [← csSup_Ioo I.left_lt_right]
    apply Real.isLUB_sSup ioo
    exact nonempty_Ioo.mpr I.left_lt_right
    exact bddAbove_Ioo
  apply IsLUB.of_subset_of_superset h₂ h₁
  exact BoundedInterval_contains_Ioo I
  exact BoundedInterval_subset_Icc I

@[simp]
theorem sInf_boundedInterval : sInf (BoundedInterval_as_set I) = I.left_endpoint := by
  apply IsGLB.csInf_eq
  exact boundedInterval_left_endpoint_isGLB I
  exact boundedInterval_nonempty I

@[simp]
theorem sSup_boundedInterval : sSup (BoundedInterval_as_set I) = I.right_endpoint := by
  apply IsLUB.csSup_eq
  exact boundedInterval_right_endpoint_isLUB I
  exact boundedInterval_nonempty I

@[simp]
lemma interior_BoundedInterval :
    interior (BoundedInterval_as_set I) = Ioo I.left_endpoint I.right_endpoint := by
  rw [BoundedInterval_as_set]
  have ⟨a, b, lt, kind⟩ := I
  match kind with
  | IooKind => dsimp; exact interior_Ioo
  | IocKind => dsimp; exact interior_Ioc
  | IcoKind => dsimp; exact interior_Ico
  | IccKind => dsimp; exact interior_Icc

@[simp]
theorem frontier_BoundedInterval :
    frontier (BoundedInterval_as_set I) = {I.left_endpoint, I.right_endpoint} := by
  rw [frontier, closure_BoundedInterval I, interior_BoundedInterval I]
  exact Icc_diff_Ioo_same (LT.lt.le I.left_lt_right)

theorem encard_frontier_BoundedInterval :
    (frontier (BoundedInterval_as_set I)).encard = 2 := by
  rw [frontier_BoundedInterval]
  exact encard_pair (ne_of_lt I.left_lt_right)

end I_section

/-! ### Finishing the classification: Unbounded Intervals -/

section Xconn_section
variable
  {X : Set ℝ} (conn : IsConnected X)

-- Continue to classify all connected sets in ℝ
lemma characterize_univ (below : ¬ BddBelow X) (above : ¬ BddAbove X) : X = univ := by
  rw [bddBelow_def] at below; push_neg at below
  rw [bddAbove_def] at above; push_neg at above
  ext x
  simp only [mem_univ, iff_true]
  have ⟨B, BX, Bbig⟩ := above x
  have ⟨A, AX, Asmall⟩ := below x
  have : Icc A B ⊆ X := (conn_has_Icc conn) A AX B BX
  exact this ⟨LT.lt.le Asmall, LT.lt.le Bbig⟩

lemma characterize_Ioi
    {infX : ℝ} (h_infX : IsGLB X infX) (infX_X : infX ∉ X)
    (above : ¬ BddAbove X) : X = Ioi infX := by
  rw [bddAbove_def] at above; push_neg at above
  apply Subset.antisymm
  · intro x xX
    exact excluded_infX_lt_x xX h_infX infX_X
  · intro x infX_lt_x
    rw [mem_Ioi] at infX_lt_x
    let ⟨B, BX, Bbig⟩ := above x
    have : Ioo infX B ⊆ X :=
      connected_bddBelow_subset_contains_Ioo conn h_infX BX
    exact this ⟨infX_lt_x, Bbig⟩

lemma characterize_Ici
    {infX : ℝ} (h_infX : IsGLB X infX) (infX_X : infX ∈ X)
    (above : ¬ BddAbove X) : X = Ici infX := by
  rw [bddAbove_def] at above; push_neg at above
  apply Set.Subset.antisymm
  · intro x xX
    exact h_infX.1 xX
  · intro x infX_le_x
    have ⟨B, BX, Bbig⟩ := above x
    have : Set.Icc infX B ⊆ X := (conn_has_Icc conn) infX infX_X B BX
    exact this ⟨infX_le_x, LT.lt.le Bbig⟩

lemma classify_Ixi
    (below : BddBelow X) (above : ¬ BddAbove X) :
    ∃ a : ℝ, (X = Ioi a ∨ X = Ici a) := by
  have ⟨infX, h_infX⟩ := Real.exists_isGLB X (IsConnected.nonempty conn) below
  use infX
  by_cases infX_X : infX ∈ X
  · right; exact characterize_Ici conn h_infX infX_X above
  · left; exact characterize_Ioi conn h_infX infX_X above

lemma characterize_Iio
    {supX : ℝ} (h_supX : IsLUB X supX) (supX_X : supX ∉ X)
    (below : ¬ BddBelow X) : X = Iio supX := by
  rw [bddBelow_def] at below; push_neg at below
  apply Set.Subset.antisymm
  · intro x xX
    exact x_lt_excluded_supX xX h_supX supX_X
  · intro x x_lt_supX
    rw [Set.mem_Iio] at x_lt_supX
    let ⟨A, AX, Asmall⟩ := below x
    have : Set.Ioo A supX ⊆ X :=
      connected_bddAbove_subset_contains_Ioo conn h_supX AX
    exact this ⟨Asmall, x_lt_supX⟩

lemma characterize_Iic
    {supX : ℝ} (h_supX : IsLUB X supX) (supX_X : supX ∈ X)
    (below : ¬ BddBelow X) : X = Iic supX := by
  rw [bddBelow_def] at below; push_neg at below
  apply Set.Subset.antisymm
  · intro x xX
    exact h_supX.1 xX
  · intro x x_le_supX
    let ⟨A, AX, Asmall⟩ := below x
    have : Set.Icc A supX ⊆ X := (conn_has_Icc conn) A AX supX supX_X
    exact this ⟨LT.lt.le Asmall, x_le_supX⟩

lemma classify_Iix (below : ¬ BddBelow X) (above : BddAbove X) :
    ∃ a : ℝ, (X = Iio a ∨ X = Iic a) := by
  have ⟨supX, h_supX⟩ := Real.exists_isLUB X (IsConnected.nonempty conn) above
  use supX
  by_cases supX_X : supX ∈ X
  · right; exact characterize_Iic conn h_supX supX_X below
  · left; exact characterize_Iio conn h_supX supX_X below

end Xconn_section

/-- A type representing the data of a connected sets in ℝ:
connected sets must be a nontrivial bounded interval, an unbounded interval, or a singleton. -/
inductive ConnectedRealClassification
  | of_univ : ConnectedRealClassification
  | of_Iio : ℝ → ConnectedRealClassification
  | of_Iic : ℝ → ConnectedRealClassification
  | of_Ioi : ℝ → ConnectedRealClassification
  | of_Ici : ℝ → ConnectedRealClassification
  | of_singleton : ℝ → ConnectedRealClassification
  | of_bounded_interval : BoundedInterval → ConnectedRealClassification

open ConnectedRealClassification

/-- Convert the data of one of the various kinds of connected sets in ℝ
into the set of real numbers that it represents. -/
def ConnectedRealClassification_as_set : ConnectedRealClassification → Set ℝ
  | of_univ => univ
  | of_Iio a => Iio a
  | of_Iic a => Iic a
  | of_Ioi a => Ioi a
  | of_Ici a => Ici a
  | of_singleton a => {a}
  | of_bounded_interval I => BoundedInterval_as_set I

/-- True iff X is one of the kinds of sets described in the classification of connected sets in ℝ.-/
def isConnectedRealClassification (X : Set ℝ) :=
  ∃ I : ConnectedRealClassification, X = ConnectedRealClassification_as_set I

/-- A connected subsets of ℝ is either
a nontrivial bounded interval, an unbounded interval, or a singleton. -/
theorem classify_connected_reals {X : Set ℝ} (conn : IsConnected X) :
    isConnectedRealClassification X := by
  by_cases below : BddBelow X
  · by_cases above : BddAbove X
    · rcases classify_connected_bounded_reals conn above below with sing | bdd
      · let ⟨a, ha⟩ := sing
        use of_singleton a; exact ha
      · let ⟨I, hI⟩ := bdd
        use of_bounded_interval I; exact hI
    · rcases classify_Ixi conn below above with ⟨a, hIoi | hIci⟩
      · use of_Ioi a; exact hIoi
      · use of_Ici a; exact hIci
  · by_cases above : BddAbove X
    · rcases classify_Iix conn below above with ⟨a, hIio | hIic⟩
      · use of_Iio a
        exact hIio
      · use of_Iic a
        exact hIic
    · use of_univ
      exact characterize_univ conn below above
