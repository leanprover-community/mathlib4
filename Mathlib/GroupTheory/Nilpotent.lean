/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ines Wright, Joachim Breitner
-/
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.TFAE

#align_import group_theory.nilpotent from "leanprover-community/mathlib"@"2bbc7e3884ba234309d2a43b19144105a753292e"

/-!

# Nilpotent groups

An API for nilpotent groups, that is, groups for which the upper central series
reaches `⊤`.

## Main definitions

Recall that if `H K : Subgroup G` then `⁅H, K⁆ : Subgroup G` is the subgroup of `G` generated
by the commutators `hkh⁻¹k⁻¹`. Recall also Lean's conventions that `⊤` denotes the
subgroup `G` of `G`, and `⊥` denotes the trivial subgroup `{1}`.

* `upperCentralSeries G : ℕ → Subgroup G` : the upper central series of a group `G`.
     This is an increasing sequence of normal subgroups `H n` of `G` with `H 0 = ⊥` and
     `H (n + 1) / H n` is the centre of `G / H n`.
* `lowerCentralSeries G : ℕ → Subgroup G` : the lower central series of a group `G`.
     This is a decreasing sequence of normal subgroups `H n` of `G` with `H 0 = ⊤` and
     `H (n + 1) = ⁅H n, G⁆`.
* `IsNilpotent` : A group G is nilpotent if its upper central series reaches `⊤`, or
    equivalently if its lower central series reaches `⊥`.
* `nilpotency_class` : the length of the upper central series of a nilpotent group.
* `IsAscendingCentralSeries (H : ℕ → Subgroup G) : Prop` and
* `IsDescendingCentralSeries (H : ℕ → Subgroup G) : Prop` : Note that in the literature
    a "central series" for a group is usually defined to be a *finite* sequence of normal subgroups
    `H 0`, `H 1`, ..., starting at `⊤`, finishing at `⊥`, and with each `H n / H (n + 1)`
    central in `G / H (n + 1)`. In this formalisation it is convenient to have two weaker predicates
    on an infinite sequence of subgroups `H n` of `G`: we say a sequence is a *descending central
    series* if it starts at `G` and `⁅H n, ⊤⁆ ⊆ H (n + 1)` for all `n`. Note that this series
    may not terminate at `⊥`, and the `H i` need not be normal. Similarly a sequence is an
    *ascending central series* if `H 0 = ⊥` and `⁅H (n + 1), ⊤⁆ ⊆ H n` for all `n`, again with no
    requirement that the series reaches `⊤` or that the `H i` are normal.

## Main theorems

`G` is *defined* to be nilpotent if the upper central series reaches `⊤`.
* `nilpotent_iff_finite_ascending_central_series` : `G` is nilpotent iff some ascending central
    series reaches `⊤`.
* `nilpotent_iff_finite_descending_central_series` : `G` is nilpotent iff some descending central
    series reaches `⊥`.
* `nilpotent_iff_lower` : `G` is nilpotent iff the lower central series reaches `⊥`.
* The `nilpotency_class` can likewise be obtained from these equivalent
  definitions, see `least_ascending_central_series_length_eq_nilpotencyClass`,
  `least_descending_central_series_length_eq_nilpotencyClass` and
  `lowerCentralSeries_length_eq_nilpotencyClass`.
* If `G` is nilpotent, then so are its subgroups, images, quotients and preimages.
  Binary and finite products of nilpotent groups are nilpotent.
  Infinite products are nilpotent if their nilpotent class is bounded.
  Corresponding lemmas about the `nilpotency_class` are provided.
* The `nilpotency_class` of `G ⧸ center G` is given explicitly, and an induction principle
  is derived from that.
* `IsNilpotent.to_isSolvable`: If `G` is nilpotent, it is solvable.


## Warning

A "central series" is usually defined to be a finite sequence of normal subgroups going
from `⊥` to `⊤` with the property that each subquotient is contained within the centre of
the associated quotient of `G`. This means that if `G` is not nilpotent, then
none of what we have called `upperCentralSeries G`, `lowerCentralSeries G` or
the sequences satisfying `IsAscendingCentralSeries` or `IsDescendingCentralSeries`
are actually central series. Note that the fact that the upper and lower central series
are not central series if `G` is not nilpotent is a standard abuse of notation.

-/


open Subgroup

section WithGroup

variable {G : Type*} [Group G] (H : Subgroup G) [Normal H]

/-- If `H` is a normal subgroup of `G`, then the set `{x : G | ∀ y : G, x*y*x⁻¹*y⁻¹ ∈ H}`
is a subgroup of `G` (because it is the preimage in `G` of the centre of the
quotient group `G/H`.)
-/
def upperCentralSeriesStep : Subgroup G where
  carrier := { x : G | ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ H }
  one_mem' y := by simp [Subgroup.one_mem]
  mul_mem' {a b ha hb y} := by
    convert Subgroup.mul_mem _ (ha (b * y * b⁻¹)) (hb y) using 1
    group
  inv_mem' {x hx y} := by
    specialize hx y⁻¹
    rw [mul_assoc, inv_inv] at hx ⊢
    exact Subgroup.Normal.mem_comm inferInstance hx
#align upper_central_series_step upperCentralSeriesStep

theorem mem_upperCentralSeriesStep (x : G) :
    x ∈ upperCentralSeriesStep H ↔ ∀ y, x * y * x⁻¹ * y⁻¹ ∈ H := Iff.rfl
#align mem_upper_central_series_step mem_upperCentralSeriesStep

open QuotientGroup

/-- The proof that `upperCentralSeriesStep H` is the preimage of the centre of `G/H` under
the canonical surjection. -/
theorem upperCentralSeriesStep_eq_comap_center :
    upperCentralSeriesStep H = Subgroup.comap (mk' H) (center (G ⧸ H)) := by
  ext
  rw [mem_comap, mem_center_iff, forall_mk]
  apply forall_congr'
  intro y
  rw [coe_mk', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, eq_comm, eq_iff_div_mem,
    div_eq_mul_inv, mul_inv_rev, mul_assoc]
#align upper_central_series_step_eq_comap_center upperCentralSeriesStep_eq_comap_center

instance : Normal (upperCentralSeriesStep H) := by
  rw [upperCentralSeriesStep_eq_comap_center]
  infer_instance

variable (G)

/-- An auxiliary type-theoretic definition defining both the upper central series of
a group, and a proof that it is normal, all in one go. -/
def upperCentralSeriesAux : ℕ → Σ'H : Subgroup G, Normal H
  | 0 => ⟨⊥, inferInstance⟩
  | n + 1 =>
    let un := upperCentralSeriesAux n
    let _un_normal := un.2
    ⟨upperCentralSeriesStep un.1, inferInstance⟩
#align upper_central_series_aux upperCentralSeriesAux

/-- `upperCentralSeries G n` is the `n`th term in the upper central series of `G`. -/
def upperCentralSeries (n : ℕ) : Subgroup G :=
  (upperCentralSeriesAux G n).1
#align upper_central_series upperCentralSeries

instance upperCentralSeries_normal (n : ℕ) : Normal (upperCentralSeries G n) :=
  (upperCentralSeriesAux G n).2

@[simp]
theorem upperCentralSeries_zero : upperCentralSeries G 0 = ⊥ := rfl
#align upper_central_series_zero upperCentralSeries_zero

@[simp]
theorem upperCentralSeries_one : upperCentralSeries G 1 = center G := by
  ext
  simp only [upperCentralSeries, upperCentralSeriesAux, upperCentralSeriesStep,
    Subgroup.mem_center_iff, mem_mk, mem_bot, Set.mem_setOf_eq]
  exact forall_congr' fun y => by rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, eq_comm]
#align upper_central_series_one upperCentralSeries_one

/-- The `n+1`st term of the upper central series `H i` has underlying set equal to the `x` such
that `⁅x,G⁆ ⊆ H n`-/
theorem mem_upperCentralSeries_succ_iff (n : ℕ) (x : G) :
    x ∈ upperCentralSeries G (n + 1) ↔ ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ upperCentralSeries G n :=
  Iff.rfl
#align mem_upper_central_series_succ_iff mem_upperCentralSeries_succ_iff


-- is_nilpotent is already defined in the root namespace (for elements of rings).
/-- A group `G` is nilpotent if its upper central series is eventually `G`. -/
class Group.IsNilpotent (G : Type*) [Group G] : Prop where
  nilpotent' : ∃ n : ℕ, upperCentralSeries G n = ⊤
#align group.is_nilpotent Group.IsNilpotent

-- Porting note: add lemma since infer kinds are unsupported in the definition of `IsNilpotent`
lemma Group.IsNilpotent.nilpotent (G : Type*) [Group G] [IsNilpotent G] :
    ∃ n : ℕ, upperCentralSeries G n = ⊤ := Group.IsNilpotent.nilpotent'

open Group

variable {G}

/-- A sequence of subgroups of `G` is an ascending central series if `H 0` is trivial and
  `⁅H (n + 1), G⁆ ⊆ H n` for all `n`. Note that we do not require that `H n = G` for some `n`. -/
def IsAscendingCentralSeries (H : ℕ → Subgroup G) : Prop :=
  H 0 = ⊥ ∧ ∀ (x : G) (n : ℕ), x ∈ H (n + 1) → ∀ g, x * g * x⁻¹ * g⁻¹ ∈ H n
#align is_ascending_central_series IsAscendingCentralSeries

/-- A sequence of subgroups of `G` is a descending central series if `H 0` is `G` and
  `⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. Note that we do not require that `H n = {1}` for some `n`. -/
def IsDescendingCentralSeries (H : ℕ → Subgroup G) :=
  H 0 = ⊤ ∧ ∀ (x : G) (n : ℕ), x ∈ H n → ∀ g, x * g * x⁻¹ * g⁻¹ ∈ H (n + 1)
#align is_descending_central_series IsDescendingCentralSeries

/-- Any ascending central series for a group is bounded above by the upper central series. -/
theorem ascending_central_series_le_upper (H : ℕ → Subgroup G) (hH : IsAscendingCentralSeries H) :
    ∀ n : ℕ, H n ≤ upperCentralSeries G n
  | 0 => hH.1.symm ▸ le_refl ⊥
  | n + 1 => by
    intro x hx
    rw [mem_upperCentralSeries_succ_iff]
    exact fun y => ascending_central_series_le_upper H hH n (hH.2 x n hx y)
#align ascending_central_series_le_upper ascending_central_series_le_upper

variable (G)

/-- The upper central series of a group is an ascending central series. -/
theorem upperCentralSeries_isAscendingCentralSeries :
    IsAscendingCentralSeries (upperCentralSeries G) :=
  ⟨rfl, fun _x _n h => h⟩
#align upper_central_series_is_ascending_central_series upperCentralSeries_isAscendingCentralSeries

theorem upperCentralSeries_mono : Monotone (upperCentralSeries G) := by
  refine' monotone_nat_of_le_succ _
  intro n x hx y
  rw [mul_assoc, mul_assoc, ← mul_assoc y x⁻¹ y⁻¹]
  exact mul_mem hx (Normal.conj_mem (upperCentralSeries_normal G n) x⁻¹ (inv_mem hx) y)
#align upper_central_series_mono upperCentralSeries_mono

/-- A group `G` is nilpotent iff there exists an ascending central series which reaches `G` in
  finitely many steps. -/
theorem nilpotent_iff_finite_ascending_central_series :
    IsNilpotent G ↔ ∃ n : ℕ, ∃ H : ℕ → Subgroup G, IsAscendingCentralSeries H ∧ H n = ⊤ := by
  constructor
  · rintro ⟨n, nH⟩
    exact ⟨_, _, upperCentralSeries_isAscendingCentralSeries G, nH⟩
  · rintro ⟨n, H, hH, hn⟩
    use n
    rw [eq_top_iff, ← hn]
    exact ascending_central_series_le_upper H hH n
#align nilpotent_iff_finite_ascending_central_series nilpotent_iff_finite_ascending_central_series

theorem is_decending_rev_series_of_is_ascending {H : ℕ → Subgroup G} {n : ℕ} (hn : H n = ⊤)
    (hasc : IsAscendingCentralSeries H) : IsDescendingCentralSeries fun m : ℕ => H (n - m) := by
  cases' hasc with h0 hH
  refine ⟨hn, fun x m hx g => ?_⟩
  dsimp at hx
  by_cases hm : n ≤ m
  · rw [tsub_eq_zero_of_le hm, h0, Subgroup.mem_bot] at hx
    subst hx
    rw [show (1 : G) * g * (1⁻¹ : G) * g⁻¹ = 1 by group]
    exact Subgroup.one_mem _
  · push_neg at hm
    apply hH
    convert hx using 1
    rw [tsub_add_eq_add_tsub (Nat.succ_le_of_lt hm), Nat.succ_eq_add_one, Nat.add_sub_add_right]
#align is_decending_rev_series_of_is_ascending is_decending_rev_series_of_is_ascending

theorem is_ascending_rev_series_of_is_descending {H : ℕ → Subgroup G} {n : ℕ} (hn : H n = ⊥)
    (hdesc : IsDescendingCentralSeries H) : IsAscendingCentralSeries fun m : ℕ => H (n - m) := by
  cases' hdesc with h0 hH
  refine ⟨hn, fun x m hx g => ?_⟩
  dsimp only at hx ⊢
  by_cases hm : n ≤ m
  · have hnm : n - m = 0 := tsub_eq_zero_iff_le.mpr hm
    rw [hnm, h0]
    exact mem_top _
  · push_neg at hm
    convert hH x _ hx g using 1
    rw [tsub_add_eq_add_tsub (Nat.succ_le_of_lt hm), Nat.succ_eq_add_one, Nat.add_sub_add_right]
#align is_ascending_rev_series_of_is_descending is_ascending_rev_series_of_is_descending

/-- A group `G` is nilpotent iff there exists a descending central series which reaches the
  trivial group in a finite time. -/
theorem nilpotent_iff_finite_descending_central_series :
    IsNilpotent G ↔ ∃ n : ℕ, ∃ H : ℕ → Subgroup G, IsDescendingCentralSeries H ∧ H n = ⊥ := by
  rw [nilpotent_iff_finite_ascending_central_series]
  constructor
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, fun m => H (n - m), is_decending_rev_series_of_is_ascending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, fun m => H (n - m), is_ascending_rev_series_of_is_descending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
#align nilpotent_iff_finite_descending_central_series nilpotent_iff_finite_descending_central_series

/-- The lower central series of a group `G` is a sequence `H n` of subgroups of `G`, defined
  by `H 0` is all of `G` and for `n≥1`, `H (n + 1) = ⁅H n, G⁆` -/
def lowerCentralSeries (G : Type*) [Group G] : ℕ → Subgroup G
  | 0 => ⊤
  | n + 1 => ⁅lowerCentralSeries G n, ⊤⁆
#align lower_central_series lowerCentralSeries

variable {G}

@[simp]
theorem lowerCentralSeries_zero : lowerCentralSeries G 0 = ⊤ := rfl
#align lower_central_series_zero lowerCentralSeries_zero

@[simp]
theorem lowerCentralSeries_one : lowerCentralSeries G 1 = commutator G := rfl
#align lower_central_series_one lowerCentralSeries_one

theorem mem_lowerCentralSeries_succ_iff (n : ℕ) (q : G) :
    q ∈ lowerCentralSeries G (n + 1) ↔
    q ∈ closure { x | ∃ p ∈ lowerCentralSeries G n,
                        ∃ q ∈ (⊤ : Subgroup G), p * q * p⁻¹ * q⁻¹ = x } := Iff.rfl
#align mem_lower_central_series_succ_iff mem_lowerCentralSeries_succ_iff

theorem lowerCentralSeries_succ (n : ℕ) :
    lowerCentralSeries G (n + 1) =
      closure { x | ∃ p ∈ lowerCentralSeries G n, ∃ q ∈ (⊤ : Subgroup G), p * q * p⁻¹ * q⁻¹ = x } :=
  rfl
#align lower_central_series_succ lowerCentralSeries_succ

instance lowerCentralSeries_normal (n : ℕ) : Normal (lowerCentralSeries G n) := by
  induction' n with d hd
  · exact (⊤ : Subgroup G).normal_of_characteristic
  · exact @Subgroup.commutator_normal _ _ (lowerCentralSeries G d) ⊤ hd _

theorem lowerCentralSeries_antitone : Antitone (lowerCentralSeries G) := by
  refine' antitone_nat_of_succ_le fun n x hx => _
  simp only [mem_lowerCentralSeries_succ_iff, exists_prop, mem_top, exists_true_left,
    true_and_iff] at hx
  refine'
    closure_induction hx _ (Subgroup.one_mem _) (@Subgroup.mul_mem _ _ _) (@Subgroup.inv_mem _ _ _)
  rintro y ⟨z, hz, a, ha⟩
  rw [← ha, mul_assoc, mul_assoc, ← mul_assoc a z⁻¹ a⁻¹]
  exact mul_mem hz (Normal.conj_mem (lowerCentralSeries_normal n) z⁻¹ (inv_mem hz) a)
#align lower_central_series_antitone lowerCentralSeries_antitone

/-- The lower central series of a group is a descending central series. -/
theorem lowerCentralSeries_isDescendingCentralSeries :
    IsDescendingCentralSeries (lowerCentralSeries G) := by
  constructor
  · rfl
  intro x n hxn g
  exact commutator_mem_commutator hxn (mem_top g)
#align lower_central_series_is_descending_central_series lowerCentralSeries_isDescendingCentralSeries

/-- Any descending central series for a group is bounded below by the lower central series. -/
theorem descending_central_series_ge_lower (H : ℕ → Subgroup G) (hH : IsDescendingCentralSeries H) :
    ∀ n : ℕ, lowerCentralSeries G n ≤ H n
  | 0 => hH.1.symm ▸ le_refl ⊤
  | n + 1 => commutator_le.mpr fun x hx q _ =>
      hH.2 x n (descending_central_series_ge_lower H hH n hx) q
#align descending_central_series_ge_lower descending_central_series_ge_lower

/-- A group is nilpotent if and only if its lower central series eventually reaches
  the trivial subgroup. -/
theorem nilpotent_iff_lowerCentralSeries : IsNilpotent G ↔ ∃ n, lowerCentralSeries G n = ⊥ := by
  rw [nilpotent_iff_finite_descending_central_series]
  constructor
  · rintro ⟨n, H, ⟨h0, hs⟩, hn⟩
    use n
    rw [eq_bot_iff, ← hn]
    exact descending_central_series_ge_lower H ⟨h0, hs⟩ n
  · rintro ⟨n, hn⟩
    exact ⟨n, lowerCentralSeries G, lowerCentralSeries_isDescendingCentralSeries, hn⟩
#align nilpotent_iff_lower_central_series nilpotent_iff_lowerCentralSeries

section Classical

open scoped Classical

variable [hG : IsNilpotent G]
variable (G)

/-- The nilpotency class of a nilpotent group is the smallest natural `n` such that
the `n`'th term of the upper central series is `G`. -/
noncomputable def Group.nilpotencyClass : ℕ := Nat.find (IsNilpotent.nilpotent G)
#align group.nilpotency_class Group.nilpotencyClass

variable {G}

@[simp]
theorem upperCentralSeries_nilpotencyClass : upperCentralSeries G (Group.nilpotencyClass G) = ⊤ :=
  Nat.find_spec (IsNilpotent.nilpotent G)
#align upper_central_series_nilpotency_class upperCentralSeries_nilpotencyClass

theorem upperCentralSeries_eq_top_iff_nilpotencyClass_le {n : ℕ} :
    upperCentralSeries G n = ⊤ ↔ Group.nilpotencyClass G ≤ n := by
  constructor
  · intro h
    exact Nat.find_le h
  · intro h
    rw [eq_top_iff, ← upperCentralSeries_nilpotencyClass]
    exact upperCentralSeries_mono _ h
#align upper_central_series_eq_top_iff_nilpotency_class_le upperCentralSeries_eq_top_iff_nilpotencyClass_le

/-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which an ascending
central series reaches `G` in its `n`'th term. -/
theorem least_ascending_central_series_length_eq_nilpotencyClass :
    Nat.find ((nilpotent_iff_finite_ascending_central_series G).mp hG) =
    Group.nilpotencyClass G := by
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · intro n hn
    exact ⟨upperCentralSeries G, upperCentralSeries_isAscendingCentralSeries G, hn⟩
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    rw [← top_le_iff, ← hn]
    exact ascending_central_series_le_upper H hH n
#align least_ascending_central_series_length_eq_nilpotency_class least_ascending_central_series_length_eq_nilpotencyClass

/-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which the descending
central series reaches `⊥` in its `n`'th term. -/
theorem least_descending_central_series_length_eq_nilpotencyClass :
    Nat.find ((nilpotent_iff_finite_descending_central_series G).mp hG) =
    Group.nilpotencyClass G := by
  rw [← least_ascending_central_series_length_eq_nilpotencyClass]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    refine ⟨fun m => H (n - m), is_decending_rev_series_of_is_ascending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    refine ⟨fun m => H (n - m), is_ascending_rev_series_of_is_descending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
#align least_descending_central_series_length_eq_nilpotency_class least_descending_central_series_length_eq_nilpotencyClass

/-- The nilpotency class of a nilpotent `G` is equal to the length of the lower central series. -/
theorem lowerCentralSeries_length_eq_nilpotencyClass :
    Nat.find (nilpotent_iff_lowerCentralSeries.mp hG) = Group.nilpotencyClass (G := G) := by
  rw [← least_descending_central_series_length_eq_nilpotencyClass]
  refine' le_antisymm (Nat.find_mono _) (Nat.find_mono _)
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    rw [← le_bot_iff, ← hn]
    exact descending_central_series_ge_lower H hH n
  · rintro n h
    exact ⟨lowerCentralSeries G, ⟨lowerCentralSeries_isDescendingCentralSeries, h⟩⟩
#align lower_central_series_length_eq_nilpotency_class lowerCentralSeries_length_eq_nilpotencyClass

@[simp]
theorem lowerCentralSeries_nilpotencyClass :
    lowerCentralSeries G (Group.nilpotencyClass G) = ⊥ := by
  rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  exact Nat.find_spec (nilpotent_iff_lowerCentralSeries.mp hG)
#align lower_central_series_nilpotency_class lowerCentralSeries_nilpotencyClass

theorem lowerCentralSeries_eq_bot_iff_nilpotencyClass_le {n : ℕ} :
    lowerCentralSeries G n = ⊥ ↔ Group.nilpotencyClass G ≤ n := by
  constructor
  · intro h
    rw [← lowerCentralSeries_length_eq_nilpotencyClass]
    exact Nat.find_le h
  · intro h
    rw [eq_bot_iff, ← lowerCentralSeries_nilpotencyClass]
    exact lowerCentralSeries_antitone h
#align lower_central_series_eq_bot_iff_nilpotency_class_le lowerCentralSeries_eq_bot_iff_nilpotencyClass_le

end Classical

theorem lowerCentralSeries_map_subtype_le (H : Subgroup G) (n : ℕ) :
    (lowerCentralSeries H n).map H.subtype ≤ lowerCentralSeries G n := by
  induction' n with d hd
  · simp
  · rw [lowerCentralSeries_succ, lowerCentralSeries_succ, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro x1 ⟨x2, ⟨x3, hx3, x4, _hx4, rfl⟩, rfl⟩
    exact ⟨x3, hd (mem_map.mpr ⟨x3, hx3, rfl⟩), x4, by simp⟩
#align lower_central_series_map_subtype_le lowerCentralSeries_map_subtype_le

/-- A subgroup of a nilpotent group is nilpotent -/
instance Subgroup.isNilpotent (H : Subgroup G) [hG : IsNilpotent G] : IsNilpotent H := by
  rw [nilpotent_iff_lowerCentralSeries] at *
  rcases hG with ⟨n, hG⟩
  use n
  have := lowerCentralSeries_map_subtype_le H n
  simp only [hG, SetLike.le_def, mem_map, forall_apply_eq_imp_iff₂, exists_imp] at this
  exact eq_bot_iff.mpr fun x hx => Subtype.ext (this x ⟨hx, rfl⟩)
#align subgroup.is_nilpotent Subgroup.isNilpotent

/-- The nilpotency class of a subgroup is less or equal to the nilpotency class of the group -/
theorem Subgroup.nilpotencyClass_le (H : Subgroup G) [hG : IsNilpotent G] :
    Group.nilpotencyClass H ≤ Group.nilpotencyClass G := by
  repeat rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  --- Porting note: Lean needs to be told that predicates are decidable
  refine @Nat.find_mono _ _ (Classical.decPred _) (Classical.decPred _) ?_ _ _
  intro n hG
  have := lowerCentralSeries_map_subtype_le H n
  simp only [hG, SetLike.le_def, mem_map, forall_apply_eq_imp_iff₂, exists_imp] at this
  exact eq_bot_iff.mpr fun x hx => Subtype.ext (this x ⟨hx, rfl⟩)
#align subgroup.nilpotency_class_le Subgroup.nilpotencyClass_le

instance (priority := 100) Group.isNilpotent_of_subsingleton [Subsingleton G] : IsNilpotent G :=
  nilpotent_iff_lowerCentralSeries.2 ⟨0, Subsingleton.elim ⊤ ⊥⟩
#align is_nilpotent_of_subsingleton Group.isNilpotent_of_subsingleton

theorem upperCentralSeries.map {H : Type*} [Group H] {f : G →* H} (h : Function.Surjective f)
    (n : ℕ) : Subgroup.map f (upperCentralSeries G n) ≤ upperCentralSeries H n := by
  induction' n with d hd
  · simp
  · rintro _ ⟨x, hx : x ∈ upperCentralSeries G d.succ, rfl⟩ y'
    rcases h y' with ⟨y, rfl⟩
    simpa using hd (mem_map_of_mem f (hx y))
#align upper_central_series.map upperCentralSeries.map

theorem lowerCentralSeries.map {H : Type*} [Group H] (f : G →* H) (n : ℕ) :
    Subgroup.map f (lowerCentralSeries G n) ≤ lowerCentralSeries H n := by
  induction' n with d hd
  · simp [Nat.zero_eq]
  · rintro a ⟨x, hx : x ∈ lowerCentralSeries G d.succ, rfl⟩
    refine closure_induction hx ?_ (by simp [f.map_one, Subgroup.one_mem _])
      (fun y z hy hz => by simp [MonoidHom.map_mul, Subgroup.mul_mem _ hy hz]) (fun y hy => by
        rw [f.map_inv]; exact Subgroup.inv_mem _ hy)
    rintro a ⟨y, hy, z, ⟨-, rfl⟩⟩
    apply mem_closure.mpr
    exact fun K hK => hK ⟨f y, hd (mem_map_of_mem f hy), by simp [commutatorElement_def]⟩
#align lower_central_series.map lowerCentralSeries.map

theorem lowerCentralSeries_succ_eq_bot {n : ℕ} (h : lowerCentralSeries G n ≤ center G) :
    lowerCentralSeries G (n + 1) = ⊥ := by
  rw [lowerCentralSeries_succ, closure_eq_bot_iff, Set.subset_singleton_iff]
  rintro x ⟨y, hy1, z, ⟨⟩, rfl⟩
  rw [mul_assoc, ← mul_inv_rev, mul_inv_eq_one, eq_comm]
  exact mem_center_iff.mp (h hy1) z
#align lower_central_series_succ_eq_bot lowerCentralSeries_succ_eq_bot

/-- The preimage of a nilpotent group is nilpotent if the kernel of the homomorphism is contained
in the center -/
theorem isNilpotent_of_ker_le_center {H : Type*} [Group H] (f : G →* H) (hf1 : f.ker ≤ center G)
    (hH : IsNilpotent H) : IsNilpotent G := by
  rw [nilpotent_iff_lowerCentralSeries] at *
  rcases hH with ⟨n, hn⟩
  use n + 1
  refine' lowerCentralSeries_succ_eq_bot (le_trans ((Subgroup.map_eq_bot_iff _).mp _) hf1)
  exact eq_bot_iff.mpr (hn ▸ lowerCentralSeries.map f n)
#align is_nilpotent_of_ker_le_center isNilpotent_of_ker_le_center

theorem nilpotencyClass_le_of_ker_le_center {H : Type*} [Group H] (f : G →* H)
    (hf1 : f.ker ≤ center G) (hH : IsNilpotent H) :
    Group.nilpotencyClass (hG := isNilpotent_of_ker_le_center f hf1 hH) ≤
      Group.nilpotencyClass H + 1 := by
  haveI : IsNilpotent G := isNilpotent_of_ker_le_center f hf1 hH
  rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  -- Porting note: Lean needs to be told that predicates are decidable
  refine @Nat.find_min' _ (Classical.decPred _) _ _ ?_
  refine lowerCentralSeries_succ_eq_bot (le_trans ((Subgroup.map_eq_bot_iff _).mp ?_) hf1)
  rw [eq_bot_iff]
  apply le_trans (lowerCentralSeries.map f _)
  simp only [lowerCentralSeries_nilpotencyClass, le_bot_iff]
#align nilpotency_class_le_of_ker_le_center nilpotencyClass_le_of_ker_le_center

/-- The range of a surjective homomorphism from a nilpotent group is nilpotent -/
theorem nilpotent_of_surjective {G' : Type*} [Group G'] [h : IsNilpotent G] (f : G →* G')
    (hf : Function.Surjective f) : IsNilpotent G' := by
  rcases h with ⟨n, hn⟩
  use n
  apply eq_top_iff.mpr
  calc
    ⊤ = f.range := symm (f.range_top_of_surjective hf)
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map _
    _ = Subgroup.map f (upperCentralSeries G n) := by rw [hn]
    _ ≤ upperCentralSeries G' n := upperCentralSeries.map hf n

#align nilpotent_of_surjective nilpotent_of_surjective

/-- The nilpotency class of the range of a surjective homomorphism from a
nilpotent group is less or equal the nilpotency class of the domain -/
theorem nilpotencyClass_le_of_surjective {G' : Type*} [Group G'] (f : G →* G')
    (hf : Function.Surjective f) [h : IsNilpotent G] :
    Group.nilpotencyClass (hG := nilpotent_of_surjective _ hf) ≤ Group.nilpotencyClass G := by
  -- Porting note: Lean needs to be told that predicates are decidable
  refine @Nat.find_mono _ _ (Classical.decPred _) (Classical.decPred _) ?_ _ _
  intro n hn
  rw [eq_top_iff]
  calc
    ⊤ = f.range := symm (f.range_top_of_surjective hf)
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map _
    _ = Subgroup.map f (upperCentralSeries G n) := by rw [hn]
    _ ≤ upperCentralSeries G' n := upperCentralSeries.map hf n

#align nilpotency_class_le_of_surjective nilpotencyClass_le_of_surjective

/-- Nilpotency respects isomorphisms -/
theorem nilpotent_of_mulEquiv {G' : Type*} [Group G'] [_h : IsNilpotent G] (f : G ≃* G') :
    IsNilpotent G' :=
  nilpotent_of_surjective f.toMonoidHom (MulEquiv.surjective f)
#align nilpotent_of_mul_equiv nilpotent_of_mulEquiv

/-- A quotient of a nilpotent group is nilpotent -/
instance nilpotent_quotient_of_nilpotent (H : Subgroup G) [H.Normal] [_h : IsNilpotent G] :
    IsNilpotent (G ⧸ H) :=
  nilpotent_of_surjective (QuotientGroup.mk' H) QuotientGroup.mk_surjective
#align nilpotent_quotient_of_nilpotent nilpotent_quotient_of_nilpotent

/-- The nilpotency class of a quotient of `G` is less or equal the nilpotency class of `G` -/
theorem nilpotencyClass_quotient_le (H : Subgroup G) [H.Normal] [_h : IsNilpotent G] :
    Group.nilpotencyClass (G ⧸ H) ≤ Group.nilpotencyClass G :=
  nilpotencyClass_le_of_surjective (QuotientGroup.mk' H) QuotientGroup.mk_surjective
#align nilpotency_class_quotient_le nilpotencyClass_quotient_le

-- This technical lemma helps with rewriting the subgroup, which occurs in indices
private theorem comap_center_subst {H₁ H₂ : Subgroup G} [Normal H₁] [Normal H₂] (h : H₁ = H₂) :
    comap (mk' H₁) (center (G ⧸ H₁)) = comap (mk' H₂) (center (G ⧸ H₂)) := by subst h; rfl

theorem comap_upperCentralSeries_quotient_center (n : ℕ) :
    comap (mk' (center G)) (upperCentralSeries (G ⧸ center G) n) = upperCentralSeries G n.succ := by
  induction' n with n ih
  · simp only [Nat.zero_eq, upperCentralSeries_zero, MonoidHom.comap_bot, ker_mk',
      (upperCentralSeries_one G).symm]
  · let Hn := upperCentralSeries (G ⧸ center G) n
    calc
      comap (mk' (center G)) (upperCentralSeriesStep Hn) =
          comap (mk' (center G)) (comap (mk' Hn) (center ((G ⧸ center G) ⧸ Hn))) :=
        by rw [upperCentralSeriesStep_eq_comap_center]
      _ = comap (mk' (comap (mk' (center G)) Hn)) (center (G ⧸ comap (mk' (center G)) Hn)) :=
        QuotientGroup.comap_comap_center
      _ = comap (mk' (upperCentralSeries G n.succ)) (center (G ⧸ upperCentralSeries G n.succ)) :=
        (comap_center_subst ih)
      _ = upperCentralSeriesStep (upperCentralSeries G n.succ) :=
        symm (upperCentralSeriesStep_eq_comap_center _)

#align comap_upper_central_series_quotient_center comap_upperCentralSeries_quotient_center

theorem nilpotencyClass_zero_iff_subsingleton [IsNilpotent G] :
    Group.nilpotencyClass G = 0 ↔ Subsingleton G := by
  -- Porting note: Lean needs to be told that predicates are decidable
  rw [Group.nilpotencyClass, @Nat.find_eq_zero _ (Classical.decPred _), upperCentralSeries_zero,
    subsingleton_iff_bot_eq_top, Subgroup.subsingleton_iff]
#align nilpotency_class_zero_iff_subsingleton nilpotencyClass_zero_iff_subsingleton

/-- Quotienting the `center G` reduces the nilpotency class by 1 -/
theorem nilpotencyClass_quotient_center [hH : IsNilpotent G] :
    Group.nilpotencyClass (G ⧸ center G) = Group.nilpotencyClass G - 1 := by
  generalize hn : Group.nilpotencyClass G = n
  rcases n with (rfl | n)
  · simp [nilpotencyClass_zero_iff_subsingleton] at *
    exact Quotient.instSubsingletonQuotient (leftRel (center G))
  · suffices Group.nilpotencyClass (G ⧸ center G) = n by simpa
    apply le_antisymm
    · apply upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp
      apply comap_injective (f := (mk' (center G))) (surjective_quot_mk _)
      rw [comap_upperCentralSeries_quotient_center, comap_top, Nat.succ_eq_add_one, ← hn]
      exact upperCentralSeries_nilpotencyClass
    · apply le_of_add_le_add_right
      calc
        n + 1 = Group.nilpotencyClass G := hn.symm
        _ ≤ Group.nilpotencyClass (G ⧸ center G) + 1 :=
          nilpotencyClass_le_of_ker_le_center _ (le_of_eq (ker_mk' _)) _

#align nilpotency_class_quotient_center nilpotencyClass_quotient_center

/-- The nilpotency class of a non-trivial group is one more than its quotient by the center -/
theorem nilpotencyClass_eq_quotient_center_plus_one [hH : IsNilpotent G] [Nontrivial G] :
    Group.nilpotencyClass G = Group.nilpotencyClass (G ⧸ center G) + 1 := by
  rw [nilpotencyClass_quotient_center]
  rcases h : Group.nilpotencyClass G with ⟨⟩
  · exfalso
    rw [nilpotencyClass_zero_iff_subsingleton] at h
    apply false_of_nontrivial_of_subsingleton G
  · simp
#align nilpotency_class_eq_quotient_center_plus_one nilpotencyClass_eq_quotient_center_plus_one

/-- If the quotient by `center G` is nilpotent, then so is G. -/
theorem of_quotient_center_nilpotent (h : IsNilpotent (G ⧸ center G)) : IsNilpotent G := by
  obtain ⟨n, hn⟩ := h.nilpotent
  use n.succ
  simp [← comap_upperCentralSeries_quotient_center, hn]
#align of_quotient_center_nilpotent of_quotient_center_nilpotent

/-- A custom induction principle for nilpotent groups. The base case is a trivial group
(`subsingleton G`), and in the induction step, one can assume the hypothesis for
the group quotiented by its center. -/
@[elab_as_elim]
theorem nilpotent_center_quotient_ind {P : ∀ (G) [Group G] [IsNilpotent G], Prop}
    (G : Type*) [Group G] [IsNilpotent G]
    (hbase : ∀ (G) [Group G] [Subsingleton G], P G)
    (hstep : ∀ (G) [Group G] [IsNilpotent G], P (G ⧸ center G) → P G) : P G := by
  obtain ⟨n, h⟩ : ∃ n, Group.nilpotencyClass G = n := ⟨_, rfl⟩
  induction' n with n ih generalizing G
  · haveI := nilpotencyClass_zero_iff_subsingleton.mp h
    exact hbase _
  · have hn : Group.nilpotencyClass (G ⧸ center G) = n := by
      simp [nilpotencyClass_quotient_center, h]
    exact hstep _ (ih _ hn)
#align nilpotent_center_quotient_ind nilpotent_center_quotient_ind

theorem derived_le_lower_central (n : ℕ) : derivedSeries G n ≤ lowerCentralSeries G n := by
  induction' n with i ih
  · simp
  · apply commutator_mono ih
    simp
#align derived_le_lower_central derived_le_lower_central

/-- Abelian groups are nilpotent -/
instance (priority := 100) CommGroup.isNilpotent {G : Type*} [CommGroup G] : IsNilpotent G := by
  use 1
  rw [upperCentralSeries_one]
  apply CommGroup.center_eq_top
#align comm_group.is_nilpotent CommGroup.isNilpotent

/-- Abelian groups have nilpotency class at most one -/
theorem CommGroup.nilpotencyClass_le_one {G : Type*} [CommGroup G] :
    Group.nilpotencyClass G ≤ 1 := by
  rw [← upperCentralSeries_eq_top_iff_nilpotencyClass_le, upperCentralSeries_one]
  apply CommGroup.center_eq_top
#align comm_group.nilpotency_class_le_one CommGroup.nilpotencyClass_le_one

/-- Groups with nilpotency class at most one are abelian -/
def commGroupOfNilpotencyClass [IsNilpotent G] (h : Group.nilpotencyClass G ≤ 1) : CommGroup G :=
  Group.commGroupOfCenterEqTop <| by
    rw [← upperCentralSeries_one]
    exact upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr h
#align comm_group_of_nilpotency_class commGroupOfNilpotencyClass

section Prod

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

theorem lowerCentralSeries_prod (n : ℕ) :
    lowerCentralSeries (G₁ × G₂) n = (lowerCentralSeries G₁ n).prod (lowerCentralSeries G₂ n) := by
  induction' n with n ih
  · simp
  · calc
      lowerCentralSeries (G₁ × G₂) n.succ = ⁅lowerCentralSeries (G₁ × G₂) n, ⊤⁆ := rfl
      _ = ⁅(lowerCentralSeries G₁ n).prod (lowerCentralSeries G₂ n), ⊤⁆ := by rw [ih]
      _ = ⁅(lowerCentralSeries G₁ n).prod (lowerCentralSeries G₂ n), (⊤ : Subgroup G₁).prod ⊤⁆ :=
        by simp
      _ = ⁅lowerCentralSeries G₁ n, (⊤ : Subgroup G₁)⁆.prod ⁅lowerCentralSeries G₂ n, ⊤⁆ :=
        (commutator_prod_prod _ _ _ _)
      _ = (lowerCentralSeries G₁ n.succ).prod (lowerCentralSeries G₂ n.succ) := rfl

#align lower_central_series_prod lowerCentralSeries_prod

/-- Products of nilpotent groups are nilpotent -/
instance isNilpotent_prod [IsNilpotent G₁] [IsNilpotent G₂] : IsNilpotent (G₁ × G₂) := by
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨max (Group.nilpotencyClass G₁) (Group.nilpotencyClass G₂), ?_⟩
  rw [lowerCentralSeries_prod,
    lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (le_max_left _ _),
    lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (le_max_right _ _), bot_prod_bot]
#align is_nilpotent_prod isNilpotent_prod

/-- The nilpotency class of a product is the max of the nilpotency classes of the factors -/
theorem nilpotencyClass_prod [IsNilpotent G₁] [IsNilpotent G₂] :
    Group.nilpotencyClass (G₁ × G₂) =
    max (Group.nilpotencyClass G₁) (Group.nilpotencyClass G₂) := by
  refine' eq_of_forall_ge_iff fun k => _
  simp only [max_le_iff, ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    lowerCentralSeries_prod, prod_eq_bot_iff]
#align nilpotency_class_prod nilpotencyClass_prod

end Prod

section BoundedPi

-- First the case of infinite products with bounded nilpotency class
variable {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]

theorem lowerCentralSeries_pi_le (n : ℕ) :
    lowerCentralSeries (∀ i, Gs i) n ≤ Subgroup.pi Set.univ
      fun i => lowerCentralSeries (Gs i) n := by
  let pi := fun f : ∀ i, Subgroup (Gs i) => Subgroup.pi Set.univ f
  induction' n with n ih
  · simp [pi_top]
  · calc
      lowerCentralSeries (∀ i, Gs i) n.succ = ⁅lowerCentralSeries (∀ i, Gs i) n, ⊤⁆ := rfl
      _ ≤ ⁅pi fun i => lowerCentralSeries (Gs i) n, ⊤⁆ := commutator_mono ih (le_refl _)
      _ = ⁅pi fun i => lowerCentralSeries (Gs i) n, pi fun i => ⊤⁆ := by simp [pi, pi_top]
      _ ≤ pi fun i => ⁅lowerCentralSeries (Gs i) n, ⊤⁆ := commutator_pi_pi_le _ _
      _ = pi fun i => lowerCentralSeries (Gs i) n.succ := rfl

#align lower_central_series_pi_le lowerCentralSeries_pi_le

/-- products of nilpotent groups are nilpotent if their nilpotency class is bounded -/
theorem isNilpotent_pi_of_bounded_class [∀ i, IsNilpotent (Gs i)] (n : ℕ)
    (h : ∀ i, Group.nilpotencyClass (Gs i) ≤ n) : IsNilpotent (∀ i, Gs i) := by
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨n, ?_⟩
  rw [eq_bot_iff]
  apply le_trans (lowerCentralSeries_pi_le _)
  rw [← eq_bot_iff, pi_eq_bot_iff]
  intro i
  apply lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (h i)
#align is_nilpotent_pi_of_bounded_class isNilpotent_pi_of_bounded_class

end BoundedPi

section FinitePi

-- Now for finite products
variable {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]

theorem lowerCentralSeries_pi_of_finite [Finite η] (n : ℕ) :
    lowerCentralSeries (∀ i, Gs i) n = Subgroup.pi Set.univ
      fun i => lowerCentralSeries (Gs i) n := by
  let pi := fun f : ∀ i, Subgroup (Gs i) => Subgroup.pi Set.univ f
  induction' n with n ih
  · simp [pi_top]
  · calc
      lowerCentralSeries (∀ i, Gs i) n.succ = ⁅lowerCentralSeries (∀ i, Gs i) n, ⊤⁆ := rfl
      _ = ⁅pi fun i => lowerCentralSeries (Gs i) n, ⊤⁆ := by rw [ih]
      _ = ⁅pi fun i => lowerCentralSeries (Gs i) n, pi fun i => ⊤⁆ := by simp [pi, pi_top]
      _ = pi fun i => ⁅lowerCentralSeries (Gs i) n, ⊤⁆ := commutator_pi_pi_of_finite _ _
      _ = pi fun i => lowerCentralSeries (Gs i) n.succ := rfl

#align lower_central_series_pi_of_finite lowerCentralSeries_pi_of_finite

/-- n-ary products of nilpotent groups are nilpotent -/
instance isNilpotent_pi [Finite η] [∀ i, IsNilpotent (Gs i)] : IsNilpotent (∀ i, Gs i) := by
  cases nonempty_fintype η
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨Finset.univ.sup fun i => Group.nilpotencyClass (Gs i), ?_⟩
  rw [lowerCentralSeries_pi_of_finite, pi_eq_bot_iff]
  intro i
  rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  exact Finset.le_sup (f := fun i => Group.nilpotencyClass (Gs i)) (Finset.mem_univ i)
#align is_nilpotent_pi isNilpotent_pi

/-- The nilpotency class of an n-ary product is the sup of the nilpotency classes of the factors -/
theorem nilpotencyClass_pi [Fintype η] [∀ i, IsNilpotent (Gs i)] :
    Group.nilpotencyClass (∀ i, Gs i) = Finset.univ.sup fun i => Group.nilpotencyClass (Gs i) := by
  apply eq_of_forall_ge_iff
  intro k
  simp only [Finset.sup_le_iff, ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    lowerCentralSeries_pi_of_finite, pi_eq_bot_iff, Finset.mem_univ, true_imp_iff]
#align nilpotency_class_pi nilpotencyClass_pi

end FinitePi

/-- A nilpotent subgroup is solvable -/
instance (priority := 100) IsNilpotent.to_isSolvable [h : IsNilpotent G] : IsSolvable G := by
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.1 h
  use n
  rw [eq_bot_iff, ← hn]
  exact derived_le_lower_central n
#align is_nilpotent.to_is_solvable IsNilpotent.to_isSolvable

theorem normalizerCondition_of_isNilpotent [h : IsNilpotent G] : NormalizerCondition G := by
  -- roughly based on https://groupprops.subwiki.org/wiki/Nilpotent_implies_normalizer_condition
  rw [normalizerCondition_iff_only_full_group_self_normalizing]
  apply @nilpotent_center_quotient_ind _ G _ _ <;> clear! G
  · intro G _ _ H _
    exact @Subsingleton.elim _ Unique.instSubsingleton _ _
  · intro G _ _ ih H hH
    have hch : center G ≤ H := Subgroup.center_le_normalizer.trans (le_of_eq hH)
    have hkh : (mk' (center G)).ker ≤ H := by simpa using hch
    have hsur : Function.Surjective (mk' (center G)) := surjective_quot_mk _
    let H' := H.map (mk' (center G))
    have hH' : H'.normalizer = H' := by
      apply comap_injective hsur
      rw [comap_normalizer_eq_of_surjective _ hsur, comap_map_eq_self hkh]
      exact hH
    apply map_injective_of_ker_le (mk' (center G)) hkh le_top
    exact (ih H' hH').trans (symm (map_top_of_surjective _ hsur))
#align normalizer_condition_of_is_nilpotent normalizerCondition_of_isNilpotent

end WithGroup

section WithFiniteGroup

open Group Fintype

variable {G : Type*} [hG : Group G]

/-- A p-group is nilpotent -/
theorem IsPGroup.isNilpotent [Finite G] {p : ℕ} [hp : Fact (Nat.Prime p)] (h : IsPGroup p G) :
    IsNilpotent G := by
  cases' nonempty_fintype G
  classical
    revert hG
    apply @Fintype.induction_subsingleton_or_nontrivial _ G _
    · intro _ _ _ _
      infer_instance
    · intro G _ _ ih _ h
      have hcq : Fintype.card (G ⧸ center G) < Fintype.card G := by
        rw [card_eq_card_quotient_mul_card_subgroup (center G)]
        apply lt_mul_of_one_lt_right
        · exact Fintype.card_pos_iff.mpr One.instNonempty
        · exact (Subgroup.one_lt_card_iff_ne_bot _).mpr (ne_of_gt h.bot_lt_center)
      have hnq : IsNilpotent (G ⧸ center G) := ih _ hcq (h.to_quotient (center G))
      exact of_quotient_center_nilpotent hnq
#align is_p_group.is_nilpotent IsPGroup.isNilpotent

variable [Fintype G]

/-- If a finite group is the direct product of its Sylow groups, it is nilpotent -/
theorem isNilpotent_of_product_of_sylow_group
    (e : (∀ p : (Fintype.card G).primeFactors, ∀ P : Sylow p G, (↑P : Subgroup G)) ≃* G) :
    IsNilpotent G := by
  classical
    let ps := (Fintype.card G).primeFactors
    have : ∀ (p : ps) (P : Sylow p G), IsNilpotent (↑P : Subgroup G) := by
      intro p P
      haveI : Fact (Nat.Prime ↑p) := Fact.mk <| Nat.prime_of_mem_primeFactors p.2
      exact P.isPGroup'.isNilpotent
    exact nilpotent_of_mulEquiv e
#align is_nilpotent_of_product_of_sylow_group isNilpotent_of_product_of_sylow_group

/-- A finite group is nilpotent iff the normalizer condition holds, and iff all maximal groups are
normal and iff all Sylow groups are normal and iff the group is the direct product of its Sylow
groups. -/
theorem isNilpotent_of_finite_tFAE :
    List.TFAE
      [IsNilpotent G, NormalizerCondition G, ∀ H : Subgroup G, IsCoatom H → H.Normal,
        ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G), (↑P : Subgroup G).Normal,
        Nonempty
          ((∀ p : (card G).primeFactors, ∀ P : Sylow p G, (↑P : Subgroup G)) ≃* G)] := by
  tfae_have 1 → 2
  · exact @normalizerCondition_of_isNilpotent _ _
  tfae_have 2 → 3
  · exact fun h H => NormalizerCondition.normal_of_coatom H h
  tfae_have 3 → 4
  · intro h p _ P; exact Sylow.normal_of_all_max_subgroups_normal h _
  tfae_have 4 → 5
  · exact fun h => Nonempty.intro (Sylow.directProductOfNormal fun {p hp hP} => h p hp hP)
  tfae_have 5 → 1
  · rintro ⟨e⟩; exact isNilpotent_of_product_of_sylow_group e
  tfae_finish
#align is_nilpotent_of_finite_tfae isNilpotent_of_finite_tFAE

end WithFiniteGroup
